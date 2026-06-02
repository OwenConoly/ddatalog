(* Distributed hardware semantics, and its correctness against [DistributedDatalog].

   A hardware network is a [DistributedDatalog.DataflowNetwork] (graph + forwarding + input +
   output + a per-node Datalog program [layout]) augmented with, for each node, its trie table
   and hardware program.  Derivation reuses DistributedDatalog's [network_prop], but a node
   fires a *hardware* rule ([EncodeNode.hw_rule_impl]) instead of [Datalog.rule_impl].

   MAIN RESULT ([hw_dist_correct], PROVED): if on every node the hardware rules match the
   node's Datalog rules ([EncodeNode.hw_rule_matches], pointwise) and the network is well-formed
   ([DistributedDatalog.good_network] -- the side condition matching DistributedDatalog), then
   the hardware network derives exactly the facts the global Datalog program derives:

       hw_net_prog_impl_fact hn f  <->  DistributedDatalog.prog_impl_fact program f

   Proof: the per-rule bridge makes [hw_net_step] and DistributedDatalog's [network_step] agree
   pointwise; [pftree_weaken] lifts that to the whole derivation, so the hardware network and the
   DistributedDatalog network derive the same facts; then DistributedDatalog's already-proved
   [soundness]/[completeness] close it.

   Discharging the per-node matching (from a compiled node) is [EncodeLayoutCorrect]'s job. *)

From Datalog Require Import Datalog.
From Stdlib Require Import List Bool ZArith.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties.
From DatalogRocq Require Import HardwareProgram EncodeNode Graph DistributedDatalog.

Import ListNotations.

Section EncodeDistributed.

(* Relations/functions are numeric ids at this layer; only variables and values are abstract. *)
Context {var aggregator T : Type}.
Context `{sig : signature nat aggregator T}.
Context {context : map.map var T} {context_ok : map.ok context}.
(* The node-identifier type is a parameter (was the hardcoded [nat*nat]). *)
Context {node_id : Type}
        {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.

Notation dl_rule := (Datalog.rule rel_id var nat aggregator).
Notation dl_program := (list dl_rule).
Notation DNet := (@DistributedDatalog.DataflowNetwork rel_id var nat aggregator T node_id).
Notation nprop := (@DistributedDatalog.network_prop rel_id T node_id).
(* ground/runtime facts at this (numeric-id) layer *)
Notation dl_fact := (Datalog.fact rel_id T).

(*----A distributed hardware network----*)

(* The Datalog-level dataflow network [hw_dnet] (graph / forwarding / input / output / the
   per-node Datalog program [layout]) plus each node's trie table and hardware program. *)
Record HwNetwork := {
  hw_dnet  : DNet;
  hw_tries : node_id -> list trie;
  hw_prog  : node_id -> hardware_program;
}.

(* One derivation step, mirroring [DistributedDatalog.network_step] but with a hardware rule
   firing ([hw_rule_impl]) in place of [rule_impl]; same [network_prop]. *)
Inductive hw_net_step (hn : HwNetwork) : nprop -> list nprop -> Prop :=
| HwInput n f :
    (hw_dnet hn).(input) n f ->
    hw_net_step hn (FactOnNode n f) []
| HwRuleApp n f hr hyps :
    In hr (hw_prog hn n) ->
    Forall (fun n' => n' = n) (map fst (get_facts_on_node hyps)) ->
    hw_rule_impl (hw_tries hn n) hr f (map snd (get_facts_on_node hyps)) ->
    hw_net_step hn (FactOnNode n f) hyps
| HwForward n n' f :
    In n' ((hw_dnet hn).(forward) n (Datalog.rel_of f)) ->
    hw_net_step hn (FactOnNode n' f) [FactOnNode n f]
| HwOutputStep n f :
    (hw_dnet hn).(output) n (Datalog.rel_of f) ->
    hw_net_step hn (Output n f) [FactOnNode n f].

Definition hw_net_pftree (hn : HwNetwork) : nprop -> Prop :=
  pftree (hw_net_step hn) (fun _ => False).

Definition hw_net_prog_impl_fact (hn : HwNetwork) : dl_fact -> Prop :=
  fun f => exists n, hw_net_pftree hn (Output n f).

(*----Per-node matching: each node's hardware rules match its Datalog rules----*)

(* The per-rule bridge [hw_rule_matches] is stated against [Datalog.rule_impl env]; in the
   bare/non-meta fragment that relation is environment-independent on the [normal_fact]
   conclusions a trie-join produces, so we fix the empty environment here. *)
Definition node_rules_match (hn : HwNetwork) : Prop :=
  forall n, Forall2 (hw_rule_matches (hw_tries hn n) (fun _ _ _ => False))
                    ((hw_dnet hn).(layout) n) (hw_prog hn n).

(* A trie-join always concludes a [normal_fact] (it projects a binding through
   [join_output_fact]). *)
Lemma hw_rule_impl_concl_normal (tries : list trie) hr (f : dl_fact) hyps' :
  hw_rule_impl tries hr f hyps' -> exists R args, f = Datalog.normal_fact R args.
Proof.
  intros [_ [vals [_ [jo [_ Hjo]]]]].
  unfold join_output_fact in Hjo.
  destruct (fold_right _ _ _) as [out|]; [|discriminate].
  injection Hjo as <-. eauto.
Qed.

(* On [normal_fact] conclusions, [rule_impl env] (for any [env]) is exactly DistributedDatalog's
   environment-free [fires]. *)
Lemma rule_impl_iff_fires (env : list dl_fact -> rel_id -> list T -> Prop)
      (r : dl_rule) (f : dl_fact) (hyps : list dl_fact) :
  (exists R args, f = Datalog.normal_fact R args) ->
  (Datalog.rule_impl env r f hyps <-> DistributedDatalog.fires r f hyps).
Proof.
  intros [R [args ->]]. split.
  - intros H. inversion H; subst. exists R, args. split; [reflexivity | assumption].
  - intros [R' [args' [Heq Hnm]]]. injection Heq as <- <-.
    apply Datalog.simple_rule_impl. assumption.
Qed.

(*----Step / derivation correspondence with DistributedDatalog----*)

Lemma step_corr (hn : HwNetwork) (Hm : node_rules_match hn) (x : nprop) (l : list nprop) :
  hw_net_step hn x l <-> network_step (hw_dnet hn) x l.
Proof.
  split; intros H.
  - inversion H; subst.
    + apply Input; assumption.
    + (* HwRuleApp: find the matching datalog rule, then bridge hw_rule_impl -> fires *)
      destruct (Forall2_exists_r _ _ _ _ (Hm n) H0) as [r [Hin Hmatch]].
      eapply RuleApp; [exact Hin | assumption |].
      apply (rule_impl_iff_fires (fun _ _ _ => False) r f);
        [eapply hw_rule_impl_concl_normal; eassumption |].
      apply (Hmatch f (map snd (get_facts_on_node l))); assumption.
    + apply Forward; assumption.
    + apply OutputStep; assumption.
  - inversion H; subst.
    + apply HwInput; assumption.
    + (* RuleApp: find the matching hardware rule, then bridge fires -> hw_rule_impl *)
      destruct (Forall2_exists_l _ _ _ _ (Hm n) H0) as [hr [Hin Hmatch]].
      eapply HwRuleApp; [exact Hin | assumption |].
      apply (Hmatch f (map snd (get_facts_on_node l))).
      apply (rule_impl_iff_fires (fun _ _ _ => False) r f);
        [ match goal with Hf : DistributedDatalog.fires _ _ _ |- _ =>
            destruct Hf as [R [args [-> _]]]; eauto end | assumption ].
    + apply HwForward; assumption.
    + apply HwOutputStep; assumption.
Qed.

Lemma pftree_corr (hn : HwNetwork) (Hm : node_rules_match hn) (x : nprop) :
  pftree (hw_net_step hn) (fun _ => False) x <-> pftree (network_step (hw_dnet hn)) (fun _ => False) x.
Proof.
  split; intros H; eapply pftree_weaken; try exact H; intros y l Hy;
    apply (step_corr hn Hm); exact Hy.
Qed.

(*----Main result----*)

(* The hardware network derives exactly what the global Datalog program does from the base
   facts [Q] (the streaming EDB distributed to per-relation input nodes). *)
Theorem hw_dist_correct (hn : HwNetwork) (program : dl_program) (Q : dl_fact -> Prop) :
  node_rules_match hn ->
  good_network_streaming (hw_dnet hn) program Q ->
  forall f, hw_net_prog_impl_fact hn f <-> DistributedDatalog.prog_impl_fact program Q f.
Proof.
  intros Hm Hgood f. split.
  - intros [n Hpf]. eapply soundness.
    + destruct Hgood as [_ [_ [_ [_ [HinQ_s _]]]]]. exact HinQ_s.
    + destruct Hgood as [_ [Hgl _]]. exact Hgl.
    + exists n. cbv [network_pftree]. apply (pftree_corr hn Hm). exact Hpf.
  - intros Hprog.
    destruct (completeness (hw_dnet hn) program Q Hgood f Hprog) as [n Hpf].
    exists n. apply (pftree_corr hn Hm). cbv [network_pftree] in Hpf. exact Hpf.
Qed.

(* The distributed correctness notion, now a corollary of the theorem. *)
Definition dist_implements (hn : HwNetwork) (program : dl_program) (Q : dl_fact -> Prop) : Prop :=
  forall f, hw_net_prog_impl_fact hn f <-> DistributedDatalog.prog_impl_fact program Q f.

Corollary hw_dist_implements (hn : HwNetwork) (program : dl_program) (Q : dl_fact -> Prop) :
  node_rules_match hn -> good_network_streaming (hw_dnet hn) program Q -> dist_implements hn program Q.
Proof. exact (hw_dist_correct hn program Q). Qed.

End EncodeDistributed.
