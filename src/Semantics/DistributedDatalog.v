From Stdlib Require Import List Bool.
From Datalog Require Import Datalog.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.
From DatalogRocq Require Import Topologies.Graph.

Import ListNotations.

Section DistributedDatalog.

  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T}.
  Context {context_ok : map.ok context}.
  Context {Node Info : Type}.
  Context {node_eqb : Node -> Node -> bool}.
  Context {node_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (node_eqb x y)}.

  (* An atom in a rule is a [clause]; a rule is the [normal_rule | meta_rule | agg_rule]
     inductive; a ground/runtime fact is a [fact] ([normal_fact R args]). *)

  (* One-step firing in the non-meta fragment (normal rules AND aggregation rules):
     rule [r] produces the normal fact [f] from hypothesis facts [hyps]. This is
     environment-free ([non_meta_rule_impl] carries no [env]); supporting [meta_rule]s
     later means switching to [rule_impl env] and threading [env]. *)
  Definition fires (r : rule) (f : fact) (hyps : list fact) : Prop :=
    exists R args, f = normal_fact R args /\ non_meta_rule_impl r R args hyps.

  Definition ForwardingTable := rel -> list Node.
  Definition ForwardingFn := Node -> ForwardingTable.
  Definition InputFn := Node -> fact -> Prop.
  Definition OutputFn := Node -> rel -> Prop.
  Definition Layout := Node -> list rule.

  Record DataflowNetwork := {
    graph : Graph (Node := Node);
    forward : ForwardingFn;
    input :  InputFn;
    output : OutputFn;
    layout : Layout
  }.

Inductive network_prop :=
  | FactOnNode (n : Node) (f : fact)
  | Output (n : Node) (f : fact).

Fixpoint get_facts_on_node (nps : list (network_prop)) : list (Node * fact) :=
  match nps with
  | [] => []
  | FactOnNode n f :: t => (n, f) :: get_facts_on_node t
  | Output n f :: t => get_facts_on_node t
  end.

Inductive network_step (net : DataflowNetwork) : network_prop -> list (network_prop) -> Prop :=
  | Input n f :
      net.(input) n f ->
      network_step net (FactOnNode n f) []
  | RuleApp n f r hyps :
      In r (net.(layout) n) ->
      Forall (fun n' => n' = n) (map fst (get_facts_on_node hyps)) ->
      fires r f (map snd (get_facts_on_node hyps)) ->
      network_step net (FactOnNode n f) (hyps)
  | Forward n n' f :
      In n' (net.(forward) n (rel_of f)) ->
      network_step net (FactOnNode n' f) [FactOnNode n f]
  | OutputStep n f :
      net.(output) n (rel_of f) ->
      network_step net (Output n f) [FactOnNode n f].

Definition network_pftree (net : DataflowNetwork) : network_prop -> Prop :=
  pftree (fun fact_node hyps => network_step net fact_node hyps) (fun _ => False).

Definition network_prog_impl_fact (net : DataflowNetwork) : fact -> Prop :=
  fun f => exists n, network_pftree net (Output n f).

(* "f is derivable from [program] given the base/EDB facts [Q]" in the non-meta fragment: the
   proof-tree closure whose leaves are base facts ([Q]) and whose every internal node fires some
   program rule.  For programs without [meta_rule]s this coincides with the reference
   [prog_impl program Q]; we keep this env-free form so soundness/completeness need no
   environment bookkeeping.  ([Q := fun _ => False] recovers the pure (no-input) derivability.) *)
Definition prog_impl_fact (program : list rule) (Q : fact -> Prop) : fact -> Prop :=
  pftree (fun f hyps => Exists (fun r => fires r f hyps) program) Q.

(* A good layout has every program rule on a node somewhere AND only assigns rules from
   the program to nodes *)
Definition good_layout (layout : Layout) (nodes : Node -> Prop) (program : list rule) : Prop :=
   Forall (fun r => exists n, nodes n /\ In r (layout n)) program /\
   forall n r, (In r (layout n) -> nodes n /\ In r program).

(* n produces facts of relation [rel] -- some rule on n has [rel] among its conclusion
   relations ([concl_rels] handles normal/meta/agg uniformly). *)
Definition node_produces (layout : Layout) (n : Node) (r : rel) : Prop :=
  exists rule, In rule (layout n) /\ In r (concl_rels rule).

(* n consumes facts of relation [rel] -- some rule on n has [rel] among its hypothesis
   relations ([hyp_rels] handles normal/meta/agg uniformly). *)
Definition node_consumes (layout : Layout) (n : Node) (r : rel) : Prop :=
  exists rule, In rule (layout n) /\ In r (hyp_rels rule).

(* There exists a forwarding path for relation r from n1 to n2 *)
Definition forwards_rel (forward : ForwardingFn) (n1 n2 : Node) (r : rel) : Prop :=
  In n2 (forward n1 r).

(* n2 is reachable from n1 via forwarding for relation r in one or more steps *)
Inductive forwarding_reachable (forward : ForwardingFn) (r : rel) : Node -> Node -> Prop :=
  | fwd_step : forall n1 n2,
      In n2 (forward n1 r) ->
      forwarding_reachable forward r n1 n2
  | fwd_trans : forall n1 n2 n3,
      In n2 (forward n1 r) ->
      forwarding_reachable forward r n2 n3 ->
      forwarding_reachable forward r n1 n3.

(* A walk whose every consecutive pair forwards [r] makes its last node forwarding-reachable
   from its first (or they coincide).  This is the bridge from a laid-down forwarding path to
   the [forwarding_reachable] closure that [good_source] reasons about. *)
Lemma forwarding_chain_reachable (forward : ForwardingFn) (r : rel) :
  forall (path : list Node) (a b : Node),
  (forall i x y, nth_error path i = Some x -> nth_error path (S i) = Some y -> In y (forward x r)) ->
  nth_error path 0 = Some a ->
  nth_error path (pred (length path)) = Some b ->
  a = b \/ forwarding_reachable forward r a b.
Proof.
  induction path as [|x [|y rest] IH]; intros a b Hcons Ha Hb.
  - discriminate Ha.
  - cbn in Ha, Hb. injection Ha as <-. injection Hb as <-. left. reflexivity.
  - cbn in Ha. injection Ha as <-.
    assert (Hxy : In y (forward x r)) by (apply (Hcons 0 x y); reflexivity).
    assert (Hcons' : forall i u v, nth_error (y :: rest) i = Some u ->
                       nth_error (y :: rest) (S i) = Some v -> In v (forward u r)).
    { intros i u v Hu Hv. apply (Hcons (S i) u v); cbn; [exact Hu | exact Hv]. }
    assert (Hb' : nth_error (y :: rest) (pred (length (y :: rest))) = Some b)
      by (cbn [length pred] in Hb |- *; cbn [nth_error] in Hb; exact Hb).
    destruct (IH y b Hcons' eq_refl Hb') as [Heq | Hreach].
    + subst y. right. apply fwd_step. exact Hxy.
    + right. exact (fwd_trans forward r x y b Hxy Hreach).
Qed.

(* A *computable* validator (the "checker that takes in paths" approach): [check_fwd_walk
   forward r path] is [true] iff every consecutive node of [path] forwards [r] to the next.
   Validating a candidate path is cheap (membership checks); proving the BFS that produced it
   is complete is not -- so the top-level checker emits/validates paths instead. *)
Fixpoint check_fwd_walk (forward : ForwardingFn) (r : rel) (path : list Node) : bool :=
  match path with
  | [] => true
  | [_] => true
  | x :: ((y :: _) as rest) =>
      existsb (node_eqb y) (forward x r) && check_fwd_walk forward r rest
  end.

Lemma existsb_node_eqb_In (y : Node) (l : list Node) :
  existsb (node_eqb y) l = true -> In y l.
Proof.
  intros H. apply existsb_exists in H. destruct H as [z [Hz Heq]].
  destruct (node_eqb_spec y z) as [->|]; [exact Hz | discriminate].
Qed.

Lemma check_fwd_walk_sound (forward : ForwardingFn) (r : rel) :
  forall (path : list Node),
  check_fwd_walk forward r path = true ->
  forall i x y, nth_error path i = Some x -> nth_error path (S i) = Some y -> In y (forward x r).
Proof.
  induction path as [|x [|y rest] IH]; intros Hchk i u v Hu Hv.
  - destruct i; discriminate.
  - destruct i; cbn in Hv; [discriminate | destruct i; discriminate].
  - cbn in Hchk. apply andb_true_iff in Hchk. destruct Hchk as [Hstep Hrest].
    destruct i as [|i'].
    + cbn in Hu, Hv. injection Hu as <-. injection Hv as <-.
      apply existsb_node_eqb_In. exact Hstep.
    + apply (IH Hrest i' u v); [exact Hu | exact Hv].
Qed.

(* the validator certifies reachability: a checked walk's endpoints are reachable (or equal). *)
Lemma checked_path_reachable (forward : ForwardingFn) (r : rel) (path : list Node) (a b : Node) :
  check_fwd_walk forward r path = true ->
  nth_error path 0 = Some a ->
  nth_error path (pred (length path)) = Some b ->
  a = b \/ forwarding_reachable forward r a b.
Proof.
  intros Hchk Ha Hb.
  apply (forwarding_chain_reachable forward r path a b).
  - apply check_fwd_walk_sound. exact Hchk.
  - exact Ha.
  - exact Hb.
Qed.

(* The forwarding table is good for a relation r if for every producer,
   there is a path to every consumer *)
Definition good_forwarding_prod_cons (net : DataflowNetwork) (r : rel) : Prop :=
  forall n_prod n_cons,
    node_produces net.(layout) n_prod r ->
    node_consumes net.(layout) n_cons r ->
    n_prod = n_cons \/
    forwarding_reachable net.(forward) r n_prod n_cons.

Definition good_forwarding_output_nodes (net : DataflowNetwork) (r : rel) : Prop :=
  forall n_prod,
    node_produces (layout net) n_prod r ->
    exists n_out,
      output net n_out r /\
      (n_prod = n_out \/ forwarding_reachable (forward net) r n_prod n_out).

(* Apply it to all relations *)
Definition good_forwarding_complete (net : DataflowNetwork) : Prop :=
  forall rel, good_forwarding_prod_cons net rel /\ good_forwarding_output_nodes net rel.

(* A good forwarding function should only be able to forward things along the
   edges *)
Definition good_forwarding_sound (forward : ForwardingFn) (nodes : Node -> Prop) (edges : Node -> Node -> Prop) : Prop :=
  forall n1 n2 r, In n2 (forward n1 r) -> nodes n1 /\ nodes n2 /\ edges n1 n2.

Definition good_forwarding (forward : ForwardingFn) (net : DataflowNetwork): Prop :=
  good_forwarding_sound forward net.(graph).(nodes) net.(graph).(edge) /\
  good_forwarding_complete net.

Definition good_input (input : InputFn) (program : list rule) : Prop :=
  forall n f, input n f ->
    exists r, In r program /\ fires r f [].

Definition good_output (net : DataflowNetwork) : Prop :=
  forall (n : Node) (f : fact),
    node_produces (layout net) n (rel_of f) ->
    exists n_out, net.(graph).(nodes) n_out /\ net.(output) n_out (rel_of f).

Definition good_network (net : DataflowNetwork) (program : list rule) : Prop :=
  good_graph net.(graph) /\
  good_layout net.(layout) net.(graph).(nodes) program /\
  good_forwarding net.(forward) net /\
  good_input net.(input) program /\
  good_output net.

(*============================================================================*)
(*  Streaming model: base facts [Q] injected at per-relation input nodes      *)
(*============================================================================*)

(* A node [n] is a *good source* for relation [R] when a fact of relation [R] sitting at [n]
   reaches (by forwarding, or is already at) every consumer of [R] and some output node.  Both
   producers (by [good_forwarding]) and input nodes (by [good_input_streaming]) are good sources;
   this is the single property soundness/completeness reason about. *)
Definition good_source (net : DataflowNetwork) (n : Node) (R : rel) : Prop :=
  (forall n_cons, node_consumes net.(layout) n_cons R ->
     n = n_cons \/ forwarding_reachable net.(forward) R n n_cons) /\
  (exists n_out, net.(output) n_out R /\
     (n = n_out \/ forwarding_reachable net.(forward) R n n_out)).

(*----------------------------------------------------------------------------*)
(* [good_source] via the path checker: rather than proving forwarding complete, *)
(* the compiler emits a candidate route to each target and we VALIDATE it.      *)
(* [validate_route net R n target path] checks [path] is a forwarding walk      *)
(* [n ~> target] (or [n = target]); soundness then hands back reachability.     *)
(*----------------------------------------------------------------------------*)

Definition validate_route (forward : ForwardingFn) (R : rel) (n target : Node)
    (path : list Node) : bool :=
  node_eqb n target ||
  (check_fwd_walk forward R path
   && match nth_error path 0 with Some h => node_eqb h n | None => false end
   && match nth_error path (pred (length path)) with Some l => node_eqb l target | None => false end).

Lemma validate_route_sound (forward : ForwardingFn) (R : rel) (n target : Node) (path : list Node) :
  validate_route forward R n target path = true ->
  n = target \/ forwarding_reachable forward R n target.
Proof.
  unfold validate_route. intros H. apply orb_true_iff in H. destruct H as [Heq | H].
  - left. destruct (node_eqb_spec n target) as [E|]; [exact E | discriminate].
  - apply andb_true_iff in H. destruct H as [H Hl]. apply andb_true_iff in H. destruct H as [Hwalk Hh].
    destruct (nth_error path 0) as [h|] eqn:Eh; [|discriminate].
    destruct (node_eqb_spec h n) as [->|]; [|discriminate].
    destruct (nth_error path (pred (length path))) as [l|] eqn:El; [|discriminate].
    destruct (node_eqb_spec l target) as [->|]; [|discriminate].
    exact (checked_path_reachable forward R path n target Hwalk Eh El).
Qed.

(* [n] is validated a good source for [R]: a checked route to every (enumerated) consumer, and to
   at least one output node. *)
Definition good_sourceb (forward : ForwardingFn) (R : rel) (n : Node)
    (consumers outputs : list Node) (cpath opath : Node -> list Node) : bool :=
  forallb (fun nc => validate_route forward R n nc (cpath nc)) consumers
  && existsb (fun no => validate_route forward R n no (opath no)) outputs.

Lemma good_sourceb_sound (net : DataflowNetwork) (R : rel) (n : Node)
    (consumers outputs : list Node) (cpath opath : Node -> list Node) :
  (forall nc, node_consumes net.(layout) nc R -> In nc consumers) ->
  (forall no, In no outputs -> net.(output) no R) ->
  good_sourceb net.(forward) R n consumers outputs cpath opath = true ->
  good_source net n R.
Proof.
  intros Hcons Hout H. apply andb_true_iff in H. destruct H as [Hall Hex]. split.
  - intros nc Hnc. apply Hcons in Hnc.
    rewrite forallb_forall in Hall. exact (validate_route_sound net.(forward) R n nc (cpath nc) (Hall nc Hnc)).
  - apply existsb_exists in Hex. destruct Hex as [no [Hin Hval]].
    exists no. split; [apply Hout; exact Hin | exact (validate_route_sound net.(forward) R n no (opath no) Hval)].
Qed.

(* Streaming input: the network's input facts are *exactly* the base facts [Q], and each base
   fact is injected at an input node that is a good source for its relation (so it forwards to
   every consumer and to an output node -- the "per-relation input node + forwarding"). *)
Definition good_input_streaming (net : DataflowNetwork) (Q : fact -> Prop) : Prop :=
  (forall n f, net.(input) n f -> Q f) /\
  (forall f, Q f -> exists n, net.(input) n f /\ good_source net n (rel_of f)).

(* The streaming well-formedness side condition: graph / layout / forwarding-soundness as before,
   every producer is a good source (forwarding completeness, bundling prod->cons and prod->output),
   and the input is the streaming distribution of [Q]. *)
Definition good_network_streaming (net : DataflowNetwork) (program : list rule) (Q : fact -> Prop) : Prop :=
  good_graph net.(graph) /\
  good_layout net.(layout) net.(graph).(nodes) program /\
  good_forwarding_sound net.(forward) net.(graph).(nodes) net.(graph).(edge) /\
  (forall n_prod R, node_produces net.(layout) n_prod R -> good_source net n_prod R) /\
  good_input_streaming net Q.

Lemma Forall_get_facts_on_node :
  forall (l : list network_prop)
         (P : Node * fact -> Prop)
         (Q : network_prop -> Prop),
    (forall n f, Q (FactOnNode n f) -> P (n, f)) ->
    Forall Q l ->
    Forall P (get_facts_on_node l).
Proof.
  induction l; intros; simpl; auto.
  - destruct a; simpl in *; auto.
    + econstructor.
      * apply H. inversion H0. assumption.
      * eapply IHl; inversion H0; eauto.
    + eapply IHl; inversion H0; eauto.
Qed.

Lemma get_facts_on_node_map_FactOnNode :
  forall n l,
    get_facts_on_node (List.map (FactOnNode n) l) = List.map (pair n) l.
Proof.
  induction l; simpl; auto.
  rewrite IHl. reflexivity.
Qed.

Lemma get_facts_fst_map_FactOnNode :
  forall n l,
    map fst (get_facts_on_node (map (FactOnNode n) l)) = map (fun _ => n) l.
Proof.
  induction l; simpl; auto.
  rewrite IHl. reflexivity.
Qed.

(* [pftree] induction predicate for the network: every derivable network proposition's
   carried fact is derivable from the program given the base facts [Q]. *)
Definition np_sound (program : list rule) (Q : fact -> Prop) (np : network_prop) : Prop :=
  match np with
  | FactOnNode _ f => prog_impl_fact program Q f
  | Output _ f => prog_impl_fact program Q f
  end.

Theorem soundness'' (net : DataflowNetwork) (program : list rule) (Q : fact -> Prop) :
  (forall n f, net.(input) n f -> Q f) ->
  good_layout net.(layout) net.(graph).(nodes) program ->
  forall np, network_pftree net np -> np_sound program Q np.
Proof.
  intros HinQ [Hlc Hls]. unfold network_pftree.
  apply (pftree_ind (fun fact_node hyps => network_step net fact_node hyps)
           (fun _ => False) (np_sound program Q)).
  - intros x [].
  - intros np l Hstep _ IH. inversion Hstep; subst; simpl in *.
    + (* Input: an input fact is a base fact [Q], hence a pftree leaf *)
      match goal with Hin : net.(input) ?n ?f |- _ =>
        apply pftree_leaf; exact (HinQ n f Hin) end.
    + (* RuleApp: fire r at n, hyps already sound by IH *)
      match goal with Hl : In ?r (net.(layout) ?n) |- _ =>
        destruct (Hls n r Hl) as [Hnode Hrin] end.
      eapply pftree_step with (l := map snd (get_facts_on_node l)).
      * apply Exists_exists. exists r. split; [exact Hrin |
          match goal with Hf : fires ?r ?f _ |- _ => exact Hf end].
      * (* every hyp fact is program-derivable, from IH on the FactOnNode premises *)
        apply Forall_forall. intros f' Hf'in.
        apply in_map_iff in Hf'in. destruct Hf'in as [[n' f''] [Heq Hin]]. simpl in Heq. subst f''.
        (* the (n', f') comes from a FactOnNode n' f' premise in l *)
        rewrite Forall_forall in IH.
        assert (Hnp : In (FactOnNode n' f') l).
        { clear -Hin. induction l as [|a l IHl]; simpl in *; [contradiction|].
          destruct a; simpl in Hin.
          - destruct Hin as [Heq | Hin]; [inversion Heq; subst; left; reflexivity | right; auto].
          - right; auto. }
        specialize (IH _ Hnp). simpl in IH. exact IH.
    + (* Forward: same fact, carried over *)
      rewrite Forall_forall in IH.
      specialize (IH (FactOnNode n f)). simpl in IH. apply IH. left. reflexivity.
    + (* OutputStep: same fact, carried over *)
      rewrite Forall_forall in IH.
      specialize (IH (FactOnNode n f)). simpl in IH. apply IH. left. reflexivity.
Qed.

Theorem soundness (net : DataflowNetwork) (program : list rule) (Q : fact -> Prop) :
  forall f,
  (forall n f, net.(input) n f -> Q f) ->
  good_layout net.(layout) net.(graph).(nodes) program ->
  network_prog_impl_fact net f ->
  prog_impl_fact program Q f.
Proof.
  intros f HinQ Hgl [n Hpf].
  apply (soundness'' net program Q HinQ Hgl (Output n f) Hpf).
Qed.

Lemma In_singular : forall {A} (x y : A) (l : list A), In x (y :: l) -> x = y \/ In x l.
Proof.
  intros. inversion H; auto.
Qed.

Lemma forwarding_lifts :
  forall net n1 n2 f,
    network_pftree net (FactOnNode n1 f) ->
    forwarding_reachable net.(forward) (rel_of f) n1 n2 ->
    network_pftree net (FactOnNode n2 f).
Proof.
  intros net n1 n2 f Hpf Hreach.
  induction Hreach.
  - (* single step: n1 -> n2 directly *)
    eapply pftree_step with (l := [FactOnNode n1 f]).
    + apply Forward. exact H.
    + constructor; [exact Hpf | constructor].
  - (* transitive: n1 -> n2 -> n3 *)
    apply IHHreach.
    eapply pftree_step with (l := [FactOnNode n1 f]).
    + apply Forward. exact H.
    + constructor; [exact Hpf | constructor].
Qed.

Lemma Forall2_exists_l {A B : Type} (P : A -> B -> Prop) (l1 : list A) (l2 : list B) (a : A) :
  Forall2 P l1 l2 ->
  In a l1 ->
  exists b, In b l2 /\ P a b.
Proof.
  intros HF Hin.
  induction HF.
  - inversion Hin.
  - destruct Hin as [-> | Hin].
    + exists y. split; [left; reflexivity | assumption].
    + destruct (IHHF Hin) as [b [Hbin Hpab]].
      exists b. split; [right; assumption | assumption].
Qed.

Lemma Forall2_exists_r {A B : Type} (P : A -> B -> Prop) (l1 : list A) (l2 : list B) (b : B) :
  Forall2 P l1 l2 ->
  In b l2 ->
  exists a, In a l1 /\ P a b.
Proof.
  intros HF Hin.
  induction HF.
  - inversion Hin.
  - destruct Hin as [-> | Hin].
    + exists x. split; [left; reflexivity | assumption].
    + destruct (IHHF Hin) as [a [Hain Hpab]].
      exists a. split; [right; assumption | assumption].
Qed.

(* interp_clause exposes the relation: an interpreted clause is a normal fact whose
   relation is the clause's relation. *)
Lemma interp_clause_rel ctx (c : clause) (f : fact) :
  interp_clause ctx c f -> rel_of f = c.(clause_rel).
Proof. intros [args' [_ ->]]. reflexivity. Qed.

(* If a rule fires producing f, [rel_of f] is one of the rule's conclusion relations. *)
Lemma fires_produces_rel :
  forall (r : rule) (f : fact) (hyps : list fact),
    fires r f hyps ->
    In (rel_of f) (concl_rels r).
Proof.
  intros r f hyps [R [args [-> Hnm]]]. simpl. inversion Hnm; subst; simpl.
  - (* normal_rule_impl *)
    apply Exists_exists in H. destruct H as [c [Hcin Hc]].
    apply interp_clause_rel in Hc. simpl in Hc. subst R.
    apply in_map. exact Hcin.
  - (* agg_rule_impl: conclusion relation is concl_rel *)
    left. reflexivity.
Qed.

(* If a rule fires consuming f', [rel_of f'] is one of the rule's hypothesis relations. *)
Lemma fires_consumes_rel :
  forall (r : rule) (f : fact) (hyps : list fact) (f' : fact),
    fires r f hyps ->
    In f' hyps ->
    In (rel_of f') (hyp_rels r).
Proof.
  intros r f hyps f' [R [args [-> Hnm]]] Hin. inversion Hnm; subst; simpl in *.
  - (* normal_rule_impl: hyps interpreted from clauses *)
    destruct (Forall2_exists_r _ _ _ f' H0 Hin) as [c [Hcin Hc]].
    apply interp_clause_rel in Hc. rewrite Hc. apply in_map. exact Hcin.
  - (* agg_rule_impl: every hypothesis fact has relation hyp_rel *)
    left.
    destruct Hin as [Heq | Hin].
    + subst f'. reflexivity.
    + apply in_map_iff in Hin. destruct Hin as [[i x_i] [Heq _]]. subst f'. reflexivity.
Qed.

(* If a rule fires producing f at node n, n is a producer of [rel_of f] *)
Lemma fires_node_produces :
  forall (r : rule) (f : fact) (hyps : list fact) (n : Node) (net : DataflowNetwork),
    fires r f hyps ->
    In r (layout net n) ->
    node_produces (layout net) n (rel_of f).
Proof.
  intros r f hyps n net Hfires Hin_layout.
  exists r. split; [exact Hin_layout |]. eapply fires_produces_rel; eauto.
Qed.

(* If a rule fires consuming f' at node n, n is a consumer of [rel_of f'] *)
Lemma fires_node_consumes :
  forall (r : rule) (f : fact) (hyps : list fact) (f' : fact) (n : Node) (net : DataflowNetwork),
    fires r f hyps ->
    In f' hyps ->
    In r (layout net n) ->
    node_consumes (layout net) n (rel_of f').
Proof.
  intros r f hyps f' n net Hfires Hf'in Hin_layout.
  exists r. split; [exact Hin_layout |]. eapply fires_consumes_rel; eauto.
Qed.

(* If a fact is at a producer, it can be forwarded to any consumer *)
(* A fact at a good source for its relation can be carried to any consumer of that relation. *)
Lemma fact_at_source_consumer :
  forall (net : DataflowNetwork) (f : fact) (n n_cons : Node),
    network_pftree net (FactOnNode n f) ->
    good_source net n (rel_of f) ->
    node_consumes (layout net) n_cons (rel_of f) ->
    network_pftree net (FactOnNode n_cons f).
Proof.
  intros net f n n_cons Hpf [Hcons _] Hc.
  destruct (Hcons n_cons Hc) as [-> | Hreach].
  - exact Hpf.
  - eapply forwarding_lifts; eauto.
Qed.

(* Every derivable fact (from base facts [Q]) exists at a node that is a good source for its
   relation -- a producer for a derived fact, or the input node for a base fact. *)
Lemma completeness_with_source (net : DataflowNetwork) (program : list rule) (Q : fact -> Prop) :
  good_network_streaming net program Q ->
  forall f, prog_impl_fact program Q f ->
    exists n, network_pftree net (FactOnNode n f) /\ good_source net n (rel_of f).
Proof.
  intros Hnet.
  destruct Hnet as [Hgraph [[Hlc Hls] [Hfwds [Hprodsrc [HinQ_s HinQ_c]]]]].
  rewrite Forall_forall in Hlc.
  apply (pftree_ind
           (fun f hyps => Exists (fun r => fires r f hyps) program)
           Q
           (fun f => exists n, network_pftree net (FactOnNode n f) /\
                               good_source net n (rel_of f))).
  - (* leaf: a base fact is injected at its input node, which is a good source *)
    intros f HQ. destruct (HinQ_c f HQ) as [n [Hin Hsrc]].
    exists n. split; [|exact Hsrc].
    eapply pftree_step with (l := []); [apply Input; exact Hin | constructor].
  - (* step: a rule fires; the producing node is a good source *)
    intros f l Hexists _ IH.
    apply Exists_exists in Hexists. destruct Hexists as [r [Hr_in Hfires]].
    destruct (Hlc r Hr_in) as [n_r [Hn_r_node Hn_r_layout]].
    assert (Hprod : node_produces (layout net) n_r (rel_of f))
      by (eapply fires_node_produces; eauto).
    assert (Hsrc : good_source net n_r (rel_of f)) by (apply Hprodsrc; exact Hprod).
    exists n_r. split; [|exact Hsrc].
    (* every hypothesis is available at [n_r] (forwarded from its own source to this consumer) *)
    assert (Hlifted : Forall (fun f' => network_pftree net (FactOnNode n_r f')) l).
    { rewrite Forall_forall in IH |- *. intros f' Hf'in.
      destruct (IH f' Hf'in) as [n' [Hpf' Hsrc']].
      assert (Hcons : node_consumes (layout net) n_r (rel_of f'))
        by (eapply fires_node_consumes; eauto).
      eapply fact_at_source_consumer; eauto. }
    eapply pftree_step with (l := List.map (FactOnNode n_r) l).
    + apply RuleApp with (r := r).
      * exact Hn_r_layout.
      * rewrite get_facts_fst_map_FactOnNode.
        apply Forall_forall. intros n' Hin.
        apply in_map_iff in Hin. destruct Hin as [? [? ?]]. auto.
      * rewrite get_facts_on_node_map_FactOnNode.
        rewrite map_map. simpl. rewrite map_id. exact Hfires.
    + apply Forall_map.
      rewrite Forall_forall in Hlifted |- *. intros f' Hf'in. apply Hlifted. exact Hf'in.
Qed.

(* Derivability depends only on the rule SET: a larger program derives at least as much.  Used to
   relate a non-distributed program [P] to the canonical union of the distributed per-node rules
   (same set => same derivable facts). *)
Lemma prog_impl_fact_subset (p1 p2 : list rule) (Q : fact -> Prop) (f : fact) :
  (forall r, In r p1 -> In r p2) ->
  prog_impl_fact p1 Q f -> prog_impl_fact p2 Q f.
Proof.
  intros Hsub. unfold prog_impl_fact.
  apply (pftree_ind
           (fun f hyps => Exists (fun r => fires r f hyps) p1) Q
           (fun f => pftree (fun f hyps => Exists (fun r => fires r f hyps) p2) Q f)).
  - intros f0 HQ. apply pftree_leaf. exact HQ.
  - intros f0 l Hex _ IH. eapply pftree_step; [| exact IH].
    apply Exists_exists in Hex. destruct Hex as [r [Hr Hf]].
    apply Exists_exists. exists r. split; [apply Hsub; exact Hr | exact Hf].
Qed.

Theorem completeness (net : DataflowNetwork) (program : list rule) (Q : fact -> Prop) :
  good_network_streaming net program Q ->
  forall f, prog_impl_fact program Q f -> network_prog_impl_fact net f.
Proof.
  intros Hnet f Hprog.
  destruct (completeness_with_source net program Q Hnet f Hprog) as [n [Hpf Hsrc]].
  destruct Hsrc as [_ [n_out [Hout Hreach]]].
  exists n_out.
  eapply pftree_step with (l := [FactOnNode n_out f]).
  - apply OutputStep. exact Hout.
  - constructor; [| constructor].
    destruct Hreach as [-> | Hfwd].
    + exact Hpf.
    + eapply forwarding_lifts; [exact Hpf | exact Hfwd].
Qed.

End DistributedDatalog.
