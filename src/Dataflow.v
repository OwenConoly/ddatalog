From Stdlib Require Import List Bool.
From Datalog Require Import Datalog.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.
From DatalogRocq Require Import Graph.

Import ListNotations.

Section DistributedDatalog.

  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context `{query_sig : query_signature rel}.
  Context {context : map.map var T}.
  Context {context_ok : map.ok context}.
  Context {Node Info : Type}.
  Context {node_eqb : Node -> Node -> bool}.
  Context {node_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (node_eqb x y)}.

  Definition fact := fact rel var fn.
  Definition rule := rule rel var fn aggregator.

  Definition ForwardingTable := rel -> list Node.
  Definition ForwardingFn := Node -> ForwardingTable.
  Definition InputFn := Node -> rel * list T -> Prop.
  Definition OutputFn := Node -> rel * list T -> Prop.
  Definition Layout := Node -> list rule.

  Record DataflowNetwork := {
    graph : Graph (Node := Node);
    forward : ForwardingFn;
    input :  InputFn;
    output : OutputFn;
    layout : Layout
  }.

Inductive network_prop := 
  | FactOnNode (n : Node) (f : rel * list T)
  | Output (n : Node) (f : rel * list T).

Fixpoint get_facts_on_node (nps : list (network_prop)) : list (Node * (rel * list T)) :=
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
      rule_impl r f (map snd (get_facts_on_node hyps)) ->
      network_step net (FactOnNode n f) (hyps)
  | Forward n n' f :
      In n' (net.(forward) n (fst f)) ->
      network_step net (FactOnNode n' f) [FactOnNode n f].
  (* | OutputStep n f :
      net.(output) n f ->
      network_step net (Output n f) [FactOnNode n f]. *)

Definition network_pftree (net : DataflowNetwork) : network_prop -> Prop :=
  pftree (fun fact_node hyps => network_step net fact_node hyps).

(* Definition network_prog_impl_fact (net : DataflowNetwork) : rel * list T -> Prop :=
  fun f => exists n, network_pftree net (Output n f). *)

Definition network_prog_impl_fact (net : DataflowNetwork) : rel * list T -> Prop :=
  fun f => exists n, network_pftree net (FactOnNode n f).

(* A good layout has every program rule on a node somewhere AND only assigns rules from 
   the program to nodes *)
Definition good_layout (layout : Layout) (nodes : Node -> Prop) (program : list rule) : Prop :=
   Forall (fun r => exists n, nodes n /\ In r (layout n)) program /\
   forall n r, (In r (layout n) -> nodes n /\ In r program).

(* n produces facts of relation r *)
(* Definition node_produces (layout : Layout) (n : Node) (r : rel) : Prop :=
  exists rule, In rule (layout n) /\
    forall f, rule_impl rule f [] -> fst f = r. *)

Definition node_produces (layout : Layout) (n : Node) (rel : rel) : Prop :=
  exists rule concl, In rule (layout n) /\ In concl rule.(rule_concls) /\
    concl.(fact_R) = rel.

(* n consumes facts of relation r — needs r as a hypothesis in some rule *)
Definition node_consumes (layout : Layout) (n : Node) (rel : rel) : Prop :=
  exists rule, In rule (layout n) /\
    ((exists hyp, In hyp (rule_hyps rule) /\ hyp.(fact_R) = rel) \/
     (exists agg_expr v,
        rule.(rule_agg) = Some (v, agg_expr) /\
        exists hyp, In hyp (agg_expr.(agg_hyps)) /\ hyp.(fact_R) = rel)).
  
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

(* The forwarding table is good for a relation r if for every producer,
   there is a path to every consumer *)
Definition good_forwarding_for_rel (net : DataflowNetwork) (r : rel) : Prop :=
  forall n_prod n_cons,
    node_produces net.(layout) n_prod r ->
    node_consumes net.(layout) n_cons r ->
    n_prod = n_cons \/ forwarding_reachable net.(forward) r n_prod n_cons.

(* Apply it to all relations *)
Definition good_forwarding_complete (net : DataflowNetwork) : Prop :=
  forall rel, good_forwarding_for_rel net rel.

(* A good forwarding function should only be able to forward things along the 
   edges *)
Definition good_forwarding_sound (forward : ForwardingFn) (nodes : Node -> Prop) (edges : Node -> Node -> Prop) : Prop :=
  forall n1 n2 r, In n2 (forward n1 r) -> nodes n1 /\ nodes n2 /\ edges n1 n2.

Definition good_forwarding (forward : ForwardingFn) (net : DataflowNetwork): Prop :=
  good_forwarding_sound forward net.(graph).(nodes) net.(graph).(edge) /\
  good_forwarding_complete net.

(* This is a temporary thing, the format will change once we have a solid streaming
   model. *)

Definition good_input (input : InputFn) (program : list rule) : Prop := 
  forall n f, input n f ->
    exists r, In r program /\ rule_impl r f [].

Definition good_network (net : DataflowNetwork) (program : list rule) : Prop :=
  good_graph net.(graph) /\
  good_layout net.(layout) net.(graph).(nodes) program /\
  good_forwarding net.(forward) net /\
  good_input net.(input) program.

Lemma Forall_get_facts_on_node :
  forall (l : list network_prop)
         (P : Node * (rel * list T) -> Prop)
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

(* Some of these aren't properly formulated with the right conditions yet, but
   this is kinda the framework I'm going for here. *)
Theorem soundness' (net : DataflowNetwork) (program : list rule) :
  forall n f, 
  good_network net program ->
  network_pftree net (FactOnNode n f)  ->
  prog_impl_fact program f.
Proof.
  intros. remember (FactOnNode n f) as node_fact.
  generalize dependent n. generalize dependent f.
  induction H0.
  intros.
  subst.
  unfold prog_impl_fact.
  inversion H0.
  - unfold good_network in H. fwd.
    unfold good_input in Hp3.
    specialize (Hp3 n f); subst.
    apply Hp3 in H6.
    econstructor; eauto.
    apply Exists_exists.
    eauto.
  - econstructor.
   + unfold good_network in H. fwd.
     unfold good_layout in Hp1. fwd.
     specialize (Hp1p1 n r). 
     apply Hp1p1 in H5.
     destruct H5 as [Hnode Hin].
     apply Exists_exists.
     exists r; eauto.
   + apply Forall_map; subst.
    eapply Forall_get_facts_on_node; eauto.
    intros.
    simpl in H3.
    eapply H3; eauto.
  - rewrite <- H4 in H2. 
    inversion H2.
    eapply H9; eauto.
Qed.

Theorem soundness (net : DataflowNetwork) (program : list rule) :
  forall f, 
  good_network net program ->
  network_prog_impl_fact net f ->
  prog_impl_fact program f.
Proof.
  intros.
  destruct H0.
  unfold network_prog_impl_fact in H0.
  inversion H0.
  eapply soundness'; eauto.
  (* inversion H1.
  subst.
  inversion H2.
  eapply soundness'; eauto. *)
Qed.

Lemma In_singular : forall {A} (x y : A) (l : list A), In x (y :: l) -> x = y \/ In x l.
Proof.
  intros. inversion H; auto.
Qed.

Lemma forwarding_lifts :
  forall net n1 n2 f,
    network_pftree net (FactOnNode n1 f) ->
    forwarding_reachable net.(forward) (fst f) n1 n2 ->
    network_pftree net (FactOnNode n2 f).
Proof.
  intros net n1 n2 f Hpf Hreach.
  induction Hreach.
  - (* single step: n1 -> n2 directly *)
    apply mkpftree with (l := [FactOnNode n1 f]).
    + apply Forward. exact H.
    + constructor; [exact Hpf | constructor].
  - (* transitive: n1 -> n2 -> n3 *)
    apply IHHreach.
    apply mkpftree with (l := [FactOnNode n1 f]).
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

Lemma interp_fact_same_rel :
  forall (ctx : context) (f_spec : fact) (f_val : rel * list T),
    interp_fact ctx f_spec f_val ->
    fst f_val = f_spec.(fact_R).
Proof.
  intros ctx f_spec f_val Hinterp.
  inversion Hinterp; subst.
  reflexivity.
Qed.


Lemma interp_agg_expr_hyps :
  forall (ctx : context)
         (aexpr : agg_expr rel var fn aggregator)
         (res : T)
         (agg_hyps's : list (list (rel * list T)))
         (f' : rel * list T),
    interp_agg_expr ctx aexpr res agg_hyps's ->
    (exists agg_hyps,
        In agg_hyps agg_hyps's /\ In f' agg_hyps) ->
    exists hyp,
      In hyp (agg_hyps aexpr) /\
      fact_R hyp = fst f'.
Proof.
  intros ctx aexpr res agg_hyps's f' Hinterp [agg_hyps [Hin_outer Hin_inner]].
  inversion Hinterp; subst.
  eapply List.Forall3_in_right with (z := agg_hyps) in H1 as Hproj; auto.
  destruct Hproj as [i' [body' [Hi'_in [Hbody'_in Hrel]]]].
  destruct Hrel as [vs' [ctx' [Hzip [HF2 _]]]].
  eapply Forall2_exists_r in HF2; eauto.
  destruct HF2 as [hyp [Hhyp_in Hinterp_hyp]].
  exists hyp. split.
  - simpl. exact Hhyp_in.
  - apply interp_fact_same_rel in Hinterp_hyp. simpl in Hinterp_hyp. symmetry. exact Hinterp_hyp.
Qed.

Lemma rule_impl_produces_rel :
  forall (r : Datalog.rule rel var fn aggregator) 
         (f : rel * list T) 
         (hyps : list (rel * list T)),
    rule_impl r f hyps ->
    exists concl, In concl (rule_concls r) /\ concl.(fact_R) = fst f.
Proof.
  intros r f hyps Himpl.
  unfold rule_impl in Himpl.
  destruct Himpl as [ctx [hyps' [agg_hyps's [_ Himpl']]]].
  inversion Himpl'; subst.
  apply Exists_exists in H0.
  destruct H0 as [concl [Hconclin Hinterp]].
  exists concl. split.
  - exact Hconclin.
  - eapply interp_fact_same_rel in Hinterp. simpl in Hinterp. symmetry. exact Hinterp.
Qed.

Lemma rule_impl_consumes_rel :
  forall (r : Datalog.rule rel var fn aggregator)
         (f : rel * list T)
         (hyps : list (rel * list T))
         (f' : rel * list T),
    rule_impl r f hyps ->
    In f' hyps ->
    ((exists hyp, In hyp (rule_hyps r) /\ hyp.(fact_R) = fst f') \/
     (exists agg_expr v,
        r.(rule_agg) = Some (v, agg_expr) /\
        exists hyp, In hyp (agg_expr.(agg_hyps)) /\ hyp.(fact_R) = fst f')).
Proof.
  intros r f hyps f' Himpl Hin.
  unfold rule_impl in Himpl.
  destruct Himpl as [ctx [hyps' [agg_hyps's [Heq Himpl']]]].
  inversion Himpl'; subst.
  (* rewrite Heq in Hin. *)
  apply in_app_or in Hin.
  destruct Hin as [Hin | Hin].
  - left.
    destruct (Forall2_exists_r _ _ _ f' H1 Hin) as [hyp [Hhypin Hinterp]].
    exists hyp. split.
    + exact Hhypin.
    + eapply interp_fact_same_rel in Hinterp. simpl in Hinterp. auto.
  - (* f' came from agg_hyps's *)
    right.
    apply in_concat in Hin.
    destruct Hin as [agg_hyps [Hin_outer Hin_inner]].
    inversion H; subst.
    + simpl in Hin_outer. inversion Hin_outer.
    + exists aexpr, res. split; auto.
      assert (Hex : exists agg_hyps0, In agg_hyps0 agg_hyps's /\ In f' agg_hyps0).
    {
      exists agg_hyps; auto.
    }
    destruct (interp_agg_expr_hyps ctx aexpr res' agg_hyps's f' H6 Hex) as [hyp [Hhypin Hinterp]].
    exists hyp.
    auto.
Qed.

(* If a rule fires producing f, the node where that rule lives is a producer of fst f *)
Lemma rule_impl_node_produces :
  forall (r : Datalog.rule rel var fn aggregator)
         (f : rel * list T)
         (hyps : list (rel * list T))
         (n : Node)
         (net : DataflowNetwork),
    rule_impl r f hyps ->
    In r (layout net n) ->
    node_produces (layout net) n (fst f).
Proof.
  intros r f hyps n net Himpl Hin_layout.
  apply rule_impl_produces_rel in Himpl.
  destruct Himpl as [concl [Hconcl_in Hrel_eq]].
  exists r, concl. auto.
Qed.

(* If a rule fires consuming f', the node where that rule lives is a consumer of fst f' *)
Lemma rule_impl_node_consumes :
  forall (r : Datalog.rule rel var fn aggregator)
         (f : rel * list T)
         (hyps : list (rel * list T))
         (f' : rel * list T)
         (n : Node)
         (net : DataflowNetwork),
    rule_impl r f hyps ->
    In f' hyps ->
    In r (layout net n) ->
    node_consumes (layout net) n (fst f').
Proof.
  intros r f hyps f' n net Himpl Hf'in Hin_layout.
  exists r. split; [exact Hin_layout |].
  eapply rule_impl_consumes_rel; eauto.
Qed.

(* If a fact is at a producer, it can be forwarded to any consumer *)
Lemma fact_at_consumer :
  forall (net : DataflowNetwork) (f : rel * list T) (n_prod n_cons : Node),
    good_forwarding_complete net ->
    network_pftree net (FactOnNode n_prod f) ->
    node_produces (layout net) n_prod (fst f) ->
    node_consumes (layout net) n_cons (fst f) ->
    network_pftree net (FactOnNode n_cons f).
Proof.
  intros net f n_prod n_cons Hfwdc Hpf Hprod Hcons.
  unfold good_forwarding_complete, good_forwarding_for_rel in Hfwdc.
  destruct (Hfwdc (fst f) n_prod n_cons Hprod Hcons) as [Heq | Hreach].
  - subst. exact Hpf.
  - eapply forwarding_lifts; eauto.
Qed.

(*  Every derivable fact exists at a producer node *)
Lemma completeness_with_producer (net : DataflowNetwork) (program : list rule) :
  forall f,
    good_network net program ->
    (* good_forwarding_complete net -> *)
    prog_impl_fact program f ->
    exists n, network_pftree net (FactOnNode n f) /\
              node_produces (layout net) n (fst f).
Proof.
  intros f Hnet Hprog.
  destruct Hnet as [Hgraph [Hlayout [[Hforwardings Hforwardingc] Hinput]]].
  destruct Hlayout as [Hlayout_complete Hlayout_sound].
  rewrite Forall_forall in Hlayout_complete.
  induction Hprog as [f l Hexists Hforall IH].
  apply Exists_exists in Hexists.
  destruct Hexists as [r [Hr_in Himpl]].
  destruct (Hlayout_complete r Hr_in) as [n_r [Hn_r_node Hn_r_layout]].
  (* n_r produces fst f *)
  assert (Hprod : node_produces (layout net) n_r (fst f)).
  { eapply rule_impl_node_produces; eauto. }
  exists n_r. split; [| exact Hprod].
  (* Show all hyps of l are available at n_r *)
  assert (Hlifted : Forall (fun f' => network_pftree net (FactOnNode n_r f')) l).
  { rewrite Forall_forall in IH |- *.
    intros f' Hf'in.
    (* By IH, f' has a proof tree at some producer *)
    destruct (IH f' Hf'in) as [n_prod [Hpf' Hprod']].
    (* n_r consumes fst f' because r uses f' as a hypothesis *)
    assert (Hcons : node_consumes (layout net) n_r (fst f')).
    { eapply rule_impl_node_consumes; eauto. }
    (* Forward from producer to consumer *)
    eapply fact_at_consumer; eauto.
  }
  (* Fire rule r at n_r *)
  apply mkpftree with (l := List.map (FactOnNode n_r) l).
  - apply RuleApp with (r := r).
    + exact Hn_r_layout.
    + rewrite get_facts_fst_map_FactOnNode.
      apply Forall_forall. intros n' Hin.
      apply in_map_iff in Hin. destruct Hin as [? [? ?]]. auto.
    + rewrite get_facts_on_node_map_FactOnNode.
      rewrite map_map. simpl. rewrite map_id.
      exact Himpl.
  - apply Forall_map.
    rewrite Forall_forall in Hlifted |- *.
    intros f' Hf'in. apply Hlifted. exact Hf'in.
Qed.

Theorem completeness (net : DataflowNetwork) (program : list rule) :
  forall f,
    good_network net program ->
    prog_impl_fact program f ->
    network_prog_impl_fact net f.
Proof.
  intros f Hnet Hprog.
  destruct (completeness_with_producer net program f Hnet Hprog) as [n [Hpf _]].
  exists n. exact Hpf.
Qed.

End DistributedDatalog.