From Stdlib Require Import List Bool.
From Datalog Require Import Datalog Tactics.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.
From Stdlib Require Import Lia.

Import ListNotations.

Section DistributedDatalog.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map var T}.
  Context {context_ok : map.ok context}.
  Context {Node Info : Type}.
  Context (all_nodes : list Node).
  Context (Hall_nodes : NoDup all_nodes /\ (forall n, In n all_nodes)).
  Context {node_eqb : Node -> Node -> bool}.
  Context {node_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (node_eqb x y)}.
  Context (is_input : rel -> bool).
  Context {rel_eqb : rel -> rel -> bool}.
  Context {rel_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (rel_eqb x y)}.

  Inductive dfact :=
  | normal_dfact (nf_rel: rel) (nf_args: list T)
  | meta_dfact (mf_rel: rel) (source: option Node) (expected_msgs: nat).

  Let clause := clause rel var fn.
  Let rule := rule rel var fn aggregator T.
  Let fact := fact rel T.

  Inductive drule :=
  | normal_drule (rule_concls : list clause) (rule_hyps : list clause)
  | agg_drule (rule_agg : aggregator) (target_rel : rel) (source_rel : rel)
  | meta_drule (target_rel : rel) (source_rels : list rel).    
  
  (*i assume graph is strongly connected, because i suspect this will be tricky enough as is*)
  Record node_state := {
      known_facts: list dfact;
      (*how many messages have i received about this relation*)
      msgs_received: rel -> nat;
      (*how many messages have i sent about this relation*)
      msgs_sent: rel -> nat;
      (*am i guaranteed to be completely done sending messages about this relation?*)
      (* finished_rel : rel -> bool; *)
    }.

  Record graph_state := {
      node_states : Node -> node_state;
      (*if (n, f) is in this list, then fact f has been sent to node n but has not yet been received*)
      facts_on_wires : list (Node * dfact);
      (*inputs that have been received so far*)
      input_facts : list dfact;
    }.

  (*i ignore all of this for now; i assume that the graph is strongly connected, and Node is a finite set whose elements are exactly the nodes of the traph*)
  (* Record Graph := { *)
  (*   nodes : Node -> Prop; *)
  (*   edge : Node -> Node -> Prop *)
  (* }. *)

  (* Definition good_graph (g : Graph) :=  *)
  (*  forall n1 n2, edge g n1 n2 -> nodes g n1 /\ nodes g n2. *)

  (* Inductive path (g : Graph) : Node -> Node -> Prop := *)
  (*   | path_nil n : *)
  (*       g.(nodes) n -> *)
  (*       path g n n  *)
  (*   | path_cons n1 n2 n3 : *)
  (*       g.(edge) n1 n2 -> *)
  (*       path g n2 n3 -> *)
  (*       path g n1 n3. *)
  
  (* Definition strongly_connected (g : Graph) : Prop := *)
  (*   forall n1 n2, g.(nodes) n1 -> g.(nodes) n2 -> path g n1 n2. *)

  (* Definition ForwardingTable := rel * list T -> list Node. *)
  (* Definition ForwardingFn := Node -> ForwardingTable. *)
  (* Definition InputFn := Node -> rel * list T -> Prop. *)
  (* Definition OutputFn := Node -> rel * list T -> Prop. *)
  Definition Layout := Node -> list drule.

  Record DataflowNetwork := {
    (* graph : Graph; *)
    (* forward : ForwardingFn; *)
    (* input :  InputFn; *)
    (* output : OutputFn; *)
    layout : Layout
  }.

(* Inductive network_prop :=  *)
(*   | FactOnNode (n : Node) (f : rel * list T) *)
(*   | Output (n : Node) (f : rel * list T). *)

(* Fixpoint get_facts_on_node (nps : list (network_prop)) : list (Node * (rel * list T)) := *)
(*   match nps with *)
(*   | [] => [] *)
(*   | FactOnNode n f :: t => (n, f) :: get_facts_on_node t *)
(*   | Output n f :: t => get_facts_on_node t *)
(*   end. *)

(* Inductive network_step (net : DataflowNetwork) : network_prop -> list (network_prop) -> Prop := *)
(*   | Input n f :  *)
(*       net.(input) n f -> *)
(*       network_step net (FactOnNode n f) [] *)
(*   | RuleApp n f r hyps : *)
(*       In r (net.(layout) n) -> *)
(*       Forall (fun n' => n' = n) (map fst (get_facts_on_node hyps)) -> *)
(*       Datalog.rule_impl r f (map snd (get_facts_on_node hyps)) -> *)
(*       network_step net (FactOnNode n f) (hyps) *)
(*   | Forward n n' f : *)
(*       In n' (net.(forward) n f) -> *)
(*       network_step net (FactOnNode n' f) [FactOnNode n f] *)
(*   | OutputStep n f : *)
(*       net.(output) n f -> *)
(*       network_step net (Output n f) [FactOnNode n f]. *)

  Print node_state.
  Print Datalog.rule. Print rule_impl. Print Datalog.fact.
  Definition can_learn_normal_fact_at_node rules ns R args :=
    exists r, In r rules /\
    match r with
    | normal_drule rule_concls rule_hyps =>
        exists ctx hyps',
        Exists (fun c => interp_clause ctx c (R, args)) rule_concls /\
          Forall2 (interp_clause ctx) rule_hyps hyps' /\
          (forall R0 args0, In (R0, args0) hyps' ->
                       In (normal_dfact R0 args0) ns.(known_facts))
    | agg_drule rule_agg target_rel source_rel =>
        exists vals,
        (forall x, In x vals <-> In (normal_dfact source_rel [x]) ns.(known_facts)) /\
          R = target_rel /\
          args = [fold_right (interp_agg rule_agg) (agg_id rule_agg) vals]
    | meta_drule _ _ => False
    end.

  Definition expect_num_R_facts R known_facts num :=
    In (meta_dfact R None num) known_facts \/
      exists expected_msgss,
        Forall2 (fun n expected_msgs => In (meta_dfact R (Some n) expected_msgs) known_facts) all_nodes expected_msgss /\
          num = fold_right Nat.add O expected_msgss.

  Definition can_learn_meta_fact_at_node rules ns R expected_msgs :=
    exists r, In r rules /\
    match r with
    | normal_drule _ _ => False
    | agg_drule _ _ _ => False
    | meta_drule R0 R's =>
        R0 = R /\
        (forall R', In R' R's ->
               expect_num_R_facts R' ns.(known_facts) (ns.(msgs_received) R')) /\
        (forall args,
            can_learn_normal_fact_at_node rules ns R args ->
            In (normal_dfact R args) ns.(known_facts)) /\
          expected_msgs = ns.(msgs_sent) R
    end.

  Definition should_learn_fact_at_node rules n ns f :=
    match f with
    | normal_dfact R args =>
        can_learn_normal_fact_at_node rules ns R args
    | meta_dfact R n0 expected_msgs =>
        n0 = Some n /\
        can_learn_meta_fact_at_node rules ns R expected_msgs
    end.

  Definition receive_fact_at_node ns f :=
    match f with
    | normal_dfact R args =>
        {| known_facts := f :: ns.(known_facts);
          msgs_received := fun R' => if rel_eqb R R' then
                                    S (ns.(msgs_received) R)
                                  else ns.(msgs_received) R';
          msgs_sent := ns.(msgs_sent) |}
    | meta_dfact _ _ _ =>
        {| known_facts := f :: ns.(known_facts);
          msgs_received := ns.(msgs_received);
          msgs_sent := ns.(msgs_sent) |}
    end.

  Definition is_input_fact f :=
    match f with
    | normal_dfact R _ => is_input R
    | meta_dfact R None _ => is_input R
    | meta_dfact _ (Some _) _ => false
    end.
  
  Inductive graph_step (rule_assignments : Node -> list drule) : graph_state -> graph_state -> Prop :=
  | Input g f :
    graph_step _
      g
      {| node_states := g.(node_states);
        facts_on_wires := map (fun n => (n, f)) all_nodes ++ g.(facts_on_wires);
        input_facts := f :: g.(input_facts); |}
  | ReceiveFact g n f fs1 fs2 :
    g.(facts_on_wires) = fs1 ++ (n, f) :: fs2 ->
    graph_step _
      g
      {| node_states := fun n' => if node_eqb n n' then
                                 receive_fact_at_node (g.(node_states) n) f
                               else g.(node_states) n';
        facts_on_wires := fs1 ++ fs2;
        input_facts := g.(input_facts); |}
  | LearnFact g n f :
    should_learn_fact_at_node (rule_assignments n) n (g.(node_states) n) f ->
    graph_step _
      g
      {| node_states := fun n' => if node_eqb n n' then
                                 receive_fact_at_node (g.(node_states) n) f
                               else g.(node_states) n';
        facts_on_wires := map (fun n => (n, f)) all_nodes ++ g.(facts_on_wires);
        input_facts := g.(input_facts) |}.

  Print graph_state.
  
  Definition good_layout (p : list rule) (rules : Node -> list drule) :=
    (forall rule_concls rule_hyps,
        In (normal_rule rule_concls rule_hyps) p <-> exists n, In (normal_drule rule_concls rule_hyps) (rules n)) /\
      (forall agg target_rel source_rel,
          In (agg_rule agg target_rel source_rel) p <-> exists n, In (agg_drule agg target_rel source_rel) (rules n)) /\
      (forall target_rel target_set source_rels,
          In (meta_rule target_rel target_set source_rels) p ->
          forall n, In (meta_drule target_rel source_rels) (rules n)) /\
      (forall target_rel source_rels n,
          In (meta_drule target_rel source_rels) (rules n) ->
          exists target_set,
            In (meta_rule target_rel target_set source_rels) p).

  Definition knows_fact (g : graph_state) f : Prop :=
    In f g.(input_facts) \/
      exists n, In f (g.(node_states) n).(known_facts).

  (*no, should not talk about set sizes, should talk about number satisfying criteria in input facts*)
  Inductive Existsn {T} (P : T -> Prop) : nat -> list T -> Prop :=
  | Existsn_nil : Existsn _ 0 []
  | Existsn_no x n l :
    ~P x ->
    Existsn _ n l ->
    Existsn _ n (x :: l)
  | Existsn_yes x n l :
    P x ->
    Existsn _ n l ->
    Existsn _ (S n) (x :: l).

  Definition facts_of (inputs : list dfact) :=
    fun f =>
      match f with
      | normal_fact R args => In (normal_dfact R args) inputs
      | meta_fact R Rset =>
          exists n,
          In (meta_dfact R None n) inputs /\
            (forall args, Rset args <-> In (normal_dfact R args) inputs) /\
            Existsn (fun f => match f with
                           | normal_dfact R' _ => R = R'
                           | meta_dfact _ _ _ => False
                           end)
              n inputs
      end.

  Definition good_inputs (inputs : list dfact) :=
    Forall (fun f => is_input_fact f = true) inputs /\
      (forall R num,
          In (meta_dfact R None num) inputs ->
          exists num',
            num' <= num /\
              Existsn (fun f => match f with
                           | normal_dfact R' _ => R = R'
                           | meta_dfact _ _ _ => False
                           end)
                num' inputs).
  Print can_learn_normal_fact_at_node.
  Notation "R ^*" := (Relations.trc R) (at level 0).
  Definition good_graph rules (p : list rule) g :=
    good_inputs g.(input_facts) ->
    (forall R args,
        knows_fact g (normal_dfact R args) ->
        prog_impl_implication p (facts_of g.(input_facts)) (normal_fact R args)) /\
      (forall R n num,
          In (meta_dfact R (Some n) num) (g.(node_states) n).(known_facts) ->
          forall g' args,
            (graph_step rules)^* g g' ->
            good_inputs g'.(input_facts) ->
            can_learn_normal_fact_at_node (rules n) (g'.(node_states) n) R args ->
            In (normal_dfact R args) (g.(node_states) n).(known_facts)) /\
      (forall R num,
          knows_fact g (meta_dfact R None num) ->
          In (meta_dfact R None num) g.(input_facts)) /\
      (forall R num n,
          knows_fact g (meta_dfact R (Some n) num) ->
          In (meta_dfact R (Some n) num) (g.(node_states) n).(known_facts)) /\
      (forall n f,
          In (n, f) g.(facts_on_wires) ->
          knows_fact g f).
  
  Lemma combine_fst_snd {A B} (l : list (A * B)) :
    l = combine (map fst l) (map snd l).
  Proof.
    induction l; simpl; f_equal; auto. destruct a; reflexivity.
  Qed.

  Lemma good_inputs_cons f fs :
    good_inputs (f :: fs) ->
    good_inputs fs.
  Proof.
    cbv [good_inputs]. simpl. intros [H1 H2]. invert H1. split; [assumption|].
    intros R num H. specialize (H2 R num ltac:(auto)). clear -H2.
    fwd. invert H2p1; eauto. eexists. split; [|eauto]. lia.
  Qed.

  Lemma Existsn_unique U P n m (l : list U) :
    Existsn P n l ->
    Existsn P m l ->
    n = m.
  Proof.
    intros H. revert m. induction H; invert 1; auto.
    all: exfalso; auto.
  Qed.
        
  Lemma facts_of_cons f fs f' :
    good_inputs (f :: fs) ->
    facts_of fs f' ->
    facts_of (f :: fs) f'.
  Proof.
    intros Hgood H. destruct f'; simpl in *; auto. fwd. eexists. split.
    { right. eassumption. }
    split.
    { intros. rewrite Hp1. split; auto. intros [H|H]; auto. subst.
      exfalso. cbv [good_inputs] in Hgood. simpl in Hgood. destruct Hgood as [_ Hgood].
      specialize (Hgood _ _ ltac:(eauto)). fwd. invert Hgoodp1.
      - congruence.
      - eapply Existsn_unique in Hp2; [|exact H3]. subst. lia. }
    apply Existsn_no. 2: assumption. intros H. destruct f; try contradiction.
    subst. cbv [good_inputs] in Hgood. simpl in Hgood. destruct Hgood as [_ Hgood].
    specialize (Hgood _ _ ltac:(eauto)). fwd. invert Hgoodp1.
    - congruence.
    - eapply Existsn_unique in Hp2; [|exact H3]. subst. lia.
  Qed.

  Lemma receive_fact_at_node_gets_more_facts f f' ns :
    In f ns.(known_facts) ->
    In f (receive_fact_at_node ns f').(known_facts).
  Proof.
    intros H. destruct f'; simpl; auto.
  Qed.
  
  Hint Unfold knows_fact : core.
  Hint Constructors graph_step : core.
  Hint Constructors Relations.trc : core.
  Lemma good_layout_normal_facts_sound p rules g g' :
    good_layout p rules ->
    graph_step rules g g' ->
    good_graph rules p g ->
    good_graph rules p g'.
  Proof.
    intros Hlayout Hstep Hgraph. intros Hinp.
    invert Hstep; simpl in *.
    - specialize (Hgraph ltac:(eauto using good_inputs_cons)).
      destruct Hgraph as (Hnorm&Hmetanode&Hmetainp&Hmnk&Hwires). ssplit.
      + cbv [knows_fact]. simpl. intros R args H. destruct H as [[H | H] | H].
        -- subst. apply partial_in. simpl. auto.
        -- eapply prog_impl_implication_weaken_hyp.
           ++ apply Hnorm. cbv [knows_fact]. auto.
           ++ auto using facts_of_cons.
        -- eapply prog_impl_implication_weaken_hyp.
           ++ apply Hnorm. cbv [knows_fact]. auto.
           ++ auto using facts_of_cons.
      + intros R n num Hkm g' args Hsteps Hinp' Hkn.
        eapply Hmetanode.
        -- eassumption.
        -- eapply Relations.TrcFront. 2: eassumption. apply Input.
        -- assumption.
        -- assumption.
      + intros R num H. cbv [knows_fact] in H. simpl in H.
        destruct H as [[H|H] |H]; eauto.
      + intros R num n H. cbv [knows_fact] in H. simpl in H.
        destruct H as [H |H].
        -- exfalso. destruct Hinp as [Hinp _]. rewrite Forall_forall in Hinp.
           simpl in Hinp. specialize (Hinp _ H). simpl in Hinp. congruence.
        -- fwd. eauto.
      + intros n f' Hf'. apply in_app_iff in Hf'. cbv [knows_fact]. simpl.
        destruct Hf' as [Hf'|Hf'].
        -- apply in_map_iff in Hf'. fwd. eauto.
        -- apply Hwires in Hf'. cbv [knows_fact] in Hf'. destruct Hf'; eauto.
    - specialize (Hgraph Hinp).
      destruct Hgraph as (Hnorm&Hmetanode&Hmetainp&Hmnk&Hwires). ssplit.
      + cbv [knows_fact]. simpl. intros R args Hkn. destruct Hkn as [Hkn | Hkn].
        -- eauto.
        -- fwd. destr (node_eqb n n0); eauto. apply Hnorm. destruct f; simpl in Hkn.
           ++ destruct Hkn as [Hkn|Hkn]; eauto.
              fwd. eapply Hwires. rewrite H. apply in_app_iff. simpl. eauto.
           ++ destruct Hkn as [Hkn|Hkn]; eauto. invert Hkn.
      + intros R n' num Hkm g' args Hsteps Hinp' Hkn.
        cbv [knows_fact] in Hkm. simpl in Hkm. destr (node_eqb n n').
        -- destruct f; simpl in *.
           ++ destruct Hkm as [Hkm|Hkm].
              --- invert Hkm.
              --- right. eapply Hmetanode. 1,3,4: eauto.
                  eapply Relations.TrcFront. 2: eassumption.
                  apply ReceiveFact with (f := normal_dfact _ _).
                  assumption.
           ++ destruct Hkm as [Hkm|Hkm].
              --- fwd. right. eapply Hmetanode. 3,4: eauto.
                  { apply Hmnk. eapply Hwires. rewrite H. apply in_app_iff.
                    simpl. eauto. }
                  eapply Relations.TrcFront. 2: eassumption.
                  apply ReceiveFact with (f := meta_dfact _ _ _).
                  assumption.
              --- right. eapply Hmetanode. 1,3,4: eauto.
                  eapply Relations.TrcFront. 2: eassumption.
                  apply ReceiveFact with (f := meta_dfact _ _ _).
                  assumption.
        -- eapply Hmetanode. 1,3,4: eauto.
           eapply Relations.TrcFront. 2: eassumption. apply ReceiveFact. assumption.
      + intros R num HR. cbv [knows_fact] in HR. simpl in HR.
        destruct HR as [HR |HR]; eauto. fwd. destr (node_eqb n n0); eauto.
        destruct f; simpl in HR.
        -- destruct HR as [HR|HR]; eauto. invert HR.
        -- destruct HR as [HR|HR]; eauto. fwd. apply Hmetainp. eapply Hwires.
           rewrite H. apply in_app_iff. simpl. eauto.
      + intros R num n' Hn'. cbv [knows_fact] in Hn'. simpl in Hn'.
        destruct Hn' as [Hn' |Hn'].
        -- exfalso. destruct Hinp as [Hinp _]. rewrite Forall_forall in Hinp.
           simpl in Hinp. specialize (Hinp _ Hn'). simpl in Hinp. congruence.
        -- fwd. destr (node_eqb n n0).
           ++ destr (node_eqb n0 n'); auto. apply Hmnk. destruct f; simpl in Hn'.
              --- destruct Hn' as [Hn'|Hn']; eauto. invert Hn'.
              --- destruct Hn' as [Hn'|Hn']; eauto. invert Hn'.
                  eapply Hwires. rewrite H. apply in_app_iff. simpl. eauto.
           ++ destr (node_eqb n n'); eauto. apply receive_fact_at_node_gets_more_facts.
              apply Hmnk. eauto.
      + intros n0 f0 H0. rewrite H in Hwires. specialize (Hwires n0 f0).
        rewrite in_app_iff in Hwires. simpl in Hwires. apply in_app_iff in H0.
        specialize (Hwires ltac:(destruct H0; auto)). destruct Hwires as [Hwires|Hwires].
        -- auto.
        -- cbv [knows_fact]. simpl. right. fwd. exists n1. destr (node_eqb n n1); eauto.
           apply receive_fact_at_node_gets_more_facts. assumption.
    - specialize (Hgraph Hinp).
      destruct Hgraph as (Hnorm&Hmetanode&Hmetainp&Hmnk&Hwires). ssplit.
      + cbv [knows_fact]. simpl. intros R args Hkn. destruct Hkn as [Hkn | Hkn].
        -- eauto.
        -- fwd. destr (node_eqb n n0); eauto. destruct f; simpl in Hkn.
           ++ destruct Hkn as [Hkn|Hkn]; eauto.
              fwd. simpl in H. cbv [can_learn_normal_fact_at_node] in H.
              fwd. destruct r; fwd. 3: contradiction.
              --- move Hlayout at bottom. cbv [good_layout] in Hlayout. fwd.
                  clear Hlayoutp1 Hlayoutp2 Hlayoutp3. epose_dep Hlayoutp0.
                  destruct Hlayoutp0 as [_ Hlayout]. specialize (Hlayout ltac:(eauto)).
                  eapply prog_impl_step.
                  +++ apply Exists_exists. eexists. split; [eassumption|].
                      econstructor. 1: eassumption. eassumption.
                  +++ apply Forall_map. apply Forall_forall.
                      intros [R' args'] H'. apply Hp1p2 in H'.
                      apply Hnorm. eauto.
              --- move Hlayout at bottom. cbv [good_layout] in Hlayout. fwd.
                  clear Hlayoutp0 Hlayoutp2 Hlayoutp3. epose_dep Hlayoutp1.
                  destruct Hlayoutp1 as [_ Hlayout]. specialize (Hlayout ltac:(eauto)).
                  
                  
              eapply Hwires. rewrite H. apply in_app_iff. simpl. eauto.
           ++ destruct Hkn as [Hkn|Hkn]; eauto. invert Hkn.
      
  
Definition network_pftree (net : DataflowNetwork) : network_prop -> Prop :=
  pftree (fun fact_node hyps => network_step net fact_node hyps).

Definition network_prog_impl_fact (net : DataflowNetwork) : rel * list T -> Prop :=
  fun f => exists n, network_pftree net (Output n f).

(* A good layout has every program rule on a node somewhere AND only assigns rules from 
   the program to nodes *)
Definition good_layout (layout : Layout) (nodes : Node -> Prop) (program : list rule) : Prop :=
   Forall (fun r => exists n, nodes n /\ In r (layout n)) program /\
   forall n r, (In r (layout n) -> nodes n /\ In r program).

(* A good forwarding function should only be able to forward things along the 
   edges *)
Definition good_forwarding (forward : ForwardingFn) (nodes : Node -> Prop) (edges : Node -> Node -> Prop) : Prop :=
  forall n1 n2 f, In n2 (forward n1 f) -> nodes n1 /\ nodes n2 /\ edges n1 n2.  

(* This is a temporary thing, the format will change once we have a solid streaming
   model. *)

Definition good_input (input : InputFn) (program : list rule) : Prop := 
  forall n f, input n f ->
    exists r, In r program /\
              Datalog.rule_impl r f [].

Definition good_network (net : DataflowNetwork) (program : list rule) : Prop :=
  good_graph net.(graph) /\
  good_layout net.(layout) net.(graph).(nodes) program /\
  good_forwarding net.(forward) net.(graph).(nodes) net.(graph).(edge) /\
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
 
(* Some of these aren't properly formulated with the right conditions yet, but
   this is kinda the framework I'm going for here. *)
Theorem soundness' (net : DataflowNetwork) (program : list rule) :
  forall n f, 
  good_network net program ->
  network_pftree net (FactOnNode n f)  ->
  Datalog.prog_impl_fact program f.
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
  Datalog.prog_impl_fact program f.
Proof.
  intros.
  destruct H0.
  unfold network_prog_impl_fact in H0.
  inversion H0.
  inversion H1.
  subst.
  inversion H2.
  eapply soundness'; eauto.
Qed.

Theorem completeness (net : DataflowNetwork) (program : list rule) :
  forall f, Datalog.prog_impl_fact program f -> 
  good_network net program ->
  network_prog_impl_fact net f.
Proof.
Admitted.

End DistributedDatalog.
