From Stdlib Require Import List Bool.
From Datalog Require Import Datalog Tactics.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.
From Stdlib Require Import Lia.
From ATL Require Import Relations. (*TODO i did not actually mean to use trc from here; should i use the stdlib thing instead?*)

Import ListNotations.

Section DistributedDatalog.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map var T}.
  Context {context_ok : map.ok context}.
  Context {Node Info : Type}.
  Context (a_node : Node).
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
      travellers : list (Node * dfact);
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

  Definition expect_num_R_facts R known_facts num :=
    if is_input R then
      In (meta_dfact R None num) known_facts
    else
      exists expected_msgss,
        Forall2 (fun n expected_msgs => In (meta_dfact R (Some n) expected_msgs) known_facts) all_nodes expected_msgss /\
          num = fold_left Nat.add expected_msgss O.

  Lemma expect_num_R_facts_incl R kf1 kf2 num :
    expect_num_R_facts R kf1 num ->
    incl kf1 kf2 ->
    expect_num_R_facts R kf2 num.
  Proof. Admitted.
  
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
        expect_num_R_facts source_rel ns.(known_facts) (ns.(msgs_received) source_rel) /\
        exists vals,
        (is_list_set (fun x => In (normal_dfact source_rel [x]) ns.(known_facts)) vals) /\
          R = target_rel /\
          args = [fold_right (interp_agg rule_agg) (agg_id rule_agg) vals]
    | meta_drule _ _ => False
    end.

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
        (forall num, ~In (meta_dfact R (Some n) num) ns.(known_facts)) /\ 
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

  Inductive inp_step : graph_state -> graph_state -> Prop :=
  | Input g f :
    inp_step
      g
      {| node_states := g.(node_states);
        travellers := map (fun n => (n, f)) all_nodes ++ g.(travellers);
        input_facts := f :: g.(input_facts); |}.  
  
  Inductive comp_step (rule_assignments : Node -> list drule) : graph_state -> graph_state -> Prop :=
  | ReceiveFact g n f fs1 fs2 :
    g.(travellers) = fs1 ++ (n, f) :: fs2 ->
    comp_step _
      g
      {| node_states := fun n' => if node_eqb n n' then
                                 receive_fact_at_node (g.(node_states) n) f
                               else g.(node_states) n';
        travellers := fs1 ++ fs2;
        input_facts := g.(input_facts); |}
  | LearnFact g n f :
    should_learn_fact_at_node (rule_assignments n) n (g.(node_states) n) f ->
    comp_step _
      g
      {| node_states := fun n' => if node_eqb n n' then
                                 receive_fact_at_node (g.(node_states) n) f
                               else g.(node_states) n';
        travellers := map (fun n => (n, f)) all_nodes ++ g.(travellers);
        input_facts := g.(input_facts) |}.

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
              Existsn (fun f => exists args, f = normal_dfact R args) num' inputs).

  Definition sound_graph (*rules*) (p : list rule) g :=
    good_inputs g.(input_facts) ->
    (forall R args,
        knows_fact g (normal_dfact R args) ->
        prog_impl_implication p (facts_of g.(input_facts)) (normal_fact R args)) (*/\*)
      (* (forall R n num, *)
      (*     In (meta_dfact R (Some n) num) (g.(node_states) n).(known_facts) -> *)
      (*     (g.(node_states) n).(msgs_sent) R = num *)
      (*     (* forall g' args, *) *)
      (*     (*   (graph_step rules)^* g g' -> *) *)
      (*     (*   good_inputs g'.(input_facts) -> *) *)
      (*     (*   can_learn_normal_fact_at_node (rules n) (g'.(node_states) n) R args -> *) *)
      (*     (*   In (normal_dfact R args) (g.(node_states) n).(known_facts) *)). *).

  Definition sane_graph g :=
    (forall R num,
        knows_fact g (meta_dfact R None num) ->
        In (meta_dfact R None num) g.(input_facts)) /\
      (forall R num n,
          knows_fact g (meta_dfact R (Some n) num) ->
          In (meta_dfact R (Some n) num) (g.(node_states) n).(known_facts)) /\
      (forall n f,
          In (n, f) g.(travellers) ->
          knows_fact g f) /\
      (forall R n num,
          In (meta_dfact R (Some n) num) (g.(node_states) n).(known_facts) ->
          (g.(node_states) n).(msgs_sent) R = num) /\
      (forall f, knows_fact g f ->
            forall n,
              In (n, f) g.(travellers) \/ In f (g.(node_states) n).(known_facts)) /\
      (forall n R,
        exists num_trav num_inp,
          Existsn (fun '(n', f) => n = n' /\ exists args, f = normal_dfact R args) num_trav g.(travellers) /\
            Existsn (fun f => exists args, f = normal_dfact R args) num_inp g.(input_facts) /\
            (g.(node_states) n).(msgs_received) R + num_trav =
              fold_left Nat.add (map (fun n' => (g.(node_states) n').(msgs_sent) R) all_nodes) O + num_inp) /\
      (forall R,
          if is_input R then
            forall n, (g.(node_states) n).(msgs_sent) R = 0
          else
            Existsn (fun f => exists args, f = normal_dfact R args) 0 g.(input_facts)).
            

  Definition meta_facts_correct_at_node rules ns :=
    forall R n args num,
      In (meta_dfact R (Some n) num) ns.(known_facts) ->
      can_learn_normal_fact_at_node rules ns R args ->
      In (normal_dfact R args) ns.(known_facts).

  Definition meta_facts_correct rules g :=
    forall n, meta_facts_correct_at_node (rules n) (g.(node_states) n).

  Lemma good_inputs_cons f fs :
    good_inputs (f :: fs) ->
    good_inputs fs.
  Proof.
    cbv [good_inputs]. simpl. intros [H1 H2]. invert H1. split; [assumption|].
    intros R num H. specialize (H2 R num ltac:(auto)). clear -H2.
    fwd. invert H2p1; eauto. eexists. split; [|eauto]. lia.
  Qed.
  
  Lemma good_inputs_unstep g g' :
    good_inputs g'.(input_facts) ->
    inp_step g g' ->
    good_inputs g.(input_facts).
  Proof.
    intros H1 H2. invert H2; simpl in *; eauto using good_inputs_cons.
  Qed.

  Lemma receive_fact_at_node_gets_more_facts f f' ns :
    In f ns.(known_facts) ->
    In f (receive_fact_at_node ns f').(known_facts).
  Proof.
    intros H. destruct f'; simpl; auto.
  Qed.
  Hint Resolve receive_fact_at_node_gets_more_facts : core.

  Lemma receive_fact_at_node_receives_facts f ns :
    In f (receive_fact_at_node ns f).(known_facts).
  Proof. destruct f; simpl; auto. Qed.
  
  Lemma step_preserves_facts rules f g g' :
    knows_fact g f ->
    comp_step rules g g' ->
    knows_fact g' f.
  Proof.
    intros Hg. invert 1.
    - destruct Hg as [Hg|Hg]; cbv [knows_fact]; simpl; eauto.
      fwd. right. exists n0. destr (node_eqb n n0); auto.
    - destruct Hg as [Hg|Hg]; cbv [knows_fact]; simpl; eauto.
      fwd. right. exists n0. destr (node_eqb n n0); auto.
  Qed.
  Hint Resolve step_preserves_facts : core.

  Lemma steps_preserves_facts rules f g g' :
    knows_fact g f ->
    (comp_step rules)^* g g' ->
    knows_fact g' f.
  Proof. induction 2; eauto. Qed.

  Lemma comp_step_pres_inputs rules g g':
    comp_step rules g g' ->
    g'.(input_facts) = g.(input_facts).
  Proof. invert 1; reflexivity. Qed.

  Lemma comp_steps_pres_inputs rules g g':
    (comp_step rules)^* g g' ->
    g'.(input_facts) = g.(input_facts).
  Proof. induction 1; eauto using eq_trans, comp_step_pres_inputs. Qed.

  Hint Unfold knows_fact : core.
  Lemma step_preserves_sanity rules g g' :
    sane_graph g ->
    comp_step rules g g' ->
    sane_graph g'.
  Proof.
    intros Hsane Hstep.
    destruct Hsane as (Hmfinp&Hmfnode&Htrav&Hcount).
    pose proof Hstep as Hstep'.
    invert Hstep; simpl in *.
  Admitted.

  Definition meta_facts_correct_at_node' rules ns :=
    forall R n num,
      In (meta_dfact R (Some n) num) ns.(known_facts) ->
      Forall (fun r =>
                match r with
                | normal_drule concls hyps =>
                    forall f' hyps',
                      rule_impl (normal_rule concls hyps) f' hyps' ->
                      Forall (fun c => expect_num_R_facts c.(fact_R) ns.(known_facts) (ns.(msgs_received) c.(fact_R))) hyps
                | _ => True
                end)
        rules.

  Definition meta_facts_correct' rules g :=
    forall n, meta_facts_correct_at_node' (rules n) (g.(node_states) n).
  
  From Datalog Require Import List.

  Lemma fold_left_add_repeat n m p :
    fold_left Nat.add (repeat n m) p = n * m + p.
  Proof.
    revert p. induction m; simpl; try lia.
    intros. rewrite IHm. lia.
  Qed.

  Lemma Existsn_unique U P n m (l : list U) :
    Existsn P n l ->
    Existsn P m l ->
    n = m.
  Proof.
    intros H. revert m. induction H; invert 1; auto.
    all: exfalso; auto.
  Qed.

  Lemma Existsn_0_Forall_not U P (l : list U) :
    Existsn P 0 l ->
    Forall (fun x => ~P x) l.
  Proof. induction l; invert 1; auto. Qed.
  
  Lemma expect_num_R_facts_no_travellers R g n args :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    expect_num_R_facts R (node_states g n).(known_facts)
                                             ((node_states g n).(msgs_received) R) ->
    In (n, normal_dfact R args) g.(travellers) ->
    False.
  Proof.
    intros Hs Hinp He Ht.
    cbv [sane_graph] in Hs. cbv [expect_num_R_facts] in He.
    destruct (is_input R) eqn:ER.
    - destruct Hs as (HmfNone&_&Htrav&_&_&Hcnt&Hinp_sane).
      specialize (Hcnt n R). fwd.
      cbv [good_inputs] in Hinp. destruct Hinp as (Hrel&Hinp_cnt).
      specialize (HmfNone _ _ ltac:(eauto)).
      rewrite Forall_forall in Hrel.
      specialize (Hrel _ HmfNone). simpl in Hrel.
      specialize (Hinp_sane R). rewrite Hrel in Hinp_sane.
      erewrite map_ext_in with (g := fun _ => 0) in Hcntp2 by auto.
      rewrite map_const in Hcntp2. rewrite fold_left_add_repeat in Hcntp2.
      replace (0 * length all_nodes + 0 + num_inp) with num_inp in Hcntp2 by lia.
      subst.
      specialize (Hinp_cnt _ _ HmfNone).
      fwd.
      epose proof Existsn_unique as Hu.
      specialize Hu with (1 := Hinp_cntp1) (2 := Hcntp1).
      subst.
      assert (num_trav = 0) by lia.
      subst.
      apply Existsn_0_Forall_not in Hcntp0.
      rewrite Forall_forall in Hcntp0.
      specialize (Hcntp0 _ Ht). simpl in Hcntp0. apply Hcntp0.
      eauto.
    - destruct Hs as (_&HmfSome&Htrav&Hmfcorrect&_&Hcnt&Hinp_sane).
      specialize (Hcnt n R). fwd.
      assert (Hem: expected_msgss = map (fun n' : Node => msgs_sent (node_states g n') R) all_nodes).
      { symmetry. apply Forall2_eq_eq.
        rewrite <- Forall2_map_l. eapply Forall2_impl; [|eassumption].
        simpl. intros n0 em Hn0.
        specialize (HmfSome _ _ _ ltac:(eauto)).
        specialize (Hmfcorrect _ _ _ ltac:(eassumption)).
        exact Hmfcorrect. }
      rewrite <- Hem in *. subst. clear Hep0.
      rewrite Hep1 in Hcntp2.
      assert (num_trav = num_inp) by lia.
      subst.
      specialize (Hinp_sane R). rewrite ER in Hinp_sane.
      epose proof Existsn_unique as Hu.
      specialize Hu with (1 := Hinp_sane) (2 := Hcntp1).
      subst.
      apply Existsn_0_Forall_not in Hcntp0.
      rewrite Forall_forall in Hcntp0.
      specialize (Hcntp0 _ Ht).
      simpl in Hcntp0.
      apply Hcntp0.
      eauto.
  Qed.
  
  Lemma step_preserves_mf_correct rules g g' :
    meta_facts_correct' rules g ->
    comp_step rules g g' ->
    meta_facts_correct' rules g'.
  Proof.
    intros Hmf. invert 1.
    - cbv [meta_facts_correct'] in *.
      intros n'. simpl.
      destr (node_eqb n n'); auto.
      destruct f; simpl.
      + specialize (Hmf n'). cbv [meta_facts_correct_at_node'] in *. simpl.
        intros R n num [H'|H']; [discriminate|].
        specialize Hmf with (1 := H').
        eapply Forall_impl; [|eassumption].
        simpl. intros r Hr. destruct r; auto.
        intros f' hyps' Hf'. specialize (Hr _ _ Hf').
        eapply Forall_impl; [|eassumption].
        simpl. intros c Hc. destr (rel_eqb nf_rel c.(fact_R)).
        2: { eapply expect_num_R_facts_incl; eauto with incl. }
        exfalso.
        eapply expect_num_R_facts_no_travellers.
        3: eassumption.
        Print sane_graph.

        intros Hcan. right.
        (*want that nf_rel is irrelevant...*)
        Print sane_graph. Print meta_facts_correct_at_node.
        cbv [can_learn_normal_fact_at_node] in Hcan.
        simpl in Hcan. fwd. destruct r; fwd.
  Abort.        

  Lemma steps_preserves_sanity rules g g' :
    sane_graph g ->
    (comp_step rules)^* g g' ->
    sane_graph g'.
  Proof.
    induction 2; eauto using step_preserves_sanity.
  Qed.

  Definition noncyclic_aggregation (p : list rule) :=
    well_founded (fun R1 R2 => exists Rs f, In R2 Rs /\ In (meta_rule R1 f Rs) p).

  Definition rel_edge (rules : Layout) R1 R2 :=
    exists n a, (*In R2 Rs /\*) In (*(meta_drule R1 Rs)*) (agg_drule a R2 R1) (rules n).

  Definition dnoncyclic_aggregation (rules : Layout) :=
    well_founded (rel_edge rules).
  
  (* Lemma meta_facts_stay_correct rules g g' R : *)
  (*   sane_graph g -> *)
  (*   graph_step rules g g' -> *)
  (*   meta_facts_correct_for g R -> *)
  (*   good_inputs g'.(input_facts) -> *)
  (*   dnoncyclic_aggregation rules -> *)
  (*   meta_facts_correct_for g' R. *)
  (* Proof. *)
  (*   intros Hsane Hstep Hmf Hinp Hnc. *)
  (*   specialize (Hsane ltac:(eauto using good_inputs_unstep)). *)
  (*   destruct Hsane as (Hmfinp&Hmfnode&Htrav&Hcount). *)
      
  Definition knows_datalog_fact g f :=
    match f with
    | normal_fact R args => knows_fact g (normal_dfact R args)
    | meta_fact R Rset =>
        (exists num, knows_fact g (meta_dfact R None num)) \/
          (forall n, exists num, knows_fact g (meta_dfact R (Some n) num))
    end.

  Lemma comp_step_preserves_datalog_facts rules f g g' :
    knows_datalog_fact g f ->
    comp_step rules g g' ->
    knows_datalog_fact g' f.
  Proof.
    intros Hknows Hstep. pose proof Hstep as Hstep'. invert Hstep'.
    - cbv [knows_datalog_fact]. destruct f; simpl.
      + destruct Hknows; fwd; eauto.
      + destruct Hknows as [Hknows|Hknows]; fwd; eauto.
        right. intros n'. specialize (Hknows n'). fwd. eauto.
    - cbv [knows_datalog_fact]. destruct f; simpl.
      + destruct Hknows; fwd; eauto.
      + destruct Hknows as [Hknows|Hknows]; fwd; eauto.
        right. intros n'. specialize (Hknows n'). fwd. eauto.
  Qed.
  
  Lemma comp_steps_preserves_datalog_facts rules f g g' :
    knows_datalog_fact g f ->
    (comp_step rules)^* g g' ->
    knows_datalog_fact g' f.
  Proof.
    induction 2; eauto using comp_step_preserves_datalog_facts.
  Qed.    
  
  Lemma node_can_receive_known_fact rules g f n :
    sane_graph g ->
    knows_fact g f ->
    exists g',
      (comp_step rules)^* g g' /\
        In f (g'.(node_states) n).(known_facts).
  Proof.
    intros Hs Hk. destruct Hs as (_&_&Heverywhere&_).
    apply Heverywhere with (n := n) in Hk. destruct Hk as [Hk|Hk].
    - apply in_split in Hk. fwd. eexists. split.
      { eapply Relations.TrcFront. 2: apply Relations.TrcRefl.
        apply ReceiveFact. eassumption. }
      simpl. destr (node_eqb n n); [|congruence].
      apply receive_fact_at_node_receives_facts.
    - exists g. split.
      { apply Relations.TrcRefl. }
      assumption.
  Qed.

  Lemma step_preserves_known_facts rules g g' n :
    comp_step rules g g' ->
    incl (g.(node_states) n).(known_facts) (g'.(node_states) n).(known_facts).
  Proof.
    invert 1; simpl.
    - destr (node_eqb n0 n); auto with incl.
      intros ? ?. apply receive_fact_at_node_gets_more_facts. assumption.
    - destr (node_eqb n0 n); auto with incl.
      intros ? ?. apply receive_fact_at_node_gets_more_facts. assumption.
  Qed.
  
  Lemma steps_preserves_known_facts rules g g' n :
    (comp_step rules)^* g g' ->
    incl (g.(node_states) n).(known_facts) (g'.(node_states) n).(known_facts).
  Proof.
    induction 1; auto with incl.
    eapply incl_tran; eauto using step_preserves_known_facts.
    About incl_tran. (*HWY would you call it that*)
  Qed.
    
  Hint Resolve TrcRefl TrcFront : core.
  Lemma node_can_receive_known_facts rules g hyps n :
    sane_graph g ->
    Forall (knows_fact g) hyps ->
    exists g',
      (comp_step rules)^* g g' /\
        Forall (fun f => In f (g'.(node_states) n).(known_facts)) hyps.
  Proof.
    intros Hs. induction 1.
    - eauto.
    - fwd. pose proof node_can_receive_known_fact as Hg'.
      specialize (Hg' rules g'). epose_dep Hg'.
      specialize (Hg' ltac:(eauto using steps_preserves_sanity) ltac:(eauto using steps_preserves_facts)).
      fwd.
      eexists. split.
      { eapply trc_trans; eassumption. }
      constructor; [eassumption|].
      eapply Forall_impl; [|eassumption].
      simpl. intros. eapply steps_preserves_known_facts; eauto.
  Qed.          

  Lemma node_can_receive_meta_facts g R rules S n :
    knows_datalog_fact g (meta_fact R S) ->
    exists g' num,
      (comp_step rules)^* g g' /\
        expect_num_R_facts R (g'.(node_states) n).(known_facts) num.
  Proof. Admitted.

  Lemma node_can_receive_expected_facts g R rules n num :
    expect_num_R_facts R (g.(node_states) n).(known_facts) num ->
    exists g',
      (comp_step rules)^* g g' /\
        (g'.(node_states) n).(msgs_received) R = num.
  Proof. Admitted.

  Lemma steps_preserves_meta_facts_correct rules g g' :
    (comp_step rules)^* g g' ->
    meta_facts_correct rules g ->
    meta_facts_correct rules g'.
  Proof. Admitted.

  Lemma node_can_expect g R rules S n :
    knows_datalog_fact g (meta_fact R S) ->
    exists g',
      (comp_step rules)^* g g' /\
        expect_num_R_facts R (g'.(node_states) n).(known_facts) ((g'.(node_states) n).(msgs_received) R).
  Proof.
    intros H. eapply node_can_receive_meta_facts in H. fwd.
    pose proof Hp1.
    eapply node_can_receive_expected_facts in Hp1. fwd.
    eexists. split; cycle 1.
    { eapply expect_num_R_facts_incl. 1: eassumption.
      eapply steps_preserves_known_facts. eassumption. }
    eauto using Relations.trc_trans.
  Qed.

  Lemma node_can_expect_much g Rs Ss rules n :
    length Rs = length Ss ->
    Forall (knows_datalog_fact g) (zip meta_fact Rs Ss) ->
    exists g',
      (comp_step rules)^* g g' /\
        Forall (fun R => expect_num_R_facts R (g'.(node_states) n).(known_facts) ((g'.(node_states) n).(msgs_received) R)) Rs.
  Proof.
    revert Ss. induction Rs; intros [|R ?] Hlen; simpl in Hlen;
      try discriminate; simpl; invert 1.
    - eauto.
    - specialize IHRs with (2 := H3). specialize (IHRs ltac:(lia)). fwd.
      rename H2 into HR. eapply comp_steps_preserves_datalog_facts in HR; [|eassumption].
      eapply node_can_expect in HR. fwd.
      eexists. split.
      { eapply Relations.trc_trans; eassumption. }
      constructor; eauto. eapply Forall_impl; [|eassumption].
      simpl. intros R' H'. eapply expect_num_R_facts_incl.
      { admit. }
      eapply steps_preserves_known_facts. eassumption.
  Admitted.

  Definition rel_of (f : fact) :=
    match f with
    | normal_fact R _ => R
    | meta_fact R _ => R
    end.
  
  (*oops this is the same as "facts_of" defined up above*)
  Definition fact_in_inputs inps f :=
    match f with
    | normal_fact R args => In (normal_dfact R args) inps
    | meta_fact R T =>
        exists num,
        In (meta_dfact R None num) inps /\
          Existsn (fun x => exists args, x = normal_dfact R args) num inps /\
          forall args, T args <-> In (normal_dfact R args) inps
    end.
  
  Definition graph_sound_for (p : list rule) rules g R :=
    forall g',
      (comp_step rules)^* g g' ->
      good_inputs g'.(input_facts) ->
      forall f,
        rel_of f = R ->
        knows_datalog_fact g' f ->
        prog_impl_implication p (fact_in_inputs g.(input_facts)) f.

  Definition graph_complete_for (p : list rule) (rules : Node -> list drule) (g : graph_state) (R : rel) :=
    forall f,
      prog_impl_implication p (fact_in_inputs g.(input_facts)) f ->
      exists g' f',
        (comp_step rules)^* g g' /\
          knows_datalog_fact g f'.

  Definition good_meta_rules (p : list rule) :=
    forall Q,
      (forall R' S',
          Q (meta_fact R' S') ->
          forall x,
            Q (normal_fact R' x) <-> S' x) ->
      (forall R S,
          prog_impl_implication p Q (meta_fact R S) ->
          forall x,
            prog_impl_implication p Q (normal_fact R x) <-> S x).

  Lemma firstn_plus {U} n m (l : list U) :
    firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
  Proof.
    revert l.
    induction n; intros l; simpl; [reflexivity|].
    destruct l.
    - rewrite firstn_nil. reflexivity.
    - simpl. f_equal. auto.
  Qed.

  (*requires some hypothesis about the source program: for each rule, for each assignment of facts to hypotheses, we get at most one fact as a conclusion*)
  Lemma node_can_find_all_conclusions rules Rs g n R :
    Forall
      (fun R =>
         expect_num_R_facts R (known_facts (g.(node_states) n))
           (msgs_received (node_states g n) R))
      Rs ->
    exists g',
      (comp_step rules)^* g g' /\
        Forall
          (fun R =>
             expect_num_R_facts R (known_facts (node_states g' n))
               (msgs_received (node_states g' n) R))
          Rs /\
        (forall args,
            can_learn_normal_fact_at_node (rules n) (node_states g' n) R args ->
            In (normal_dfact R args) (known_facts (node_states g' n))).
  Proof. Admitted.

  Lemma good_layout_complete' p r rules hyps g R f :
    good_inputs g.(input_facts) ->
    good_meta_rules p ->
    good_layout p rules ->
    sane_graph g ->
    meta_facts_correct rules g ->
    (forall R', rel_edge rules R' R -> graph_sound_for p rules g R') ->
    Forall (knows_datalog_fact g) hyps ->
    In r p ->
    rule_impl r f hyps ->
    rel_of f = R ->
     exists g',
       (comp_step rules)^* g g' /\
         knows_datalog_fact g' f.
  Proof.
    intros Hinp Hmr Hgood Hsane Hmf Hrels Hhyps Hr Himpl Hf. invert Himpl.
    - cbv [good_layout] in Hgood. destruct Hgood as (Hgood&_).
      apply Hgood in Hr. clear Hgood.
      destruct Hr as (n&Hr).
      
      edestruct node_can_receive_known_facts as (g1&Hstep1&Hhyps1).
      { eassumption. }
      { apply Forall_map with (f := fun '(R, args) => normal_dfact R args).
        rewrite Lists.List.Forall_map in Hhyps.
        eapply Forall_impl; [|exact Hhyps].
        simpl. intros [? ?]. simpl. intros H'. exact H'. }

      eenough (Hcan: can_learn_normal_fact_at_node (rules n) (node_states g1 n) R0 _).
      { pose proof (Classical_Prop.classic (exists num, In (meta_dfact R0 (Some n) num) (known_facts (node_states g1 n)))) as Hor.
        destruct Hor as [Hor|Hor].
        { fwd. exists g1. split; [eassumption|]. simpl. cbv [knows_fact].
          eapply steps_preserves_meta_facts_correct in Hmf; [|exact Hstep1].
          cbv [meta_facts_correct meta_facts_correct_at_node] in Hmf.
          specialize Hmf with (1 := Hor). eauto. }
          eexists. split.
          { (*first, step to a state where node n knows all the hypotheses;
              then, one final step where n deduces the conclusion*)
            eapply Relations.trc_trans.
            { exact Hstep1. }
            eapply Relations.TrcFront. 2: apply Relations.TrcRefl.
            apply LearnFact with (n := n) (f := normal_dfact R0 args).
            simpl. split.
            { eauto. }
            assumption. }
      simpl. cbv [knows_fact]. simpl. right. exists n.
      destr (node_eqb n n); [|congruence].
      simpl. left. reflexivity. }
      cbv [can_learn_normal_fact_at_node].
      eexists. split; [eassumption|]. simpl.
      do 2 eexists. split; [eassumption|]. split; [eassumption|].
      intros R' args' H'. rewrite Lists.List.Forall_map in Hhyps1.
      rewrite Forall_forall in Hhyps1. apply Hhyps1 in H'. exact H'.
    - cbv [good_layout] in Hgood. destruct Hgood as (_&Hgood&_).
      apply Hgood in Hr. clear Hgood.
      destruct Hr as (n&Hr).

      invert Hhyps. rename H2 into Hmhyp. rename H3 into Hhyps.
      
      edestruct node_can_receive_known_facts with (g := g) as (g1&Hg1&Hhyps1).
      { eassumption. }
      { eapply Forall_map.
        rewrite Lists.List.Forall_map in Hhyps.
        exact Hhyps. }

      pose proof Hmhyp as HS.
      eapply comp_steps_preserves_datalog_facts in Hmhyp; [|exact Hg1].
      eapply node_can_receive_meta_facts in Hmhyp.
      destruct Hmhyp as (g2&num&Hg2&Hnum).

      pose proof node_can_receive_expected_facts as Hrcv.
      Fail specialize Hrcv with (1 := Hnum). (*hmm*)
      epose_dep Hrcv. specialize (Hrcv Hnum). destruct Hrcv as (g3&Hg3&num').
      
      eenough (Hcan: can_learn_normal_fact_at_node (rules n) (node_states g3 n) _ _).
      { epose proof (Classical_Prop.classic (exists num, In (meta_dfact _ (Some n) num) (known_facts (node_states g3 n)))) as Hor.
        destruct Hor as [Hor|Hor].
        { fwd. exists g3. split; [eauto using Relations.trc_trans|]. simpl. cbv [knows_fact].
          eapply steps_preserves_meta_facts_correct with (g' := g3) in Hmf.
          2: { eauto using Relations.trc_trans. }
          cbv [meta_facts_correct meta_facts_correct_at_node] in Hmf.
          move Hmf at bottom. epose_dep Hmf. specialize (Hmf Hor).
          right. eexists. eapply Hmf. eauto. }
        eexists. split.
        { (*first, step to a state where node n knows all the hypotheses;
            then, one final step where n deduces the conclusion*)
          eapply Relations.trc_trans.
          { exact Hg1. }
          eapply Relations.trc_trans.
          { exact Hg2. }
          eapply Relations.trc_trans.
          { exact Hg3. }
          eapply Relations.TrcFront. 2: apply Relations.TrcRefl.
          eapply LearnFact with (n := n) (f := normal_dfact _ _).
          simpl. split.
          { eauto. }
          eassumption. }
        simpl. cbv [knows_fact]. simpl. right. exists n.
        destr (node_eqb n n); try congruence.
        simpl. auto. }
      cbv [can_learn_normal_fact_at_node].
      eexists. split; [eassumption|]. simpl.
      split.
      { subst. eapply expect_num_R_facts_incl; [eassumption|].
        eapply steps_preserves_known_facts. eassumption. }
      eexists. split; [|split; reflexivity].
      destruct H as (Hp1&Hp2). split. 2: exact Hp2.
      intros x. split; intros Hx.
      + (*this is where we use soundness*)
        apply Hp1.

        specialize (Hrels source_rel). simpl in Hrels. specialize' Hrels.
        { cbv [rel_edge]. eauto. }
        cbv [graph_sound_for] in Hrels. move Hrels at bottom.
        specialize (Hrels g3 ltac:(eauto using Relations.trc_trans)).
        specialize' Hrels.
        { repeat erewrite comp_steps_pres_inputs by eassumption. assumption. }
        pose proof Hrels as Hrels'.
        specialize (Hrels (normal_fact source_rel [x]) ltac:(reflexivity)).
        specialize' Hrels.
        { simpl. eauto. }
        specialize (Hrels' (meta_fact source_rel S) ltac:(reflexivity)).
        specialize' Hrels'.
        { eapply comp_steps_preserves_datalog_facts.
          1: eassumption. eauto using Relations.trc_trans. }
        (*should follow from Hrels plus Hrels'*)
        move Hmr at bottom.
        cbv [good_meta_rules] in Hmr. rewrite <- Hmr. 1,3: eassumption.
        simpl. intros R' S' H' x0. fwd.
        intros. symmetry. apply H'p2.
      + apply Lists.List.Forall_map in Hhyps1. rewrite Forall_forall in Hhyps1.
        specialize (Hhyps1 _ Hx). Search incl known_facts.
        eapply steps_preserves_known_facts. 2: eassumption.
        eauto using Relations.trc_trans.
    - destruct Hgood as (_&_&Hgood&_).
      specialize Hgood with (1 := Hr).
      cbv [knows_datalog_fact].
      enough (forall len,
               exists g' : graph_state,
                 Relations.trc (comp_step rules) g g' /\
                   (forall n : Node,
                       In n (firstn len all_nodes) ->
                       exists num : nat, knows_fact g' (meta_dfact target_rel (Some n) num))) as H'.
      { specialize (H' (length all_nodes)). rewrite firstn_all in H'. fwd.
        eexists. split;  eauto. right. intros n. apply H'p1.
        destruct Hall_nodes. auto. }
      intros len. induction len.
      { exists g. split; [apply Relations.TrcRefl|]. simpl. contradiction. }

      destruct IHlen as (g1&Hg1&Hhyps1).

      assert (firstn (S len) all_nodes = firstn len all_nodes \/
                exists n, firstn (S len) all_nodes = firstn len all_nodes ++ [n]) as [Hor|Hor].
      { replace (S len) with (len + 1) by lia. rewrite firstn_plus.
        destruct (skipn len all_nodes); simpl.
        - left. rewrite app_nil_r. reflexivity.
        - right. eauto. }

      { rewrite Hor. eauto. }

      destruct Hor as [n Hn].

      pose proof node_can_expect_much as Hg2.
      specialize Hg2 with (g := g1).
      epose_dep Hg2. specialize (Hg2 ltac:(eassumption)). specialize' Hg2.
      { eapply Forall_impl; [|eassumption].
        intros. eapply comp_steps_preserves_datalog_facts; eassumption. }
      destruct Hg2 as (g2&Hg2&Hhyps2).

      pose proof node_can_find_all_conclusions as Hg3.
      epose_dep Hg3. specialize (Hg3 Hhyps2). clear Hhyps2.
      destruct Hg3 as (g3&Hg3&Hhyps3a&Hhyps3b).
      
      eexists.
      split.
      { eapply Relations.trc_trans.
        { exact Hg1. }
        eapply Relations.trc_trans.
        { exact Hg2. }
        eapply Relations.trc_trans.
        { exact Hg3. }
        eapply Relations.TrcFront. 2: apply Relations.TrcRefl.
        eapply LearnFact with (f := meta_dfact target_rel (Some n) _).
        simpl. split; [reflexivity|]. cbv [can_learn_meta_fact_at_node].
        eexists. split.
        { apply Hgood. }
        simpl. split; [reflexivity|]. split.
        { apply Forall_forall. eassumption. }
        split.
        { eassumption. }
        reflexivity. }
      rewrite Hn. intros n' Hn'. rewrite in_app_iff in Hn'.
      destruct Hn' as [Hn'|Hn'].
      { apply Hhyps1 in Hn'. fwd. eexists.
        eapply steps_preserves_facts. 1: eassumption.
        { (*oops i already proved htis earlier*)
          eapply Relations.trc_trans.
        { exact Hg2. }
        eapply Relations.trc_trans.
        { exact Hg3. }
        eapply Relations.TrcFront. 2: apply Relations.TrcRefl.
        eapply LearnFact with (f := meta_dfact target_rel (Some n) _).
        simpl. split; [reflexivity|]. cbv [can_learn_meta_fact_at_node].
        eexists. split.
        { apply Hgood. }
        simpl. split; [reflexivity|]. split.
        { apply Forall_forall. eassumption. }
        split.
        { eassumption. }
        reflexivity.
        (*end repeated stuff*) } }
      destruct Hn' as [?|?]; [subst|contradiction].
      eexists. cbv [knows_fact]. simpl. right.
      exists n'. destr (node_eqb n' n'); [|congruence]. simpl. left. reflexivity.
  Qed.
    
  Lemma combine_fst_snd {A B} (l : list (A * B)) :
    l = combine (map fst l) (map snd l).
  Proof.
    induction l; simpl; f_equal; auto. destruct a; reflexivity.
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

  Print expect_num_R_facts.
  Lemma expect_num_R_facts_correct rules R p g n :
    good_inputs g.(input_facts) ->
    good_graph rules p g ->
    expect_num_R_facts R (g.(node_states) n).(known_facts) ((g.(node_states) n).(msgs_received) R) ->
    exists Rset,
      prog_impl_implication p (facts_of g.(input_facts)) (meta_fact R Rset) /\
        forall x,
          In (normal_dfact R [x]) (g.(node_states) n).(known_facts) <-> Rset [x]. (* prog_impl_implication p (facts_of g.(input_facts)) (normal_fact R [x]). *)
  Proof.
    intros Hinp (Hnorm&Hmetanode&Hmetainp&Hmnk&Hwires) [H|H].
    - assumption.
    - admit.
      Forall (knows_fact g)
    -
  Abort.
    
  
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
                  cbv [expect_num_R_facts] in Hp1p0.

                  
                  
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
