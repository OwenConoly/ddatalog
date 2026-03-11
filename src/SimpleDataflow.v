From Stdlib Require Import List Bool.
From Datalog Require Import Datalog Tactics.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.
From Stdlib Require Import Lia.
From Datalog Require Import List.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Permutation.

Notation "R ^*" := (clos_refl_trans_1n _ R) (format "R ^*").
Hint Constructors clos_refl_trans_1n : core.
Lemma crt1n_transitive A R (x y z : A) :
  R^* x y ->
  R^* y z ->
  R^* x z.
Proof. induction 1; eauto. Qed.

Import ListNotations.

Section DistributedDatalog.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map var T}.
  Context {context_ok : map.ok context}.
  Context {Node Info : Type}.
  Context (a_node : Node).
  Context (all_nodes : list Node).
  Context (Hall_nodes : is_list_set (fun _ => True) all_nodes).
  Context {node_eqb : Node -> Node -> bool}.
  Context {node_eqb_spec : EqDecider node_eqb}.
  Context (is_input : rel -> bool).
  Context {rel_eqb : rel -> rel -> bool}.
  Context {rel_eqb_spec : EqDecider rel_eqb}.

  Inductive dfact :=
  | normal_dfact (nf_rel: rel) (nf_args: list T)
  | meta_dfact (mf_rel: rel) (source: option Node) (expected_msgs: nat) (*number of messages that node "source" will ever send about mf_rel*).

  Let clause := clause rel var fn.
  Let rule := rule rel var fn aggregator T.
  Let fact := fact rel T.

  Definition good_rule_inputs (r : rule) :=
    match r with
    | normal_rule cs _ => Forall (fun R => is_input R = false) (map fact_R cs)
    | agg_rule _ target_rel _ => is_input target_rel = false
    | meta_rule R _ _ => is_input R = false
    end.

  Definition good_layout (p : list rule) (rules : Node -> list rule) :=
    (forall r, In r p -> exists n, In r (rules n)) /\
      (forall r n, In r (rules n) -> In r p) /\
      (forall target_rel target_set source_rels n,
          In (meta_rule target_rel target_set source_rels) p ->
          In (meta_rule target_rel target_set source_rels) (rules n)).

  Definition consistent (p : list rule) Q R S0 :=
    forall x,
      prog_impl_implication p Q (normal_fact R x) <-> S0 x.

  Definition rule_impl_implication (r : rule) Q f :=
    exists hyps,
      rule_impl r f hyps /\ Forall Q hyps.

  Definition good_meta_rule (p : list rule) r :=
    forall Q R0 S0,
      rule_impl_implication r
        (fun f =>
           match f with
           | normal_fact _ _ => False
           | meta_fact R' S' => consistent p Q R' S'
           end)
        (meta_fact R0 S0) ->
      forall x,
        prog_impl_implication p Q (normal_fact R0 x) <-> Q (normal_fact R0 x) \/ S0 x
  (*consistent p Q R0 S0*).

  Context (p : list rule) (rules : Node -> list rule).
  Context (Hp_inp : Forall good_rule_inputs p) (Hlayout : good_layout p rules) (Hgmr : Forall (good_meta_rule p) p).

  (*i assume graph is complete, because i suspect this will be tricky enough as is*)
  Record node_state := {
      known_facts: list dfact;
      (*how many messages have i received about this relation*)
      msgs_received: rel -> nat;
      (*how many messages have i sent about this relation*)
      msgs_sent: rel -> nat;
    }.

  Record graph_state := {
      node_states : Node -> node_state;
      (*if (n, f) is in this list, then fact f has been sent to node n but has not yet been received*)
      travellers : list (Node * dfact);
      (*inputs that have been received so far*)
      input_facts : list dfact;
    }.

  Definition expect_num_R_facts R known_facts num :=
    if is_input R then
      In (meta_dfact R None num) known_facts
    else
      exists expected_msgss,
        Forall2 (fun n expected_msgs => In (meta_dfact R (Some n) expected_msgs) known_facts) all_nodes expected_msgss /\
          num = fold_left Nat.add expected_msgss O.

  Lemma expect_num_R_facts_relevant_mfs_incl R kf1 kf2 num :
    expect_num_R_facts R kf1 num ->
    (forall n num,
        In (meta_dfact R n num) kf1 ->
        In (meta_dfact R n num) kf2) ->
    expect_num_R_facts R kf2 num.
  Proof.
    intros H Hincl. cbv [expect_num_R_facts] in *.
    destruct (is_input R); auto.
    fwd. eexists. split; eauto.
    eapply Forall2_impl; [|eassumption].
    simpl. auto.
  Qed.

  Lemma expect_num_R_facts_incl R kf1 kf2 num :
    expect_num_R_facts R kf1 num ->
    incl kf1 kf2 ->
    expect_num_R_facts R kf2 num.
  Proof. eauto using expect_num_R_facts_relevant_mfs_incl. Qed.

  Definition can_learn_normal_fact_at_node' P (rules : list rule) ns R args :=
    exists r, In r rules /\
    match r with
    | normal_rule rule_concls rule_hyps =>
        exists ctx hyps',
        Exists (fun c => interp_clause ctx c (R, args)) rule_concls /\
          Forall2 (interp_clause ctx) rule_hyps hyps' /\
          (forall R0 args0, In (R0, args0) hyps' ->
                       P R0 /\
                         In (normal_dfact R0 args0) ns.(known_facts))
    | agg_rule rule_agg target_rel source_rel =>
        P source_rel /\
          expect_num_R_facts source_rel ns.(known_facts) (ns.(msgs_received) source_rel) /\
          exists vals,
            (is_list_set (fun x => In (normal_dfact source_rel [x]) ns.(known_facts)) vals) /\
              R = target_rel /\
              args = [fold_right (interp_agg rule_agg) (agg_id rule_agg) vals]
    | meta_rule _ _ _ => False
    end.

  Definition can_learn_normal_fact_at_node := can_learn_normal_fact_at_node' (fun _ => True).

  Definition can_learn_meta_fact_at_node rules ns R expected_msgs :=
    exists r, In r rules /\
    match r with
    | normal_rule _ _ => False
    | agg_rule _ _ _ => False
    | meta_rule R0 _ R's =>
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

  Definition learn_fact_at_node ns f :=
    match f with
    | normal_dfact R args =>
        {| known_facts := f :: ns.(known_facts);
          msgs_received := ns.(msgs_received);
          msgs_sent := fun R' => if rel_eqb R R' then
                                S (ns.(msgs_sent) R)
                              else ns.(msgs_sent) R' |}
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

  Inductive comp_step : graph_state -> graph_state -> Prop :=
  | ReceiveFact g n f fs1 fs2 :
    g.(travellers) = fs1 ++ (n, f) :: fs2 ->
    comp_step
      g
      {| node_states := fun n' => if node_eqb n n' then
                                 receive_fact_at_node (g.(node_states) n) f
                               else g.(node_states) n';
        travellers := fs1 ++ fs2;
        input_facts := g.(input_facts); |}
  | LearnFact g n f :
    should_learn_fact_at_node (rules n) n (g.(node_states) n) f ->
    comp_step
      g
      {| node_states := fun n' => if node_eqb n n' then
                                 learn_fact_at_node (g.(node_states) n) f
                               else g.(node_states) n';
        travellers := map (fun n => (n, f)) all_nodes ++ g.(travellers);
        input_facts := g.(input_facts) |}.

  Definition knows_fact (g : graph_state) f : Prop :=
    In f g.(input_facts) \/
      exists n, In f (g.(node_states) n).(known_facts).

  (*this definition is kind of ugly*)
  Definition good_inputs (inputs : list dfact) :=
    Forall (fun f => is_input_fact f = true) inputs /\
      (forall R num,
          In (meta_dfact R None num) inputs ->
          (forall num0, In (meta_dfact R None num0) inputs -> num0 = num) /\
            exists num',
              num' <= num /\
                Existsn (fun f => exists args, f = normal_dfact R args) num' inputs).

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
            (forall n, (g.(node_states) n).(msgs_sent) R = 0) /\
              (forall n num, ~knows_fact g (meta_dfact R (Some n) num))
          else
            Existsn (fun f => exists args, f = normal_dfact R args) 0 g.(input_facts)).

  Lemma good_inputs_cons f fs :
    good_inputs (f :: fs) ->
    good_inputs fs.
  Proof.
    cbv [good_inputs]. simpl. intros [H1 H2]. invert H1. split; [assumption|].
    intros R num H. specialize (H2 R num ltac:(auto)). clear -H2.
    fwd. invert H2p1p1; split; eauto. eexists. split; [|eauto]. lia.
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

  Lemma learn_fact_at_node_gets_more_facts f f' ns :
    In f ns.(known_facts) ->
    In f (learn_fact_at_node ns f').(known_facts).
  Proof.
    intros H. destruct f'; simpl; auto.
  Qed.
  Hint Resolve learn_fact_at_node_gets_more_facts : core.

  Lemma receive_fact_at_node_receives_facts f ns :
    In f (receive_fact_at_node ns f).(known_facts).
  Proof. destruct f; simpl; auto. Qed.

  Lemma learn_fact_at_node_learns_facts f ns :
    In f (receive_fact_at_node ns f).(known_facts).
  Proof. destruct f; simpl; auto. Qed.

  Lemma step_preserves_facts f g g' :
    knows_fact g f ->
    comp_step g g' ->
    knows_fact g' f.
  Proof.
    intros Hg. invert 1.
    - destruct Hg as [Hg|Hg]; cbv [knows_fact]; simpl; eauto.
      fwd. right. exists n0. destr (node_eqb n n0); auto.
    - destruct Hg as [Hg|Hg]; cbv [knows_fact]; simpl; eauto.
      fwd. right. exists n0. destr (node_eqb n n0); auto.
  Qed.
  Hint Resolve step_preserves_facts : core.

  Lemma steps_preserves_facts f g g' :
    knows_fact g f ->
    comp_step^* g g' ->
    knows_fact g' f.
  Proof. induction 2; eauto. Qed.

  Lemma comp_step_pres_inputs g g':
    comp_step g g' ->
    g'.(input_facts) = g.(input_facts).
  Proof. invert 1; reflexivity. Qed.

  Lemma comp_steps_pres_inputs g g':
    comp_step^* g g' ->
    g'.(input_facts) = g.(input_facts).
  Proof. induction 1; eauto using eq_trans, comp_step_pres_inputs. Qed.

  Ltac solve_in_travellers :=
    match goal with
    | Htrav : forall (n : Node) (f : dfact), In (n, f) (travellers _) -> knows_fact _ f, H: travellers _ = _ |- _
  =>
    repeat match goal with
      | H: In _ (_ ++ _) |- _ => apply in_app_iff in H; destruct H
      end;
    solve [eapply Htrav; rewrite H; apply in_app_iff; simpl; eauto]
  end.

  Ltac t := repeat match goal with
              | _ => progress (intros; simpl in *; subst )
              | H: meta_dfact _ _ _ = normal_dfact _ _ |- _ => discriminate H
              | H: normal_dfact _ _ = meta_dfact _ _ _ |- _ => discriminate H
              | _ => solve[eauto]
              | H: knows_fact _ _ |- _ => destruct H
              (* | H: exists _, _ |- _ => destruct H *)
              (* | H: _ /\ _ |- _ => destruct H *)
              | _ => progress fwd (*slow, would be nice to replace by lines above*)
              | H: context[node_eqb ?x ?y] |- _ => destr (node_eqb x y); try congruence
              | |- context[node_eqb ?x ?y] => destr (node_eqb x y); try congruence
              | H: context[rel_eqb ?x ?y] |- _ => destr (rel_eqb x y); try congruence
              | |- context[rel_eqb ?x ?y] => destr (rel_eqb x y); try congruence
              | H: context[receive_fact_at_node _ ?f] |- _ => destruct f
              | H: context[learn_fact_at_node _ ?f] |- _ => destruct f
              | H: _ \/ _ |- _ => destruct H
              | _ => solve_in_travellers
              | _ => congruence
              | _ => solve[eauto 6]
              end.

  Lemma all_nodes_split n :
    exists l1 l2,
      all_nodes = l1 ++ n :: l2 /\
        ~In n l1 /\ ~In n l2.
  Proof.
    destruct Hall_nodes as [H1 H2]. specialize (H1 n). pose proof (H1' := I).
    apply H1 in H1'. apply in_split in H1'. fwd. do 2 eexists. split; [reflexivity|].
    apply NoDup_remove_2 in H2. rewrite in_app_iff in H2. auto.
  Qed.

  Lemma fold_left_add_from_0 l n :
    fold_left Nat.add l n = fold_left Nat.add l 0 + n.
  Proof.
    revert n.
    induction l as [|a ?]; simpl; auto.
    intros. rewrite (IHl a), (IHl (_ + a)). lia.
  Qed.

  Hint Unfold knows_fact : core.
  Lemma step_preserves_sanity g g' :
    sane_graph g ->
    comp_step g g' ->
    sane_graph g'.
  Proof.
    intros Hsane Hstep.
    destruct Hsane as (Hmfinp&Hmfnode&Htrav&Hmfcorrect&Heverywhere&Hcount&Hinp_sane).
    pose proof Hstep as Hstep'.
    invert Hstep; simpl in *.
    - cbv [sane_graph]. simpl. ssplit.
      + t.
        { apply Hmfinp. solve_in_travellers. }
      + t.
        { apply Hmfnode. solve_in_travellers. }
      + t.
        { eapply step_preserves_facts; [|eassumption]. solve_in_travellers. }
        { eapply step_preserves_facts; [|eassumption]. solve_in_travellers. }
      + t.
        { apply Hmfcorrect. apply Hmfnode. solve_in_travellers. }
      + intros f0 Hf0 n0.
        move Heverywhere at bottom.
        specialize (Heverywhere f0).
        specialize' Heverywhere.
        { t. }
        specialize (Heverywhere n0). destruct Heverywhere as [He|He].
        -- rewrite H in He. apply in_app_iff in He. simpl in He.
           rewrite in_app_iff.
           destruct He as [He|[He|He]]; auto.
           invert He.
           t.
        -- t.
      + intros n' R. specialize (Hcount n' R). fwd. move Hcountp0 at bottom.
        rewrite H in Hcountp0. eapply Existsn_perm in Hcountp0.
        2: { apply Permutation_sym. apply Permutation_middle. }
        pose proof (all_nodes_split n) as H'. fwd. rewrite H'p0 in *. clear H'p0.
        rewrite map_app in *. simpl in *. destr (node_eqb n n); [|congruence].
        rewrite fold_left_app in *. simpl in *.
        eassert (map _ l1 = map _ l1) as ->.
        { apply map_ext_in. intros n0 Hn0. destr (node_eqb n n0); [exfalso; auto|].
          reflexivity. }
        eassert (map _ l2 = map _ l2) as ->.
        { apply map_ext_in. intros n0 Hn0. destr (node_eqb n n0); [exfalso; auto|].
          reflexivity. }
        rewrite (fold_left_add_from_0 _ (_ + _)).
        rewrite (fold_left_add_from_0 _ (_ + _)) in Hcountp2.
        move Hcountp2 at bottom.
        invert Hcountp0.
        -- do 2 eexists. split; [eassumption|]. split; [eassumption|].
           destr (node_eqb n n').
           ++ cbv [receive_fact_at_node]. destruct f; simpl.
              --- destr (rel_eqb nf_rel R); [exfalso; eauto|]. assumption.
              --- assumption.
           ++ cbv [receive_fact_at_node]. destruct f; assumption.
        -- do 2 eexists. split; [eassumption|]. split; [eassumption|]. fwd.
           destr (node_eqb n n); [|congruence].
           cbv [receive_fact_at_node]. simpl.
           destr (rel_eqb R R); [|congruence].
           lia.
      + intros R. specialize (Hinp_sane R). destruct (is_input R).
        -- split; [t|]. intros. intros ?. fwd. eapply Hinp_sanep1. t.
        -- t.
    - cbv [sane_graph]. simpl. ssplit.
      + t.
      + t.
      + t.
        { rename H0 into Hnf. apply in_app_iff in Hnf. destruct Hnf as [Hnf|Hnf].
          - apply in_map_iff in Hnf. fwd. right. exists n. t.
          - t. }
        { rename H0 into Hnf. apply in_app_iff in Hnf. destruct Hnf as [Hnf|Hnf].
          - apply in_map_iff in Hnf. fwd. right. exists n. t.
          - t. }
      + t.
        -- exfalso. intuition eauto.
        -- cbv [can_learn_meta_fact_at_node] in *. fwd. reflexivity.
      + intros f0 Hf0 n0.
        assert (f0 = f \/ knows_fact g f0) as [?|?] by t.
        { subst. left. apply in_app_iff. left. apply in_map_iff.
          destruct Hall_nodes as [H'1 H'2]. eexists. split; eauto. apply H'1. auto. }
        specialize (Heverywhere _ ltac:(eassumption)).
        specialize (Heverywhere n0). destruct Heverywhere as [He|He].
        -- rewrite in_app_iff. eauto.
        -- t.
      + intros n' R. specialize (Hcount n' R). fwd.
        pose proof (all_nodes_split n) as H'. fwd. rewrite H'p0 in *. clear H'p0.
        rewrite (map_app (fun _ => msgs_sent _ _)).
        rewrite (map_app (fun _ => msgs_sent _ _)) in Hcountp2.
        simpl in *.
        destr (node_eqb n n); [|congruence].
        rewrite fold_left_app in *. simpl in *.
        eassert (map _ l1 = map _ l1) as ->.
        { apply map_ext_in. intros n0 Hn0. destr (node_eqb n n0); [exfalso; auto|].
          reflexivity. }
        eassert (map _ l2 = map _ l2) as ->.
        { apply map_ext_in. intros n0 Hn0. destr (node_eqb n n0); [exfalso; auto|].
          reflexivity. }
        rewrite (fold_left_add_from_0 _ (_ + _)).
        rewrite (fold_left_add_from_0 _ (_ + _)) in Hcountp2.
        destruct f; simpl in *.
        -- destr (rel_eqb nf_rel R).
           ++ do 2 eexists. split.
              { apply Existsn_app.
                - apply Existsn_map. eapply Existsn_iff.
                  { eapply list_set_Existsn_1 with (x := n'). 1: eassumption. constructor. }
                  intros. split; intros; fwd; eauto.
                - eassumption. }
              split; [eassumption|].
              destr (node_eqb n n'); simpl; lia.
           ++ do 2 eexists. split.
              { apply Existsn_app.
                - apply Existsn_map. apply Forall_not_Existsn_0. apply Forall_app. split.
                  + apply Forall_forall. intros ? ? ?. fwd. congruence.
                  + constructor.
                    -- intros ?. fwd. congruence.
                    -- apply Forall_forall. intros ? ? ?. fwd. congruence.
                - eassumption. }
              split; [eassumption|].
              destr (node_eqb n n'); simpl; assumption.
        -- do 2 eexists. split.
              { apply Existsn_app.
                - apply Existsn_map. apply Forall_not_Existsn_0. apply Forall_app. split.
                  + apply Forall_forall. intros ? ? ?. fwd. congruence.
                  + constructor.
                    -- intros ?. fwd. congruence.
                    -- apply Forall_forall. intros ? ? ?. fwd. congruence.
                - eassumption. }
              split; [eassumption|].
              destr (node_eqb n n'); simpl; assumption.
      + intros R. specialize (Hinp_sane R). pose proof Hp_inp as Hr.
        rewrite Forall_forall in Hr.
        destruct (is_input R) eqn:ER; t.
        2: { split; t. intros ?. eapply Hinp_sanep1. t.
             cbv [can_learn_meta_fact_at_node] in Hp1. fwd.
             epose_dep Hr. specialize' Hr.
             { destruct Hlayout as [_ [Hl _]]. eapply Hl. eassumption. }
             simpl in Hr. congruence. }
        split; t.
        2: { intros ?. eapply Hinp_sanep1. t. }
        exfalso.
        cbv [can_learn_normal_fact_at_node can_learn_normal_fact_at_node'] in Hp1.
        fwd. epose_dep Hr. specialize' Hr.
        { destruct Hlayout as [_ [Hl _]]. eapply Hl. eassumption. }
        destruct r; fwd.
        -- simpl in Hr. apply Lists.List.Forall_map in Hr. rewrite Forall_forall in Hr.
           apply Exists_exists in Hp1p1p0. fwd. specialize (Hr _ ltac:(eassumption)).
           invert Hp1p1p0p1. congruence.
        -- congruence.
        -- contradiction.
  Qed.

  Definition meta_facts_correct_at_node (rules : list rule) n ns :=
    forall R num,
      In (meta_dfact R (Some n) num) ns.(known_facts) ->
      exists f Rs,
        In (meta_rule R f Rs) rules /\
          ~In R Rs /\
          Forall (fun R' => expect_num_R_facts R' ns.(known_facts) (ns.(msgs_received) R')) Rs /\
          (forall args,
              can_learn_normal_fact_at_node' (fun R' => In R' Rs) rules ns R args ->
              In (normal_dfact R args) (known_facts ns)).

  Definition meta_facts_correct rules g :=
    forall n, meta_facts_correct_at_node (rules n) n (g.(node_states) n).

  Lemma fold_left_add_repeat n m q :
    fold_left Nat.add (repeat n m) q = n * m + q.
  Proof.
    revert q. induction m; simpl; try lia.
    intros. rewrite IHm. lia.
  Qed.

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
      specialize (Hinp_sane R). rewrite Hrel in Hinp_sane. fwd.
      erewrite map_ext_in with (g := fun _ => 0) in Hcntp2 by auto.
      rewrite map_const in Hcntp2. rewrite fold_left_add_repeat in Hcntp2.
      replace (0 * length all_nodes + 0 + num_inp) with num_inp in Hcntp2 by lia.
      subst.
      specialize (Hinp_cnt _ _ HmfNone).
      fwd.
      epose proof Existsn_unique as Hu.
      specialize Hu with (1 := Hinp_cntp1p1) (2 := Hcntp1).
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

  Lemma expect_num_R_facts_msgs_received_stable_step g R n g' :
    sane_graph g ->
    good_inputs (input_facts g) ->
    expect_num_R_facts R
      (node_states g n).(known_facts)
                          ((g.(node_states) n).(msgs_received) R) ->
    comp_step g g' ->
    (g'.(node_states) n).(msgs_received) R = (g.(node_states) n).(msgs_received) R.
  Proof.
    intros Hs Hinp He Hstep. invert Hstep; simpl.
    - destr (node_eqb n0 n); [|reflexivity].
      cbv [receive_fact_at_node]. destruct f; [|reflexivity].
      simpl. destr (rel_eqb nf_rel R); [|reflexivity].
      exfalso.
      eapply expect_num_R_facts_no_travellers; eauto.
      rewrite H. apply in_app_iff. simpl. eauto.
    - destr (node_eqb n0 n); [|reflexivity].
      cbv [learn_fact_at_node]. destruct f; reflexivity.
  Qed.

  Lemma steps_preserves_sanity g g' :
    sane_graph g ->
    comp_step^* g g' ->
    sane_graph g'.
  Proof.
    induction 2; eauto using step_preserves_sanity.
  Qed.

  Lemma step_preserves_known_facts g g' n :
    comp_step g g' ->
    incl (g.(node_states) n).(known_facts) (g'.(node_states) n).(known_facts).
  Proof.
    invert 1; simpl.
    - destr (node_eqb n0 n); auto with incl.
      intros ? ?. apply receive_fact_at_node_gets_more_facts. assumption.
    - destr (node_eqb n0 n); auto with incl.
      intros ? ?. apply learn_fact_at_node_gets_more_facts. assumption.
  Qed.

  Lemma expect_num_R_facts_msgs_received_stable_steps g R n g' :
    sane_graph g ->
    good_inputs (input_facts g) ->
    expect_num_R_facts R
      (node_states g n).(known_facts)
                          ((g.(node_states) n).(msgs_received) R) ->
    comp_step^* g g' ->
    (g'.(node_states) n).(msgs_received) R = (g.(node_states) n).(msgs_received) R.
  Proof.
    induction 4.
    - reflexivity.
    - rewrite IHclos_refl_trans_1n.
      + eapply expect_num_R_facts_msgs_received_stable_step; eassumption.
      + eauto using steps_preserves_sanity.
      + erewrite comp_steps_pres_inputs by (eapply rt1n_trans; eauto). assumption.
      + erewrite expect_num_R_facts_msgs_received_stable_step by eassumption.
        eapply expect_num_R_facts_incl.
        -- eassumption.
        -- eapply step_preserves_known_facts. eassumption.
  Qed.

  Lemma reasonable_meta_fact_nodes g R n num :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    knows_fact g (meta_dfact R n num) ->
    if is_input R then n = None
    else exists n0, n = Some n0.
  Proof.
    intros Hs Hinp Hf. destruct Hs as (HmfNone&_&_&_&_&_&Hinp_sane).
    specialize (Hinp_sane R).
    destruct (is_input R) eqn:E.
    - fwd. destruct n; auto. exfalso. intuition eauto.
    - destruct n; eauto. exfalso. apply HmfNone in Hf.
      destruct Hinp as (Hinp&_). rewrite Forall_forall in Hinp. apply Hinp in Hf.
      simpl in Hf. congruence.
  Qed.

  Lemma mfs_unique g R n num1 num2 :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    knows_fact g (meta_dfact R n num1) ->
    knows_fact g (meta_dfact R n num2) ->
    num1 = num2.
  Proof.
    intros Hs Hinp H1 H2. destruct Hs as (HmfNone&HmfSome&_&Hmfcorrect&_).
    destruct n.
    - apply HmfSome in H1, H2. apply Hmfcorrect in H1, H2. subst. reflexivity.
    - apply HmfNone in H1, H2. cbv [good_inputs] in Hinp. destruct Hinp as (_&Hinp).
      apply Hinp in H1. fwd. apply H1p0 in H2. subst. reflexivity.
  Qed.

  Definition rel_ofd f :=
    match f with
    | normal_dfact R _ => R
    | meta_dfact R _ _ => R
    end.

  (*TODO remove this, should be imported from datalog/src/List*)
  Lemma is_list_set_ext X (S1 S2 : X -> _) l :
    is_list_set S1 l ->
    (forall x, S1 x <-> S2 x) ->
    is_list_set S2 l.
  Proof.
    intros [H1 H2] H3. split; auto. intros. rewrite <- H3. apply H1.
  Qed.

  Lemma can_learn_normal_fact_at_node'_incl P rules0 ns ns' R args :
    can_learn_normal_fact_at_node' P rules0 ns R args ->
    (forall f, P (rel_ofd f) -> In f ns'.(known_facts) <-> In f ns.(known_facts)) ->
    (forall R', P R' -> ns'.(msgs_received) R' = ns.(msgs_received) R') ->
    can_learn_normal_fact_at_node' P rules0 ns' R args.
  Proof.
    intros H Hfs Hmsgs. cbv [can_learn_normal_fact_at_node'] in *. fwd.
    eexists. split; [eassumption|].
    destruct r; fwd.
    - do 2 eexists. split; [eassumption|]. split; [eassumption|].
      intros R0 args0 H0. specialize (Hp1p2 _ _ ltac:(eassumption)). fwd.
      split; [assumption|]. apply Hfs; auto.
    - split; [assumption|]. split.
      { rewrite Hmsgs by assumption.
        eapply expect_num_R_facts_relevant_mfs_incl; [eassumption|].
        intros. apply Hfs; auto. }
      eexists. split; eauto. eapply is_list_set_ext; [eassumption|]. simpl.
      intros. symmetry. apply Hfs. simpl. assumption.
    - assumption.
  Qed.

  Lemma can_learn_normal_fact_at_node'_weaken P1 P2 rules0 ns R args :
    can_learn_normal_fact_at_node' P1 rules0 ns R args ->
    (forall R', P1 R' -> P2 R') ->
    can_learn_normal_fact_at_node' P2 rules0 ns R args.
  Proof.
    cbv [can_learn_normal_fact_at_node']. intros H HP. fwd.
    eexists. split; [eassumption|]. destruct r; fwd.
    - do 2 eexists. split; [eassumption|]. split; [eassumption|].
      intros R0 args0 H0. apply Hp1p2 in H0. fwd. eauto.
    - eauto 7.
    - assumption.
  Qed.

  Definition knows_datalog_fact g f :=
    match f with
    | normal_fact R args => knows_fact g (normal_dfact R args)
    | meta_fact R Rset =>
        if is_input R then
          exists num, knows_fact g (meta_dfact R None num) /\
                   Existsn (fun f => exists args, f = normal_dfact R args) num g.(input_facts)
        else
          forall n, exists num, knows_fact g (meta_dfact R (Some n) num)
    end.

  Lemma something_about_expect_num_R_facts R S g n :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    expect_num_R_facts R (g.(node_states) n).(known_facts)
      ((g.(node_states) n).(msgs_received) R) ->
    knows_datalog_fact g (meta_fact R S).
  Proof.
    intros Hsane Hinp H.
    destruct Hsane as (HmfNone&_&_&_&_&Hcnt&Hinp_sane).
    move Hcnt at bottom. move Hinp_sane at bottom.
    specialize (Hcnt n R). specialize (Hinp_sane R).
    simpl. cbv [expect_num_R_facts] in H. destruct (is_input R).
    --- eexists. split; [eauto|]. fwd. erewrite map_ext in Hcntp2.
        2: { intros. apply Hinp_sanep0. }
        rewrite map_const in Hcntp2. rewrite fold_left_add_repeat in Hcntp2.
        move Hinp at bottom. destruct Hinp as (_&Hinp). epose_dep Hinp.
        specialize' Hinp.
        { apply HmfNone. eauto. }
        destruct Hinp as (_&Hinp). fwd.
        eapply Existsn_unique in Hinpp1; [|exact Hcntp1]. subst.
        assert (num' = (g.(node_states) n).(msgs_received) R) by lia.
        subst. assumption.
    --- move H at bottom. fwd. intros n'.
        apply Forall2_forget_r in Hp0. move Hall_nodes at bottom.
        destruct Hall_nodes as (H'&_). rewrite Forall_forall in Hp0.
        specialize (Hp0 n'). specialize' Hp0.
        { apply H'. constructor. }
        fwd. eauto.
  Qed.

  Lemma expect_num_R_facts_knows_everything g n R args :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    expect_num_R_facts R (g.(node_states) n).(known_facts)
                                               ((g.(node_states) n).(msgs_received) R) ->
    knows_fact g (normal_dfact R args) ->
    In (normal_dfact R args) (g.(node_states) n).(known_facts).
  Proof.
    intros Hsane Hinp HR Hargs.
    pose proof expect_num_R_facts_no_travellers as H'.
    epose_dep H'. specialize (H' ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    destruct Hsane as (_&_&_&_&Heverywhere&_).
    specialize (Heverywhere _ ltac:(eassumption)).
    edestruct Heverywhere; [|eassumption].
    exfalso. eauto.
  Qed.

  Lemma expect_num_R_facts_knows_meta_facts g n R source num :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    expect_num_R_facts R (g.(node_states) n).(known_facts)
                                               ((g.(node_states) n).(msgs_received) R) ->
    knows_fact g (meta_dfact R source num) ->
    In (meta_dfact R source num) (g.(node_states) n).(known_facts).
  Proof.
    intros Hs Hinp H Hf. cbv [expect_num_R_facts] in H. Print sane_graph.
    pose proof Hs as Hs'.
    destruct Hs' as (HmfNone&_&_&Hmfcnt&_&_&Hs'). specialize (Hs' R).
    destruct (is_input R) eqn:E; fwd.
    - destruct source.
      { exfalso. intuition eauto. }
      pose proof mfs_unique as Huniq.
      epose_dep Huniq. specialize (Huniq ltac:(eassumption) ltac:(eassumption)).
      specialize' Huniq.
      { clear -H. (*why did taht do nothing*) clear Hf. eauto. }
      specialize' Huniq.
      { clear -Hf. (*why*) clear H. eauto. }
      subst. assumption.
    - destruct source.
      2: { exfalso. apply HmfNone in Hf.
           destruct Hinp as [Hinp _]. rewrite Forall_forall in Hinp.
           apply Hinp in Hf. simpl in Hf. congruence. }
      apply Forall2_forget_r in Hp0. rewrite Forall_forall in Hp0.
      epose_dep Hp0. specialize' Hp0.
      { destruct Hall_nodes as [H' _]. apply H'. constructor. }
      fwd.
      pose proof mfs_unique as Huniq.
      epose_dep Huniq. specialize (Huniq ltac:(eassumption) ltac:(eassumption)).
      specialize' Huniq.
      { clear -Hf. (*why did taht do nothing*) clear Hp0p1. eauto. }
      specialize' Huniq.
      { clear -Hp0p1. (*why*) clear Hf. eauto. }
      subst. assumption.
  Qed.

  Lemma no_learning_inputs g n R args :
    can_learn_normal_fact_at_node (rules n) (node_states g n) R args ->
    is_input R = false.
  Proof.
    intros H.
    cbv [can_learn_normal_fact_at_node can_learn_normal_fact_at_node'] in H.
    fwd. destruct Hlayout as [_ [Hl _]]. apply Hl in Hp0.
    rewrite Forall_forall in Hp_inp. specialize (Hp_inp _ Hp0).
    destruct r; fwd; simpl in Hp_inp.
    - apply Exists_exists in Hp1p0. fwd. invert Hp1p0p1.
      apply Lists.List.Forall_map in Hp_inp.
      rewrite Forall_forall in Hp_inp.
      apply Hp_inp. assumption.
    - assumption.
    - contradiction.
  Qed.

  Lemma no_learning_inputs_meta g n R num :
    can_learn_meta_fact_at_node (rules n) (node_states g n) R num ->
    is_input R = false.
  Proof.
    intros H.
    cbv [can_learn_meta_fact_at_node] in H.
    fwd. destruct Hlayout as [_ [Hl _]]. apply Hl in Hp0.
    rewrite Forall_forall in Hp_inp. specialize (Hp_inp _ Hp0).
    simpl in Hp_inp. assumption.
  Qed.

  Lemma step_preserves_mf_correct g g' :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    meta_facts_correct rules g ->
    comp_step g g' ->
    meta_facts_correct rules g'.
  Proof.
    intros Hs Hinp Hmf Hstep.
    assert (Hs': sane_graph g').
    { eauto using step_preserves_sanity. }
    invert Hstep.
    - cbv [meta_facts_correct] in *.
      intros n'. simpl.
      destr (node_eqb n n'); auto.
      destruct f; simpl.
      + specialize (Hmf n'). cbv [meta_facts_correct_at_node] in *. simpl.
        intros R num [H'|H']; [discriminate|].
        specialize Hmf with (1 := H').
        fwd. do 2 eexists. split; [eassumption|]. split; [assumption|]. split.
        -- eapply Forall_impl; [|eassumption].
           simpl. intros R' HR'. destr (rel_eqb nf_rel R').
           2: { eapply expect_num_R_facts_incl; eauto with incl. }
           exfalso.
           eapply expect_num_R_facts_no_travellers with (g := g); try eassumption.
           rewrite H. apply in_app_iff. simpl. eauto.
        -- intros args Hargs. right. apply Hmfp3. move Hmfp0 at bottom.
           assert (Hn : ~In nf_rel Rs).
           { intros H''. rewrite Forall_forall in Hmfp2. specialize (Hmfp2 _ H'').
             simpl in Hmfp1. eapply expect_num_R_facts_no_travellers with (g := g); try eassumption.
             rewrite H. apply in_app_iff. simpl. eauto. }
           eapply can_learn_normal_fact_at_node'_incl; [eassumption| |].
           ++ simpl. intros f' HRs. split; auto. intros [Hf'|Hf']; [|assumption].
              subst. exfalso. simpl in HRs. auto.
           ++ simpl. intros R' HR'. destr (rel_eqb nf_rel R'); auto.
              exfalso. auto.
      + cbv [meta_facts_correct_at_node]. simpl. intros R num [H'|H'].
        -- invert H'.
           cbv [sane_graph] in Hs. destruct Hs as (_&HmfSome&Htrav&_).
           rewrite H in Htrav. epose_dep Htrav.
           rewrite in_app_iff in Htrav. simpl in Htrav.
           specialize (Htrav ltac:(eauto)).
           apply HmfSome in Htrav. specialize (Hmf _ _ _ Htrav).
           fwd. do 2 eexists. split; [eassumption|]. split; [assumption|]. split.
           ++ eapply Forall_impl; [|exact Hmfp2].
              simpl. intros. eapply expect_num_R_facts_incl; [eassumption|].
              auto with incl.
           ++ intros args Hargs. right. apply Hmfp3.
              eapply can_learn_normal_fact_at_node'_incl; [eassumption| |].
              --- simpl. intros. split; auto. intros [?|?]; auto. subst. assumption.
              --- simpl. auto.
        -- pose proof H' as H'0.
           apply Hmf in H'. fwd.
           do 2 eexists. split; [eassumption|]. split; [assumption|]. split.
           ++ eapply Forall_impl; [|eassumption].
              simpl. intros. eapply expect_num_R_facts_incl; [eassumption|].
              auto with incl.
           ++ intros args Hargs. right. apply H'p3.
              eapply can_learn_normal_fact_at_node'_incl; [eassumption| |].
              --- simpl. intros. split; auto. intros [?|?]; auto. subst.
                  simpl in *. rewrite Forall_forall in H'p2.
                  specialize (H'p2 _ ltac:(eassumption)).
                  apply expect_num_R_facts_knows_meta_facts; try assumption.
                  destruct Hs as (_&_&Htrav&_). eapply Htrav. rewrite H.
                  apply in_app_iff. simpl. eauto.
              --- simpl. auto.
    - rename H into Hf.
      cbv [meta_facts_correct] in *.
      intros n'. simpl.
      destr (node_eqb n n'); auto.
      destruct f; simpl in *; fwd.
      + pose proof Hmf as Hmf'.
        specialize (Hmf' n'). cbv [meta_facts_correct_at_node] in Hmf'.
        cbv [meta_facts_correct_at_node]. simpl.
        intros R num [H'|H']; [discriminate|].
        specialize Hmf' with (1 := H'). fwd.
        do 2 eexists. split; [eassumption|]. split; [assumption|]. split.
        -- eapply Forall_impl; [|eassumption].
           simpl. intros. eapply expect_num_R_facts_incl; [eassumption|].
           auto with incl.
        -- intros args Hargs. right. apply Hmf'p3.
           eapply can_learn_normal_fact_at_node'_incl; [eassumption| |].
           ++ simpl. intros f' Hf'. split; auto. intros [?|?]; auto.
              subst. simpl in Hf'. exfalso.
              rewrite Forall_forall in Hmf'p2.
              specialize (Hmf'p2 _ ltac:(eassumption)).
              apply no_learning_inputs in Hfp1.
              cbv [expect_num_R_facts] in Hmf'p2. rewrite Hfp1 in Hmf'p2.
              fwd. apply Forall2_forget_r in Hmf'p2p0. rewrite Forall_forall in Hmf'p2p0.
              epose_dep Hmf'p2p0. specialize' Hmf'p2p0.
              { destruct Hall_nodes as [Han _]. apply Han. constructor. }
              fwd. eapply Hfp0. exact Hmf'p2p0p1.
           ++ simpl. auto.
      + cbv [meta_facts_correct_at_node]. simpl. intros R num [H'|H'].
        -- invert H'.
           pose proof Hfp1 as Hfp1'. apply no_learning_inputs_meta in Hfp1'.
           cbv [can_learn_meta_fact_at_node] in Hfp1. fwd. move Hs' at top.
           assert (In R source_rels \/ ~In R source_rels) as [HR|HR].
           { apply Classical_Prop.classic. }
           ++ apply Hfp1p1p1 in HR. cbv [meta_facts_correct_at_node] in Hmf.
              cbv [expect_num_R_facts] in HR. rewrite Hfp1' in HR. fwd.
              apply Forall2_forget_r in HRp0. rewrite Forall_forall in HRp0.
              epose_dep HRp0. specialize' HRp0.
              { destruct Hall_nodes as [Han _]. apply Han. constructor. }
              fwd. specialize (Hmf _ _ _ HRp0p1). fwd.
              clear Hfp1p0 Hfp1p1p1 Hfp1p1p2.
              do 2 eexists. split; [eassumption|]. split; [assumption|]. split.
              --- eapply Forall_impl; [|eassumption]. simpl. intros.
                  eapply expect_num_R_facts_incl; [eassumption|].
                  auto with incl.
              --- intros args Hargs. right. apply Hmfp3.
                  eapply can_learn_normal_fact_at_node'_incl; [eassumption| |].
                  +++ simpl. intros f' Hf'. split; auto. intros [?|?]; auto. subst.
                      destruct Hs as (_&_&_&Hs&_). specialize (Hs _ _ _ HRp0p1).
                      subst. assumption.
                  +++ simpl. auto.
           ++ do 2 eexists. split; [eassumption|]. split; [assumption|]. split.
              --- apply Forall_forall. intros R' HR'.
                  eapply expect_num_R_facts_incl.
                  { apply Hfp1p1p1. assumption. }
                  auto with incl.
              --- intros args Hargs. right.
                  apply Hfp1p1p2. eapply can_learn_normal_fact_at_node'_weaken.
                  +++ eapply can_learn_normal_fact_at_node'_incl; [eassumption| |].
                      ---- simpl. intros f' Hf'. split; auto. intros [?|?]; auto.
                           subst. simpl in Hf'. exfalso. auto.
                      ---- simpl. auto.
                  +++ simpl. auto.
        -- apply Hmf in H'. fwd.
           do 2 eexists. split; [eassumption|]. split; [assumption|]. split.
           ++ eapply Forall_impl; [|eassumption].
              simpl. intros. eapply expect_num_R_facts_incl; [eassumption|].
              auto with incl.
           ++ intros args Hargs. right. apply H'p3.
              eapply can_learn_normal_fact_at_node'_incl; [eassumption| |].
              --- simpl. intros. split; auto. intros [?|?]; auto. subst.
                  simpl in *. rewrite Forall_forall in H'p2.
                  specialize (H'p2 _ ltac:(eassumption)).
                  cbv [expect_num_R_facts] in H'p2.
                  pose proof Hfp1 as Hfp1'.
                  apply no_learning_inputs_meta in Hfp1'.
                  rewrite Hfp1' in H'p2. fwd.
                  apply Forall2_forget_r in H'p2p0. rewrite Forall_forall in H'p2p0.
                  epose_dep H'p2p0. specialize' H'p2p0.
                  { destruct Hall_nodes as [Han _]. apply Han. constructor. }
                  fwd. destruct Hs as (_&_&_&Hmfcnt&_). move Hmfcnt at bottom.
                  specialize (Hmfcnt _ _ _ H'p2p0p1). subst.
                  move Hfp1 at bottom. cbv [can_learn_meta_fact_at_node] in Hfp1.
                  fwd. assumption.
              --- simpl. auto.
  Qed.

  Lemma comp_step_preserves_datalog_facts f g g' :
    knows_datalog_fact g f ->
    comp_step g g' ->
    knows_datalog_fact g' f.
  Proof.
    intros Hknows Hstep. pose proof Hstep as Hstep'. invert Hstep'.
    - cbv [knows_datalog_fact]. destruct f; simpl.
      + destruct Hknows; fwd; eauto.
      + cbv [knows_datalog_fact] in Hknows.
        destruct (is_input mf_rel); fwd; eauto.
        intros n'. specialize (Hknows n'). fwd. eauto.
    - cbv [knows_datalog_fact]. destruct f; simpl.
      + destruct Hknows; fwd; eauto.
      + cbv [knows_datalog_fact] in Hknows.
        destruct (is_input mf_rel); fwd; eauto.
        intros n'. specialize (Hknows n'). fwd. eauto.
  Qed.

  Lemma comp_steps_preserves_datalog_facts f g g' :
    knows_datalog_fact g f ->
    comp_step^* g g' ->
    knows_datalog_fact g' f.
  Proof.
    induction 2; eauto using comp_step_preserves_datalog_facts.
  Qed.

  Lemma node_can_receive_known_fact g f n :
    sane_graph g ->
    knows_fact g f ->
    exists g',
      comp_step^* g g' /\
        In f (g'.(node_states) n).(known_facts).
  Proof.
    intros Hs Hk. destruct Hs as (_&_&_&_&Heverywhere&_).
    apply Heverywhere with (n := n) in Hk. destruct Hk as [Hk|Hk].
    - apply in_split in Hk. fwd. eexists. split.
      { eapply rt1n_trans. 2: apply rt1n_refl.
        apply ReceiveFact. eassumption. }
      simpl. destr (node_eqb n n); [|congruence].
      apply receive_fact_at_node_receives_facts.
    - exists g. split.
      { apply rt1n_refl. }
      assumption.
  Qed.

  Lemma steps_preserves_known_facts g g' n :
    comp_step^* g g' ->
    incl (g.(node_states) n).(known_facts) (g'.(node_states) n).(known_facts).
  Proof.
    induction 1; auto with incl.
    eapply incl_tran; eauto using step_preserves_known_facts.
  Qed.

  Lemma node_can_receive_known_facts g hyps n :
    sane_graph g ->
    Forall (knows_fact g) hyps ->
    exists g',
      comp_step^* g g' /\
        Forall (fun f => In f (g'.(node_states) n).(known_facts)) hyps.
  Proof.
    intros Hs. induction 1.
    - eauto.
    - fwd. pose proof node_can_receive_known_fact as Hg'.
      specialize (Hg' g'). epose_dep Hg'.
      specialize (Hg' ltac:(eauto using steps_preserves_sanity) ltac:(eauto using steps_preserves_facts)).
      fwd.
      eexists. split.
      { eapply crt1n_transitive; eassumption. }
      constructor; [eassumption|].
      eapply Forall_impl; [|eassumption].
      simpl. intros. eapply steps_preserves_known_facts; eauto.
  Qed.

  Lemma firstn_plus {U} n m (l : list U) :
    firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
  Proof.
    revert l.
    induction n; intros l; simpl; [reflexivity|].
    destruct l.
    - rewrite firstn_nil. reflexivity.
    - simpl. f_equal. auto.
  Qed.

  Definition knows_there_are_num_R_facts g R num :=
    if is_input R then
      knows_fact g (meta_dfact R None num) /\
        Existsn (fun f0 : dfact => exists args : list T, f0 = normal_dfact R args) num
          (input_facts g)
    else
      exists nums,
        Forall2 (fun n num => knows_fact g (meta_dfact R (Some n) num)) all_nodes nums /\
          num = fold_left Nat.add nums 0.

  Lemma steps_preserves_knows_there_are_num_R_facts g g' R num :
    knows_there_are_num_R_facts g R num ->
    comp_step^* g g' ->
    knows_there_are_num_R_facts g' R num.
  Proof.
    cbv [knows_there_are_num_R_facts]. intros H Hstep.
    destruct (is_input R); simpl in *; fwd.
    - split.
      + eapply steps_preserves_facts; eassumption.
      + erewrite comp_steps_pres_inputs by eassumption. assumption.
    - eexists. split; [|reflexivity]. eapply Forall2_impl; [|eassumption].
      simpl. eauto using steps_preserves_facts.
  Qed.

  Lemma knows_datalog_fact_knows_num_R_facts g R S :
    knows_datalog_fact g (meta_fact R S) ->
    exists num,
      knows_there_are_num_R_facts g R num.
  Proof.
    intros H. cbv [knows_datalog_fact] in H. cbv [knows_there_are_num_R_facts].
    destruct (is_input R).
    - fwd. eauto.
    - clear -H Hall_nodes.
      enough (forall len, exists nums,
                 Forall2 (fun (n0 : Node) (num : nat) => knows_fact g (meta_dfact R (Some n0) num))
                   (firstn len all_nodes) nums) as H'.
      { specialize (H' (length all_nodes)). rewrite firstn_all in H'. fwd. eauto. }
      intros len. induction len.
      { simpl. eauto. }
      fwd. replace (Datatypes.S len) with (len + 1) by lia.
      rewrite firstn_plus.
      destruct (skipn len all_nodes) as [|n' ?].
      { simpl. rewrite app_nil_r. eauto. }
      simpl. specialize (H n'). fwd. eexists (_ ++ [_]).
      apply Forall2_app; eauto.
  Qed.

  Lemma node_can_receive_meta_facts g R num n :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    knows_there_are_num_R_facts g R num ->
    exists g',
      comp_step^* g g' /\
        expect_num_R_facts R (g'.(node_states) n).(known_facts) num.
  Proof.
    intros Hsane Hinp H. cbv [knows_there_are_num_R_facts] in H.
    cbv [expect_num_R_facts].
    destruct (is_input R).
    - fwd. eapply node_can_receive_known_fact in Hp0; eauto.
    - pose proof node_can_receive_known_facts as H'.
      fwd. edestruct H'.
      + eassumption.
      + eapply Forall_zip. eapply Forall2_impl; [|eassumption]. simpl.
        instantiate (1 := fun _ _ => _). simpl. intros. eassumption.
      + fwd. eexists. split; [eassumption|].
        eexists. split; [|reflexivity]. eapply Forall2_impl.
        2: { eapply Forall2_zip; [|eassumption]. eapply Forall2_length. eassumption. }
        simpl. eauto.
  Qed.

  Lemma node_can_receive_travellers g num_trav n R :
    Existsn (fun '(n', f) => n = n' /\ (exists args : list T, f = normal_dfact R args))
      num_trav g.(travellers) ->
    exists g' : graph_state,
      comp_step^* g g' /\
        msgs_received (node_states g' n) R =
          msgs_received (node_states g n) R + num_trav.
  Proof.
    revert g. induction num_trav; intros g Hg.
    - eauto.
    - apply Existsn_S in Hg. fwd. epose (g1 := _).
      specialize (IHnum_trav g1). eenough _ as H'.
      { specialize (IHnum_trav H'). fwd. eexists. split.
        { eapply rt1n_trans.
          { apply ReceiveFact. eassumption. }
          subst g1. eassumption. }
        subst g1. simpl in *. destr (node_eqb n0 n0); [|congruence].
        simpl in *. destr (rel_eqb R R); [|congruence]. lia. }
      subst g1. simpl. assumption.
  Qed.

  Lemma node_can_receive_expected_facts g R n num :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    knows_there_are_num_R_facts g R num ->
    expect_num_R_facts R (g.(node_states) n).(known_facts) num ->
    exists g',
      comp_step^* g g' /\
        (g'.(node_states) n).(msgs_received) R = num.
  Proof.
    intros Hs Hinp Hk H. cbv [knows_there_are_num_R_facts expect_num_R_facts] in *.
    destruct (is_input R) eqn:ER.
    - fwd. cbv [sane_graph] in Hs. destruct Hs as (_&_&_&_&_&Hcnt&Hinp_sane).
      specialize (Hcnt n R). fwd. eapply Existsn_unique in Hkp1; [|exact Hcntp1].
      subst.
      specialize (Hinp_sane R). rewrite ER in Hinp_sane. fwd.
      erewrite map_ext with (g := fun _ => 0) in Hcntp2 by auto.
      rewrite map_const in Hcntp2. rewrite fold_left_add_repeat in Hcntp2.
      replace (0 * length all_nodes + 0 + num) with num in Hcntp2 by lia.
      subst. apply node_can_receive_travellers. assumption.
    - fwd. cbv [sane_graph] in Hs. destruct Hs as (_&HmfSome&_&Hmf_sane&_&Hcnt&_).
      rewrite Hkp1.
      specialize (Hcnt n R). fwd. assert (num_inp = 0).
      { eapply Existsn_unique; [eassumption|].
        (*maybe should state this as a lemma*)
        apply Forall_not_Existsn_0.
        move Hinp at bottom. destruct Hinp as (Hinp&_).
        eapply Forall_impl; [|exact Hinp]. simpl. intros f Hf1 Hf2. fwd.
        simpl in *. congruence. }
      subst. clear Hcntp1. clear Hkp1. clear Hp0 expected_msgss.
      assert (map (fun n' : Node => msgs_sent (node_states g n') R) all_nodes = nums).
      { apply Forall2_eq_eq. rewrite <- Forall2_map_l.
        eapply Forall2_impl; [|eassumption].
        simpl. intros n' num Hn'. apply Hmf_sane. apply HmfSome. apply Hn'. }
      subst.
      eapply node_can_receive_travellers in Hcntp0. fwd.
      eexists. split; [eassumption|]. lia.
  Qed.

  Lemma steps_preserves_meta_facts_correct g g' :
    sane_graph g ->
    good_inputs (input_facts g) ->
    meta_facts_correct rules g ->
    comp_step^* g g' ->
    meta_facts_correct rules g'.
  Proof.
    intros Hs Hinp Hmf Hstep. induction Hstep; auto.
    apply IHHstep.
    - eauto using steps_preserves_sanity.
    - erewrite comp_steps_pres_inputs by (eapply rt1n_trans; eauto). assumption.
    - eapply step_preserves_mf_correct; eauto.
  Qed.

  Lemma node_can_expect g R num n :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    knows_there_are_num_R_facts g R num ->
    exists g',
      comp_step^* g g' /\
        expect_num_R_facts R (g'.(node_states) n).(known_facts) ((g'.(node_states) n).(msgs_received) R).
  Proof.
    intros Hsane Hinp H.
    pose proof H as H'.
    eapply node_can_receive_meta_facts in H; try assumption.
    fwd.
    eapply steps_preserves_knows_there_are_num_R_facts in H'; [|eassumption].
    eapply node_can_receive_expected_facts in H'.
    2: { eauto using steps_preserves_sanity. }
    2: { erewrite comp_steps_pres_inputs by eassumption. assumption. }
    2: { eassumption. }
    fwd. eexists. split; cycle 1.
    { eapply expect_num_R_facts_incl. 1: eassumption.
      eapply steps_preserves_known_facts. eassumption. }
    eauto using crt1n_transitive.
  Qed.

  (*what a stupid name*)
  Lemma node_can_expect_much g Rs Ss n :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    length Rs = length Ss ->
    Forall (knows_datalog_fact g) (zip meta_fact Rs Ss) ->
    exists g',
      comp_step^* g g' /\
        Forall (fun R => expect_num_R_facts R (g'.(node_states) n).(known_facts) ((g'.(node_states) n).(msgs_received) R)) Rs.
  Proof.
    intros Hs Hinp.
    revert Ss. induction Rs; intros [|R ?] Hlen; simpl in Hlen;
      try discriminate; simpl; invert 1.
    - eauto.
    - specialize IHRs with (2 := H3). specialize (IHRs ltac:(lia)). fwd.
      rename H2 into HR. eapply comp_steps_preserves_datalog_facts in HR; [|eassumption].
      apply knows_datalog_fact_knows_num_R_facts in HR. fwd.
      eapply node_can_expect in HR.
      2: { eauto using steps_preserves_sanity. }
      2: { erewrite comp_steps_pres_inputs by eauto. assumption. }
      fwd.
      eexists. split.
      { eapply crt1n_transitive; eassumption. }
      constructor; eauto. eapply Forall_impl; [|eassumption].
      simpl. intros R' H'. eapply expect_num_R_facts_incl.
      { erewrite expect_num_R_facts_msgs_received_stable_steps.
        - eassumption.
        - eauto using steps_preserves_sanity.
        - erewrite comp_steps_pres_inputs by eauto. assumption.
        - assumption.
        - eassumption. }
      eapply steps_preserves_known_facts. eassumption.
  Qed.

  Definition rel_of (f : fact) :=
    match f with
    | normal_fact R _ => R
    | meta_fact R _ => R
    end.

  Definition fact_in_inputs inps f :=
    match f with
    | normal_fact R args => In (normal_dfact R args) inps
    | meta_fact R T =>
        exists num,
        In (meta_dfact R None num) inps /\
          Existsn (fun x => exists args, x = normal_dfact R args) num inps /\
          forall args, T args <-> In (normal_dfact R args) inps
    end.

  Definition mf_consistent g f :=
    match f with
    | normal_fact _ _ => True
    | meta_fact R S' =>
        forall args,
          knows_fact g (normal_dfact R args) <-> S' args
    end.

  Definition graph_correct_for g R :=
    (forall f',
        rel_of f' = R ->
        (knows_datalog_fact g f' /\ mf_consistent g f') ->
        prog_impl_implication p (fact_in_inputs g.(input_facts)) f').

  Definition graph_correct g :=
    forall f,
      (knows_datalog_fact g f /\ mf_consistent g f) ->
      prog_impl_implication p (fact_in_inputs g.(input_facts)) f.

  Definition finite_fact (f : fact) :=
    match f with
    | normal_fact _ _ => True
    | meta_fact R S' => exists l, forall x, S' x -> In x l
    end.

  Definition graph_complete (g : graph_state) :=
    forall f,
      prog_impl_implication p (fact_in_inputs g.(input_facts)) f ->
      exists g',
        comp_step^* g g' /\
          knows_datalog_fact g' f.

  Definition same_msgs_received g g' :=
    forall n,
      (g.(node_states) n).(msgs_received) = (g'.(node_states) n).(msgs_received).

  Print meta_facts_correct_at_node.
  Lemma node_can_find_all_conclusions g l n R :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    meta_facts_correct rules g ->
    (forall args g',
        comp_step^* g g' ->
        knows_fact g' (normal_dfact R args) ->
        In args l) ->
    exists g',
      comp_step^* g g' /\
        (forall args,
            can_learn_normal_fact_at_node (rules n) (node_states g' n) R args ->
            In (normal_dfact R args) (known_facts (node_states g' n))) /\
        same_msgs_received g g'.
  Proof.
    intros Hsane Hinp Hmf Hl.
    assert (Hor : (fun P => P \/ ~P) (exists num, In (meta_dfact R (Some n) num) (known_facts (node_states g n)))).
    { apply Classical_Prop.classic. }
    simpl in Hor. destruct Hor as [Hor|Hor].
    { admit. } (* fwd. intros. exists g. split; [auto|]. split; [|cbv [same_msgs_received]; auto]. *)
      (* intros. Print meta_facts_correct_at_node. apply Hmf in Hor. fwd. Print good_meta_rules. capply Horp3auto. destruct Hor as [_ Hor]. apply Hor. assumption. } *)
    assert (Hl0: forall args g',
               comp_step^* g g' ->
               knows_fact g' (normal_dfact R args) ->
               In (normal_dfact R args) (known_facts (node_states g n)) \/ In args l).
    { eauto. }
    clear Hl. rename Hl0 into Hl. revert g Hsane Hinp Hmf Hor Hl.
    remember (length l) as len eqn:E.
    assert (Hlen: length l < S len) by lia. clear E.
    revert l Hlen. induction (S len) as [|len0]; intros l Hlen g Hsane Hinp Hmf Hor Hl.
    - lia.
    - assert (Hor' : (fun P => P \/ ~P) (Exists (fun args => can_learn_normal_fact_at_node (rules n) (node_states g n) R args) l)).
      { apply Classical_Prop.classic. }
      destruct Hor' as [Hor'|Hor'].
      + rewrite Exists_exists in Hor'. destruct Hor' as (args&Hor'). fwd.
        apply in_split in Hor'p0. fwd.
        specialize (IHlen0 (l1 ++ l2)). specialize' IHlen0.
        { rewrite length_app in *. simpl in *. lia. }
        eassert (Hstep : comp_step g _).
        { eapply LearnFact with (f := normal_dfact R args).
          simpl. eauto. }
        epose_dep IHlen0.
        specialize' IHlen0.
        { eapply step_preserves_sanity; eassumption. }
        specialize' IHlen0.
        { simpl. assumption. }
        specialize' IHlen0.
        { eapply step_preserves_mf_correct; eassumption. }
        simpl in IHlen0. destr (node_eqb n n); [|congruence]. simpl in IHlen0.
        specialize' IHlen0.
        { simpl. intros H'. fwd. destruct H'; [congruence|eauto]. }
        specialize' IHlen0.
        { simpl. intros args' g' Hsteps Hargs'.
          specialize (Hl args' g' ltac:(eauto) ltac:(assumption)).
          move Hl at bottom. destruct Hl as [Hl|Hl]; auto.
          apply in_app_iff in Hl. rewrite in_app_iff.
          destruct Hl as [Hl| [Hl| Hl]]; subst; auto. }
        fwd. exists g'. split; [eauto|]. split; [assumption|]. cbv [same_msgs_received].
        intros n'. rewrite <- IHlen0p2. simpl. destr (node_eqb n n'); reflexivity.
      + exists g. ssplit; auto. 2: cbv [same_msgs_received]; auto.
        intros args Hargs. epose_dep Hl. specialize' Hl.
        { eapply rt1n_trans; [|apply rt1n_refl].
          eapply LearnFact with (f := normal_dfact _ _).
          simpl. split; [|eassumption]. eauto. }
        specialize' Hl.
        { right. simpl. exists n. destr (node_eqb n n); [|congruence]. simpl. auto. }
        destruct Hl; [assumption|]. exfalso. rewrite Exists_exists in Hor'. eauto.
  Abort.

  Lemma receive_fact_at_node_impl ns f f0 :
    In f0 (receive_fact_at_node ns f).(known_facts) ->
    In f0 ns.(known_facts) \/ f0 = f.
  Proof.
    intros H. destruct f; simpl in *.
    - destruct H; auto.
    - destruct H; auto.
  Qed.

  Lemma learn_fact_at_node_impl ns f f0 :
    In f0 (learn_fact_at_node ns f).(known_facts) ->
    In f0 ns.(known_facts) \/ f0 = f.
  Proof.
    intros H. destruct f; simpl in *.
    - destruct H; auto.
    - destruct H; auto.
  Qed.

  Lemma only_one_fact_learned g n f f0 :
    knows_fact
      {|
        node_states :=
          fun n' : Node =>
          if node_eqb n n'
          then learn_fact_at_node (node_states g n) f0
          else node_states g n';
        travellers := map (fun n : Node => (n, f0)) all_nodes ++ travellers g;
        input_facts := input_facts g
      |} f ->
    knows_fact g f \/ f = f0.
  Proof.
    intros Hf. destruct Hf as [Hf|Hf]; simpl in Hf.
    - eauto.
    - fwd. destr (node_eqb n n0); eauto.
      apply learn_fact_at_node_impl in Hf. destruct Hf; eauto.
  Qed.

  Lemma nothing_new_received g n f0 fs1 fs2 f :
    sane_graph g ->
    knows_fact
      {|
        node_states :=
          fun n' : Node =>
            if node_eqb n n'
            then receive_fact_at_node (node_states g n) f0
            else node_states g n';
        travellers := fs1 ++ fs2;
        input_facts := input_facts g
      |} f ->
    travellers g = fs1 ++ (n, f0) :: fs2 ->
    knows_fact g f.
  Proof.
    intros Hsane Hf Hf0.
    destruct Hf as [Hf|Hf]; simpl in Hf.
    -- eauto.
    -- fwd. destr (node_eqb n n0); cycle 1.
       { eauto. }
       apply receive_fact_at_node_impl in Hf. destruct Hf as [Hf|Hf].
       { eauto. }
       subst. destruct Hsane as (_&_&Htrav&_).
       eapply Htrav. rewrite Hf0. apply in_app_iff. simpl. eauto.
  Qed.

  Lemma knows_meta_fact_step_learns_nothing g g' R S args :
    sane_graph g ->
    knows_datalog_fact g (meta_fact R S) ->
    comp_step g g' ->
    knows_fact g' (normal_dfact R args) ->
    knows_fact g (normal_dfact R args).
  Proof.
    intros Hsane H Hstep Hargs. simpl in H.
    pose proof Hstep as Hstep'. invert Hstep.
    - eauto using nothing_new_received.
    - apply only_one_fact_learned in Hargs.
      destruct Hargs as [Hargs|Hargs]; auto.
      subst. simpl in H0. fwd. apply no_learning_inputs in H0p1.
      rewrite H0p1 in *. specialize (H n). fwd.
      exfalso. eapply H0p0. destruct Hsane as (_&HmfSome&_).
      apply HmfSome. eassumption.
  Qed.

  Lemma knows_meta_fact_steps_learns_nothing g g' R S args :
    sane_graph g ->
    knows_datalog_fact g (meta_fact R S) ->
    comp_step^* g g' ->
    knows_fact g' (normal_dfact R args) ->
    knows_fact g (normal_dfact R args).
  Proof.
    induction 3; auto.
    intros. eapply knows_meta_fact_step_learns_nothing; eauto.
    apply IHclos_refl_trans_1n.
    - eauto using steps_preserves_sanity.
    - eauto using comp_steps_preserves_datalog_facts.
    - assumption.
  Qed.

  Lemma consistent_preserved g g' R S :
    sane_graph g ->
    knows_datalog_fact g (meta_fact R S) ->
    mf_consistent g (meta_fact R S) ->
    comp_step^* g g' ->
    mf_consistent g' (meta_fact R S).
  Proof.
    intros Hs Hk Hc Hstep. cbv [mf_consistent].
    cbv [mf_consistent] in Hc. intros args. rewrite <- Hc. clear Hc.
    split.
    - eauto using knows_meta_fact_steps_learns_nothing.
    - eauto using steps_preserves_facts.
  Qed.

  Definition good_input_hyps Q :=
    (forall R' S',
        Q (meta_fact R' S') -> forall x, Q (normal_fact R' x) <-> S' x) /\
      forall f, Q f -> is_input (rel_of f) = true.

  Lemma no_learning_inputs' r f hyps :
    rule_impl r f hyps ->
    In r p ->
    is_input (rel_of f) = false.
  Proof.
    intros H1 H2.
    rewrite Forall_forall in Hp_inp. apply Hp_inp in H2.
    invert H1.
    + apply Exists_exists in H. fwd. invert Hp1. simpl. simpl in H2.
      rewrite Forall_forall in H2. apply H2. apply in_map_iff. eauto.
    + simpl. simpl in H2. assumption.
    + simpl. simpl in H2. assumption.
  Qed.

  Lemma meta_rules_sound Q R0 S0 :
    good_input_hyps Q ->
    prog_impl_implication p Q (meta_fact R0 S0) ->
    consistent p Q R0 S0.
  Proof.
    intros HQ H. remember (meta_fact R0 S0) as f eqn:E. revert R0 S0 E.
    induction H; intros R0 S0 ?; subst.
    - cbv [consistent]. cbv [good_input_hyps] in HQ. fwd. intros x.
      rewrite <- HQp0 with (S' := S0); [|eassumption]. split.
      2: { intros. apply partial_in. assumption. }
      intros H'. invert H'; auto. exfalso. rename H0 into Hr.
      apply Exists_exists in Hr. fwd. apply HQp1 in H. simpl in H.
      apply no_learning_inputs' in Hrp1; [|eassumption]. simpl in Hrp1. congruence.
    - apply Exists_exists in H. fwd.
      rewrite Forall_forall in Hgmr. specialize (Hgmr _ ltac:(eassumption)).
      cbv [good_meta_rule] in Hgmr.
      cbv [consistent]. intros args. rewrite Hgmr.
      2: { cbv [rule_impl_implication]. eexists. split; [eassumption|].
           invert Hp1. apply Forall2_zip in H1; [|assumption].
           apply Forall_zip. eapply Forall2_impl; [|exact H1].
           simpl. auto. }
      split; auto. intros [HQ'|?]; auto. exfalso.
      apply HQ in HQ'. simpl in HQ'.
      rewrite Forall_forall in Hp_inp. apply Hp_inp in Hp0.
      invert Hp1. simpl in Hp0. congruence.
  Qed.

  Lemma hmfs_unique Q R S S' :
    good_input_hyps Q ->
    prog_impl_implication p Q (meta_fact R S) ->
    prog_impl_implication p Q (meta_fact R S') ->
    forall args,
      S args <-> S' args.
  Proof.
    intros HQ H1 H2 args. cbv [good_meta_rule] in Hgmr.
    eapply meta_rules_sound in H1, H2; try assumption.
    cbv [consistent] in H1, H2. rewrite <- H1, <- H2. reflexivity.
  Qed.

  Lemma fact_in_inputs_knows_datalog_fact g f :
    fact_in_inputs g.(input_facts) f ->
    good_inputs g.(input_facts) ->
    knows_datalog_fact g f.
  Proof.
    intros H Hinp. destruct f; simpl in *; eauto.
    fwd.
    destruct Hinp as [Hinp _]. rewrite Forall_forall in Hinp.
    specialize (Hinp _ ltac:(eassumption)).
    simpl in Hinp. rewrite Hinp. eauto.
  Qed.

  Lemma input_facts_come_from_input Q f :
    is_input (rel_of f) = true ->
    prog_impl_implication p Q f ->
    Q f.
  Proof.
    intros Hinp.
    invert 1; auto.
    rename H0 into Hr. apply Exists_exists in Hr. fwd.
    rewrite Forall_forall in Hp_inp. specialize (Hp_inp _ Hrp0).
    invert Hrp1; simpl in Hp_inp, Hinp.
    - apply Exists_exists in H. fwd. invert Hp1. rewrite Forall_forall in Hp_inp.
      rewrite Hp_inp in Hinp; [congruence|]. apply in_map. assumption.
    - congruence.
    - congruence.
  Qed.

  (*TODO this does not belong here*)
  Instance existsb_spec U (f : U -> _) l :
    BoolSpec (Exists (fun x => f x = true) l) (Forall (fun x => f x = false) l) (existsb f l).
  Proof.
    destruct (existsb f l) eqn:E; constructor.
    - apply existsb_exists in E. fwd. apply Exists_exists. eauto.
    - assert (E': ~existsb f l = true) by congruence. rewrite existsb_exists in E'.
      apply Forall_forall. intros. enough (f x <> true) by (destruct (f x); congruence).
      eauto.
  Qed.

  (*TODO does not belong here*)
  Lemma zip_app A B C xs1 xs2 ys1 ys2 (f : A -> B -> C) :
    length xs1 = length ys1 ->
    zip f (xs1 ++ xs2) (ys1 ++ ys2) = zip f xs1 ys1 ++ zip f xs2 ys2.
  Proof.
    intros. cbv [zip]. rewrite combine_app by assumption. apply map_app.
  Qed.

  Lemma zip_cons A B C x xs y ys (f : A -> B -> C) :
    zip f (x :: xs) (y :: ys) = f x y :: zip f xs ys.
  Proof. reflexivity. Qed.

  Lemma prog_impl_trans Q f :
    prog_impl_implication p (prog_impl_implication p Q) f ->
    prog_impl_implication p Q f.
  Proof. apply partial_pftree_trans. Qed.

  Print good_meta_rule.

  Definition good_meta_rule' R Rs :=
    forall Q args,
      prog_impl_implication p Q (normal_fact R args) ->
      Q (normal_fact R args) \/
        prog_impl_implication p (fun f => prog_impl_implication p Q f /\ In (rel_of f) Rs) (normal_fact R args).

  Lemma good_meta_rule_good_meta_rule' R f Rs :
    good_meta_rule p (meta_rule R f Rs) ->
    good_meta_rule' R Rs.
  Proof.
    cbv [good_meta_rule good_meta_rule']. intros H Q args Hargs.
    pose proof H as H'.
    specialize (H Q).
    specialize (H' (fun f => prog_impl_implication p Q f /\ In (rel_of f) Rs)).
    epose_dep H. specialize' H.
    { clear H'. cbv [rule_impl_implication]. eexists. split.
      - eapply meta_rule_impl with
          (source_sets := map (fun R' args => prog_impl_implication p Q (normal_fact R' args)) Rs).
        { rewrite length_map. reflexivity. }
        reflexivity.
      - apply Forall_zip. rewrite <- Forall2_map_r. apply Forall2_same.
        apply Forall_forall. intros R' HR'. cbv [consistent]. reflexivity. }
    epose_dep H'. specialize' H'.
    { clear H. cbv [rule_impl_implication]. eexists. split.
      - eapply meta_rule_impl with
          (source_sets := map (fun R' args => prog_impl_implication p Q (normal_fact R' args)) Rs).
        { rewrite length_map. reflexivity. }
        reflexivity.
      - apply Forall_zip. rewrite <- Forall2_map_r. apply Forall2_same.
        apply Forall_forall. intros R' HR'. cbv [consistent].
        intros args'. split; intros Hargs'.
        + apply prog_impl_trans. eapply prog_impl_implication_weaken_hyp; [eassumption|].
          simpl. intros. fwd. assumption.
        + apply partial_in. auto. }
    apply H in Hargs. clear H. destruct Hargs as [Hargs|Hargs]; [auto|].
    right. apply H'. clear H'. right. exact Hargs.
  Qed.

  Definition intersect {A} (eqb : A -> A -> bool) l1 l2 :=
    filter (fun x => existsb (eqb x) l2) l1.

  Definition intersect_many {A} (eqb : A -> A -> bool) ls :=
    match ls with
    | [] => []
    | l :: ls' => fold_right (intersect eqb) l ls'
    end.

  (*Gemini tries to help*)
  Section Specifications.
    Context {A : Type}.
    Context (eqb : A -> A -> bool).

    (* Assumption: eqb correctly reflects propositional equality *)
    Context (eqb_eq : EqDecider eqb).

    (** Helper Lemma: Connects existsb and In using our eqb_eq assumption.
     **)
    Lemma existsb_In : forall x l,
        existsb (eqb x) l = true <-> In x l.
    Proof.
      intros x l. rewrite existsb_exists. split.
      - intros [y [Hin Heqb]]. destr (eqb x y); congruence.
      - intros Hin. exists x. split; auto. destr (eqb x x); congruence.
    Qed.

    (** Specification 1: intersect
    An element is in the intersection if and only if it is in both lists.
     **)
    Lemma intersect_spec : forall x l1 l2,
        In x (intersect eqb l1 l2) <-> In x l1 /\ In x l2.
    Proof.
      intros x l1 l2.
      unfold intersect.
      rewrite filter_In.
      rewrite existsb_In.
      reflexivity.
    Qed.

    (** Helper Lemma: Describes the behavior of fold_right over intersect.
     **)
    Lemma fold_right_intersect_spec : forall x l ls,
        In x (fold_right (intersect eqb) l ls) <-> In x l /\ forall l', In l' ls -> In x l'.
    Proof.
      intros x l ls. induction ls as [|a ls IHls].
      - simpl. split.
        + intros H. split; auto. intros l' H'. contradiction.
        + intros [H _]. exact H.
      - simpl. rewrite intersect_spec. rewrite IHls. split.
        + intros [Ha [Hl Hls]]. split; auto. intros l' [H_eq | H_in].
          * subst. exact Ha.
          * apply Hls. exact H_in.
        + intros [Hl Hls]. split.
          * apply Hls. left. reflexivity.
          * split; auto.
    Qed.

    (** Specification 2: intersect_many
    For a non-empty list of lists, an element is in the intersection
    if and only if it is present in every list.
    (Note: The specification inherently requires the list of lists to not be empty).
     **)
    Lemma intersect_many_spec : forall x ls,
        ls <> [] ->
        (In x (intersect_many eqb ls) <-> forall l, In l ls -> In x l).
    Proof.
      intros x ls Hneq. destruct ls as [|l ls].
      - contradiction.
      - simpl. rewrite fold_right_intersect_spec. split.
        + intros [Hl Hls] l' [H_eq | H_in].
          * subst. exact Hl.
          * apply Hls. exact H_in.
        + intros H. split.
          * apply H. left. reflexivity.
          * intros l' H_in. apply H. right. exact H_in.
    Qed.
  End Specifications.

  Lemma weaken_good_meta_rule' R Rs1 Rs2 :
    incl Rs1 Rs2 ->
    good_meta_rule' R Rs1 ->
    good_meta_rule' R Rs2.
  Proof.
    cbv [good_meta_rule']. intros Hincl H Q args Hargs.
    apply H in Hargs. destruct Hargs as [Hargs|Hargs]; auto.
    right. eapply prog_impl_implication_weaken_hyp; [eassumption|].
    simpl. intros. fwd. auto with incl.
  Qed.

  Lemma pairwise_intersect_good_meta_rule' R Rs1 Rs2 :
    good_meta_rule' R Rs1 ->
    good_meta_rule' R Rs2 ->
    good_meta_rule' R (intersect rel_eqb Rs1 Rs2).
  Proof.
    cbv [good_meta_rule']. intros H1 H2 Q args Hargs.
    pose proof H1 as H1'. pose proof H2 as H2'.
    specialize (H1 _ _ Hargs). specialize (H2 _ _ Hargs).
    destruct H1 as [H1|H1]; auto. destruct H2 as [H2|H2]; auto.
    apply H1' in H2. apply H2' in H1.
    right. destruct H1 as [H1|H1].
    - destruct H2 as [H2|H2].
      + fwd. apply partial_in. split; auto. apply intersect_spec; auto.
      + clear H1 Hargs. eapply prog_impl_implication_weaken_hyp; [exact H2|].
  Abort.

  Lemma good_meta_rule'_good_meta_rule R f Rs :
    good_meta_rule' R Rs ->
    good_meta_rule p (meta_rule R f Rs).
  Proof.
    cbv [good_meta_rule' good_meta_rule]. intros H Q R0 S0 H0 args.
    cbv [rule_impl_implication] in H0. fwd. invert H0p0.
    apply Forall2_zip in H0p1; [|assumption].
    split; intros Hargs.
    - apply H in Hargs. destruct Hargs as [Hargs|Hargs]; [auto|]. admit.
    - admit.
  Abort.

  Lemma intersect_meta_rules R f Rs f' Rs' :
    good_meta_rule p (meta_rule R f Rs) ->
    good_meta_rule p (meta_rule R f' Rs') ->
    exists f0,
      good_meta_rule p (meta_rule R f0 (filter (fun x => existsb (rel_eqb x) Rs') Rs)).
  Proof.
    intros H1 H2. set (Rs0 := @nil rel).
    eassert (filter _ Rs = Rs0 ++ filter _ Rs) as -> by (subst Rs0; reflexivity).
    revert H1.
    assert (meta_rule R f Rs = meta_rule R f (Rs0 ++ Rs)) as -> by (subst Rs0; reflexivity).
    clearbody Rs0. revert f Rs0. induction Rs as [|R0 Rs]; intros f Rs0 H1.
    - exists f. simpl. assumption.
    - simpl. destr (existsb (rel_eqb R0) Rs').
      + specialize (IHRs f (Rs0 ++ [R0])). do 2 rewrite <- app_assoc in IHRs.
        apply IHRs. assumption.
      + apply IHRs with
          (f := fun l => f (firstn (length Rs0) l ++ (fun _ => False) :: skipn (length Rs0) l)).
        clear IHRs.
        cbv [good_meta_rule]. intros Q R' S' H' args.
        (*instantiate H1 with Q := prog_impl_implication Q \ R0.  instantiate H2 with Q := Q and Q := Q \ R0.*)
        pose proof H2 as H2'.
        specialize (H1 (fun f => prog_impl_implication p Q f /\ rel_of f <> R0)).
        specialize (H2 Q).
        specialize (H2' (fun f => prog_impl_implication p Q f /\ rel_of f <> R0)).
        apply H2.
        rewrite H2.
        rewrite H2 with (S0 := S'). 2: admit.
        cbv [rule_impl_implication] in H'. fwd. invert H'p0. rewrite length_app in *.
        rewrite <- (firstn_skipn (length Rs0) source_sets) in H'p1.
        rewrite zip_app in H'p1.
        2: { rewrite length_firstn. lia. }
        apply Forall_app in H'p1. fwd.
        apply Forall2_zip in H'p1p0.
        2: { rewrite length_firstn. lia. }
        apply Forall2_zip in H'p1p1.
        2: { rewrite length_skipn. lia. }
        epose_dep H2. specialize' H2.
        { clear H1 H2'. eexists. split.
          - eapply meta_rule_impl with
              (source_sets := map (fun R'' args'' => prog_impl_implication p Q (normal_fact R'' args'')) Rs').
            2: reflexivity.
            rewrite length_map. reflexivity.
          - apply Forall_zip. rewrite <- Forall2_map_r.
            apply Forall2_same. apply Forall_forall. intros R'' HR''.
            cbv [consistent]. intros. reflexivity. }
        epose_dep H2'. specialize' H2'.
        { clear H1 H2. eexists. split.
          - eapply meta_rule_impl with
              (source_sets := map (fun R'' args'' => prog_impl_implication p Q (normal_fact R'' args'')) Rs').
            2: reflexivity.
            rewrite length_map. reflexivity.
          - apply Forall_zip. rewrite <- Forall2_map_r.
            apply Forall2_same. apply Forall_forall. intros R'' HR''.
            cbv [consistent]. intros. split.
            + intros H''. apply prog_impl_trans.
              eapply prog_impl_implication_weaken_hyp; [eassumption|].
              simpl. intros. fwd. assumption.
            + intros. apply partial_in. split; [assumption|].
              rewrite Forall_forall in E. apply E in HR''. simpl.
              destr (rel_eqb R0 R''); congruence. }
        (*this seems true, but I think i am going about the proof not quite right*)
        (*and i don't actually need this lemma; intersection property of
          good_meta_rule' suffices*)
  Abort.

  Lemma use_meta_facts_correct R g :
    good_inputs g.(input_facts) ->
    sane_graph g ->
    (* In (meta_rule R S Rs) p -> *)
    meta_facts_correct rules g ->
    (forall R',
        (forall f Rs, In (meta_rule R f Rs) p -> In R' Rs) ->
        graph_correct_for g R') ->
    (* Forall (fun R' => graph_correct_for g R' /\ knows_datalog_fact g (meta_fact R' (fun _ => True))) Rs -> *)
    knows_datalog_fact g (meta_fact R (fun _ => True)) ->
    forall args,
      prog_impl_implication p (fact_in_inputs (input_facts g)) (normal_fact R args) ->
      knows_fact g (normal_dfact R args).
  Proof.
    intros Hinp Hsane Hmf HRs HR args Hargs.
    simpl in HR. destruct (is_input R) eqn:E.
    { apply input_facts_come_from_input in Hargs; [|assumption].
      simpl in Hargs. auto. }
    eassert (Hg: exists (Rss : list (list rel)),
                Forall2
                  (fun n Rs => exists f,
                       In (meta_rule R f Rs) (rules n) /\
                         (forall args,
                             can_learn_normal_fact_at_node' (fun R' : rel => In R' Rs) (rules n)
                               (node_states g n) R args ->
                             In (normal_dfact R args) (known_facts (node_states g n))))
                  all_nodes Rss).
    { apply Forall_exists_r_Forall2.
      apply Forall_forall. intros n _.
      specialize (HR n). fwd. specialize (Hmf n).
      cbv [meta_facts_correct_at_node] in Hmf. destruct Hsane as (_&HmfSome&_).
      apply HmfSome in HR. apply Hmf in HR. fwd. eauto. }
    fwd.

  In (meta_rule R f Rs) rules /\

      eexists f.
      apply Hmf in HR.
    -
      2: { simpl. assumption
      simpl in Hargs. Search fact_in_inputs. invert Hargs. fwd. destruct Hsane as (HmfNone&_). apply HmfNone in HRp0.
      destruct Hinp as [_ Hinp]. apply Hinp in HRp0.
    cbv [good_meta_rule] in Hgmr.
    (*for every such R', every node knows every fact about it;
      and no node can deduce a new fact from these R's.
      So, ....
     *)


    cbv [meta_facts_correct meta_facts_correct_at_node] in Hmf.
    invert Hargs.
    - apply fact_in_inputs_knows_datalog_fact in H. 1: apply H. assumption.
    - apply Exists_exists in H. fwd. Print meta_facts_correct_at_node.
      move prog_good at bottom. cbv [good_prog] in prog_good.
      specialize (prog_good _ _ _ ltac:(eassumption)).
      move Hlayout at bottom. cbv [good_layout] in Hlayout.
      invert Hp1.
      + pose proof Hp0 as Hp0'.
        destruct Hlayout as (Hhl&Hlh&Hm). apply Hhl in Hp0. clear Hhl.
        fwd. move HR at bottom. simpl in HR.
        eapply Hm in Hr. clear Hm.
        pose proof rules_good as rules_good'.
        specialize (rules_good' n).
        rewrite Forall_forall in rules_good'. specialize (rules_good' _ Hr).
        simpl in rules_good'. rewrite rules_good' in HR. specialize (HR n).
        pose proof Hsane as Hsane'. fwd.
        destruct Hsane as (_&HmfSome&_). apply HmfSome in HR. apply Hmf in HR.
        fwd. right. eexists. apply HRp1.
        cbv [can_learn_normal_fact_at_node]. eexists. split; [exact Hp0|]. simpl.
        do 2 eexists. split; [eassumption|]. split; [eassumption|].
        intros R0 args0 Hargs0.
        apply expect_num_R_facts_knows_everything; try assumption.
        -- rewrite Forall_forall in HRp0. specialize (HRp0 _ Hp0). simpl in HRp0.
           specialize' HRp0.
           { apply in_map_iff. apply Exists_exists in H3. fwd. invert H3p1. eauto. }
           rewrite Lists.List.Forall_map in HRp0. rewrite Forall_forall in HRp0.
           apply Forall2_forget_l in H5. rewrite Forall_forall in H5.
           specialize (H5 _ Hargs0). fwd. invert H5p1. apply HRp0. assumption.
        -- rewrite Forall_forall in HRs. move HRs at bottom. specialize (HRs R0).
           specialize' HRs.
           { destruct prog_good as (Hp_1&_). eapply Hp_1; try eassumption.
             --- apply in_map_iff. apply Exists_exists in H3. fwd. invert H3p1. eauto.
             --- apply Forall2_forget_l in H5. rewrite Forall_forall in H5.
                 specialize (H5 _ Hargs0). fwd. invert H5p1. apply in_map_iff. eauto. }
           fwd. cbv [graph_correct_for] in HRsp0.
           epose proof (HRsp0 (meta_fact _ _) eq_refl) as HRsp0. specialize' HRsp0.
           { split.
             { simpl. exact HRsp1. }
             simpl. intros. instantiate (1 := fun _ => _). simpl. reflexivity. }
           move Hgmr at bottom. cbv [good_meta_rules] in Hgmr.
           eapply Hgmr in HRsp0.
           2: { simpl. intros R' S' H'' x0. fwd. intros. symmetry. apply H''p2. }
           destruct HRsp0 as [HRsp0|HRsp0].
           { simpl in HRsp0. eauto. }
           apply HRsp0. rewrite Forall_forall in H0. apply H0. apply in_map_iff.
           eexists (_, _). eauto.
      + pose proof Hp0 as Hp0'.
        destruct Hlayout as (Hhl&Hlh&Hm). apply Hhl in Hp0. clear Hhl.
        fwd. move HR at bottom. simpl in HR.
        eapply Hm in Hr. clear Hm.
        pose proof rules_good as rules_good'.
        specialize (rules_good' n).
        rewrite Forall_forall in rules_good'. specialize (rules_good' _ Hr).
        simpl in rules_good'. rewrite rules_good' in HR. specialize (HR n).
        pose proof Hsane as Hsane'. fwd.
        destruct Hsane as (_&HmfSome&_). apply HmfSome in HR. apply Hmf in HR.
        fwd. right. eexists. apply HRp1.
        cbv [can_learn_normal_fact_at_node]. eexists. split; [exact Hp0|]. simpl.
        rewrite Forall_forall in HRp0. specialize (HRp0 _ Hp0). simpl in HRp0.
        specialize (HRp0 eq_refl).
        split; [assumption|]. eexists. split; [|eauto].
        move H4 at bottom. destruct H4 as (H4p0&H4p1). split; [|assumption].
        intros x. rewrite <- H4p0. move Hgmr at bottom. cbv [good_meta_rules] in Hgmr.
        move H0p0 at bottom. pose proof H0p0 as H0p0'. eapply Hgmr in H0p0.
        2: { simpl. intros R' S' H'' x0. fwd. intros. symmetry. apply H''p2. }
        move HRs at bottom. rewrite Forall_forall in HRs.
        specialize (HRs source_rel). specialize' HRs.
        { destruct prog_good as (_&Hp_2). eapply Hp_2. eassumption. }
        fwd. cbv [graph_correct_for] in HRsp0.
        destruct H0p0 as [H0p0|H0p0].
        { split; intros _; cycle 1.
          { simpl in HRsp0. eapply expect_num_R_facts_knows_everything; eauto. }
          Search fact_in_inputs. Print good_inputs.
          simpl in H0p0.
          move Hinp at bottom. cbv [good_inputs] in Hinp. destruct Hinp as (Hinp&_).
          rewrite Forall_forall in Hinp. specialize (Hinp _ H0p0). simpl in Hinp.
          apply input_meta_facts_come_from_input in H0p0'; [|assumption].
          simpl in H0p0'. fwd. apply H0p0'p2. assumption. }
        rewrite <- H0p0. split; intros H'.
        -- apply HRsp0.
           ++ reflexivity.
           ++ simpl. eauto.
        -- epose proof (HRsp0 (meta_fact _ _) eq_refl) as HRsp0. specialize' HRsp0.
           { split.
             { simpl. exact HRsp1. }
             simpl. intros. instantiate (1 := fun _ => _). simpl. reflexivity. }
           eapply hmfs_unique in HRsp0. 3: exact H0p0'.
           2: { simpl. intros R' S' H'' x0. fwd. intros. symmetry. apply H''p2. }
           apply H0p0 in H'. destruct HRsp0 as [HRsp0|HRsp0].
           { simpl in HRsp0. eapply expect_num_R_facts_knows_everything; try assumption.
             eauto. }
           apply HRsp0 in H'.
           eapply expect_num_R_facts_knows_everything; assumption.
  Qed.

  Lemma list_em U (l : list U) P Q :
    Forall (fun x => P x \/ Q x) l ->
    Forall P l \/ Exists Q l.
  Proof.
    induction 1; auto.
    do 2 match goal with | H: _ \/ _ |- _ => destruct H end; auto.
  Qed.

  Lemma meta_fact_ext (r : rule) R S S' hyps :
    (forall x, S x <-> S' x) ->
    rule_impl r (meta_fact R S) hyps ->
    rule_impl r (meta_fact R S') hyps.
  Proof.
    intros H1 H2. invert H2.
    constructor; auto. intros. rewrite <- H1. auto.
  Qed.

  Lemma graph_correct_for_preserved g g' R :
    sane_graph g ->
    (forall f, rel_ofd f = R ->
          knows_fact g' f ->
          knows_fact g f) ->
    comp_step g g' ->
    graph_correct_for g R ->
    graph_correct_for g' R.
  Proof.
    intros Hsane H1 Hstep H2. cbv [graph_correct_for]. intros f' ? (H3&H4). subst.
    erewrite comp_step_pres_inputs by eassumption.
    apply H2; auto.
    destruct f'; simpl in *.
    - auto.
    - destruct (is_input mf_rel).
      + fwd. split.
        -- eexists. split; eauto.
           erewrite comp_step_pres_inputs in H3p1 by eassumption.
           assumption.
        -- intros. rewrite <- H4. split; eauto.
      + split.
        -- intros n. specialize (H3 n). fwd. eauto.
        -- intros args. rewrite <- H4. split; eauto.
  Qed.

  Lemma good_layout_sound' g g' :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    meta_facts_correct rules g ->
    graph_correct g ->
    comp_step g g' ->
    graph_correct g'.
  Proof.
    intros Hsane Hinp Hmfs Hsound Hstep f (Hf1&Hf2).
    pose proof Hstep as Hstep'.
    invert Hstep.
    - apply Hsound. destruct f; simpl in *.
      + eauto using nothing_new_received.
      + destruct (is_input mf_rel).
        -- fwd. split; [eauto using nothing_new_received|].
           intros. rewrite <- Hf2. split; eauto using nothing_new_received.
        -- split.
           ++ intros n'. specialize (Hf1 n'). fwd. eauto using nothing_new_received.
           ++ intros. rewrite <- Hf2. split; eauto using nothing_new_received.
    - destruct f; simpl in *.
      + apply only_one_fact_learned in Hf1. destruct Hf1; eauto. subst.
        simpl in H. destruct H as (_&H).
        (*maybe should proe some lemma about can_learn_normal_fact_at_node..*)
        cbv [can_learn_normal_fact_at_node] in H. fwd. destruct r; fwd.
        -- apply Exists_exists in Hp1p0. destruct Hp1p0 as (r&Hr1&Hr2).
           eapply prog_impl_step.
           ++ apply Exists_exists. eexists. split.
              { destruct Hlayout as (_&Hlh&_). eapply Hlh. eassumption. }
              econstructor.
              --- apply Exists_exists. eauto.
              --- eassumption.
           ++ apply Forall_map. apply Forall_forall. intros [R' args'] H'.
              apply Hsound. simpl. eauto 6.
        -- eapply prog_impl_step.
           ++ apply Exists_exists. eexists. split.
              { destruct Hlayout as (_&Hlh&_). eapply Hlh. eassumption. }
              econstructor. instantiate (1 := fun _ => _). simpl. eassumption.
           ++ constructor.
              --- apply Hsound. split.
                  +++ eapply something_about_expect_num_R_facts; eassumption.
                  +++ simpl. intros. split; eauto. intros Hargs.
                      apply expect_num_R_facts_knows_everything; assumption.
              --- apply Forall_map. apply Forall_forall. intros x Hx.
                  destruct Hp1p1p0 as (H'&_). apply H' in Hx.
                  apply Hsound. simpl. eauto.
        -- contradiction.
      + destruct (is_input mf_rel) eqn:E.
        -- apply Hsound. simpl. rewrite E.
           fwd. apply only_one_fact_learned in Hf1p0. destruct Hf1p0.
           { simpl. split; eauto. intros. rewrite <- Hf2. split; eauto.
             intros [Hargs|Hargs]; eauto. simpl in Hargs. fwd.
             destr (node_eqb n n0); eauto.
             apply learn_fact_at_node_impl in Hargs.
             destruct Hargs as [Hargs|Hargs]; eauto.
             subst. simpl in H. destruct H as [_ H].
             apply no_learning_inputs in H. congruence. }
           subst. simpl in H. fwd. congruence.
        -- pose proof list_em as H'.
           specialize (H' _ all_nodes). epose_dep H'. specialize' H'.
           { apply Forall_forall. intros n' _. specialize (Hf1 n').
             fwd. apply only_one_fact_learned in Hf1. destruct Hf1 as [Hf1|Hf1].
             - left. instantiate (1 := fun _ => exists num, _). exists num. exact Hf1.
             - right. instantiate (1 := fun _ => exists num, _). exists num. exact Hf1. }
           destruct H' as [H'|H'].
           ++ apply Hsound. simpl. rewrite E. split.
              --- intros n'. rewrite Forall_forall in H'. apply H'.
                  destruct Hall_nodes as (Han&_). apply Han. constructor.
              --- intros. rewrite <- Hf2. split; eauto.
                  intros [Hargs|Hargs]; eauto. simpl in Hargs. fwd.
                  destr (node_eqb n n0); eauto.
                  apply learn_fact_at_node_impl in Hargs.
                  destruct Hargs as [Hargs|Hargs]; eauto.
                  subst. simpl in H. rewrite Forall_forall in H'.
                  specialize (H' n0). specialize' H'.
                  { destruct Hall_nodes as [Hn0 _]. apply Hn0. constructor. }
                  fwd. exfalso. eapply Hp0. destruct Hsane as (_&HmfSome&_).
                  apply HmfSome. eassumption.
           ++ apply Exists_exists in H'. fwd.
              clear H'p0. simpl in H. fwd.
              cbv [can_learn_meta_fact_at_node] in Hp1. fwd.
              destruct Hlayout as (_&Hlh&_). specialize (Hlh _ _ ltac:(eassumption)).
              eapply prog_impl_step.
              --- apply Exists_exists. eexists. split; [eassumption|].
                  eenough _ as H'. 1: eapply meta_fact_ext; [|exact H'].
                  2: { eapply meta_rule_impl with (source_sets := map (fun R args => knows_fact g (normal_dfact R args)) source_rels).
                     { rewrite length_map. reflexivity. }
                     intros. reflexivity. }
                  pose proof Hgmr as Hgmr'.
                  cbv [good_meta_rules] in Hgmr'.
                  intros args. rewrite <- Hf2.
                  eenough _ as H'1; [eenough _ as H'2; [epose proof (Hgmr' _ H'1 _ _ H'2 _) as Hgmr'; clear H'1 H'2|clear H'1]|].
                  2: { eapply prog_impl_step.
                       { apply Exists_exists. eexists.
                         split; [eassumption|]. eassumption. }
                       apply Forall_zip. apply Forall2_map_r. apply Forall2_same.
                       apply Forall_forall. intros R' HR'.
                       apply Hsound. split.
                       { eapply something_about_expect_num_R_facts; eauto. }
                       simpl. reflexivity. }
                  2: { simpl. intros R' S' H'' x0. fwd.
                       intros. symmetry. apply H''p2. }
                  destruct Hgmr' as [Hgmr'|Hgmr'].
                  { exfalso. move E at bottom.
                    simpl in Hgmr'. move Hinp at bottom. destruct Hinp as [Hinp _].
                    rewrite Forall_forall in Hinp. apply Hinp in Hgmr'. simpl in Hgmr'.
                    congruence. }
                  rewrite <- Hgmr'.
                  split; intros Hargs.
                  +++ move Hlayout at bottom. destruct Hlayout as (_&Hlh'&_).
                      apply Hlh' in Hp1p0.
                      eapply use_meta_facts_correct.
                      ---- simpl. assumption.
                      ---- eauto using step_preserves_sanity.
                      ---- eassumption.
                      ---- eauto using step_preserves_mf_correct.
                      ---- apply Forall_forall. intros R HR. split.
                           ++++ eapply graph_correct_for_preserved; try eassumption.
                                ----- intros f ? Hf. subst.
                                apply only_one_fact_learned in Hf.
                                destruct Hf; auto. subst. simpl in HR.
                                apply Hp1p1p1 in HR. cbv [expect_num_R_facts] in HR.
                                rewrite E in HR. fwd. eapply Forall2_forget_r in HRp0.
                                rewrite Forall_forall in HRp0.
                                specialize (HRp0 n). specialize' HRp0.
                                { destruct Hall_nodes as [H'' _]. apply H''. constructor. }
                                destruct Hsane as (_&_&_&Hsent&_).
                                fwd. pose proof HRp0p1. apply Hsent in HRp0p1.
                                subst. eauto.
                                ----- cbv [graph_correct_for]. intros.
                                apply Hsound. assumption.
                           ++++ eapply comp_step_preserves_datalog_facts; [|eassumption].
                                eapply something_about_expect_num_R_facts; eauto.
                      ---- simpl. rewrite E. assumption.
                      ---- simpl. assumption.
                  +++ apply Hsound. simpl. split; [|constructor].
                      apply only_one_fact_learned in Hargs.
                      destruct Hargs; [assumption|congruence].
              --- apply Forall_zip. apply Forall2_map_r. apply Forall2_same.
                  apply Forall_forall. intros R HR.
                  apply Hsound. split.
                  +++ eapply something_about_expect_num_R_facts; try eassumption. auto.
                  +++ simpl. intros. reflexivity.
  Qed.

  Lemma good_layout_sound g g' :
    sane_graph g ->
    good_inputs g.(input_facts) ->
    meta_facts_correct rules g ->
    graph_correct g ->
    comp_step^* g g' ->
    graph_correct g'.
  Proof.
    induction 5; auto. apply IHclos_refl_trans_1n.
    - eauto using step_preserves_sanity.
    - erewrite comp_step_pres_inputs by eassumption. assumption.
    - eapply step_preserves_mf_correct; eassumption.
    - eapply good_layout_sound'; eassumption.
  Qed.

  Lemma good_layout_complete'' r hyps g f :
    good_inputs g.(input_facts) ->
    sane_graph g ->
    meta_facts_correct rules g ->
    graph_correct g ->
    Forall (knows_datalog_fact g) hyps ->
    Forall (consistent g) hyps ->
    finite_fact f ->
    In r p ->
    rule_impl r f hyps ->
     exists g',
       comp_step^* g g' /\
         knows_datalog_fact g' f.
  Proof.
    intros Hinp Hsane Hmf Hcor Hhyps1 Hhyps2 Hfin Hr Himpl.
    pose proof Hlayout as Hgood.
    pose proof Hgood as Hgood'.
    assert (Hpii: prog_impl_implication p (fact_in_inputs g.(input_facts)) f).
    { eapply prog_impl_step.
      - apply Exists_exists. eauto.
      - eapply Forall_impl. 2: apply Forall_and; [exact Hhyps1|exact Hhyps2].
        simpl. intros. apply Hcor. assumption. }
    invert Himpl.
    - cbv [good_layout] in Hgood. destruct Hgood as (Hgood&_).
      apply Hgood in Hr. clear Hgood.
      destruct Hr as (n&Hr).

      edestruct node_can_receive_known_facts as (g1&Hstep1&Hhypsg1).
      { eassumption. }
      { apply Forall_map with (f := fun '(R, args) => normal_dfact R args).
        rewrite Lists.List.Forall_map in Hhyps1.
        eapply Forall_impl; [|exact Hhyps1].
        simpl. intros [? ?]. simpl. intros H'. exact H'. }

      eenough (Hcan: can_learn_normal_fact_at_node (rules n) (node_states g1 n) R _).
      { pose proof (Classical_Prop.classic (exists num, In (meta_dfact R (Some n) num) (known_facts (node_states g1 n)))) as Hor.
        destruct Hor as [Hor|Hor].
        { exists g1. split; [eassumption|].
          simpl. cbv [knows_fact].
          eapply steps_preserves_meta_facts_correct in Hmf; cycle -1.
          { exact Hstep1. }
          all: try eassumption.
          cbv [meta_facts_correct meta_facts_correct_at_node] in Hmf.
          fwd. specialize Hmf with (1 := Hor). destruct Hmf as (_&Hmf). eauto. }
        fwd.
        eexists. split.
          { (*first, step to a state where node n knows all the hypotheses;
              then, one final step where n deduces the conclusion*)
            eapply crt1n_transitive.
            { exact Hstep1. }
            eapply rt1n_trans. 2: apply rt1n_refl.
            apply LearnFact with (n := n) (f := normal_dfact R args).
            simpl. split.
            { eauto. }
            assumption. }
      simpl. cbv [knows_fact]. simpl. right. exists n.
      destr (node_eqb n n); [|congruence].
      simpl. left. reflexivity. }
      cbv [can_learn_normal_fact_at_node].
      eexists. split; [eassumption|]. simpl.
      do 2 eexists. split; [eassumption|]. split; [eassumption|].
      intros R' args' H'. rewrite Lists.List.Forall_map in Hhypsg1.
      rewrite Forall_forall in Hhypsg1. apply Hhypsg1 in H'. exact H'.
    - cbv [good_layout] in Hgood. destruct Hlayout as (Hhl&Hlh&Hm).
      apply Hhl in Hr. clear Hgood.
      destruct Hr as (n&Hr).

      invert Hhyps1. rename H2 into Hmhyp. rename H3 into Hhyps.

      edestruct node_can_receive_known_facts with (g := g) as (g1&Hg1&Hhyps1).
      { eassumption. }
      { eapply Forall_map.
        rewrite Lists.List.Forall_map in Hhyps.
        exact Hhyps. }

      pose proof Hmhyp as HS.
      eapply comp_steps_preserves_datalog_facts in Hmhyp; [|exact Hg1].
      eapply knows_datalog_fact_knows_num_R_facts in Hmhyp. fwd.
      pose proof Hmhyp as Hmhyp'.
      eapply node_can_receive_meta_facts in Hmhyp.
      2: { eauto using steps_preserves_sanity. }
      2: { erewrite comp_steps_pres_inputs by eauto. assumption. }
      destruct Hmhyp as (g2&Hg2&Hnum).

      pose proof node_can_receive_expected_facts as Hrcv.
      specialize Hrcv with (g := g2).
      epose_dep Hrcv. specialize' Hrcv.
      { eapply steps_preserves_sanity; eauto using crt1n_transitive. }
      specialize' Hrcv.
      { erewrite comp_steps_pres_inputs. 1: eassumption. eauto using crt1n_transitive. }
      specialize' Hrcv.
      { eapply steps_preserves_knows_there_are_num_R_facts; eauto using crt1n_transitive. }
      specialize (Hrcv Hnum). destruct Hrcv as (g3&Hg3&Hnum').

      eassert (Hcan: can_learn_normal_fact_at_node (rules n) (node_states g3 n) _ _).
      { cbv [can_learn_normal_fact_at_node].
        eexists. split; [eassumption|]. simpl.
        split.
        { rewrite <- Hnum' in *. eapply expect_num_R_facts_incl; [eassumption|].
          eapply steps_preserves_known_facts. eassumption. }
        eexists. split.
        { move H at bottom. cbv [is_list_set] in H. fwd. split; [|eassumption].
          intros x. split; intros Hx.
          + pose proof good_layout_sound as Hsound.
            specialize (Hsound g g3 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(eauto using crt1n_transitive)).
            pose proof Hsound as Hsound'.
            specialize (Hsound (normal_fact source_rel [x])).
            specialize' Hsound.
            { simpl. eauto. }
            specialize (Hsound' (meta_fact source_rel S)).
            specialize' Hsound'.
            { split.
              - eapply comp_steps_preserves_datalog_facts.
                1: eassumption. eauto using crt1n_transitive.
              - eapply consistent_preserved; try eassumption. eauto using crt1n_transitive. }
            (*should follow from Hrels plus Hrels'*)
            pose proof Hgmr as Hgmr'.
            apply Hp0. cbv [good_meta_rules] in Hgmr'.
            eenough _ as H'1; [eenough _ as H'2; [epose proof (Hgmr' _ H'1 _ _ H'2 _) as Hgmr'; clear H'1 H'2|clear H'1]|].
            2: eassumption.
            2: { simpl. intros R' S' H' x0. fwd. intros. symmetry. apply H'p2. }
            destruct Hgmr' as [Hgmr'|Hgmr'].
            { move Hinp at bottom.
              assert (g3.(input_facts) = g.(input_facts)) as Hif.
              { repeat erewrite comp_steps_pres_inputs by eassumption. reflexivity. }
              rewrite Hif in *. clear Hif.
              cbv [good_inputs] in Hinp. destruct Hinp as (Hinp&_).
              rewrite Forall_forall in Hinp. specialize (Hinp _ Hgmr'). simpl in Hinp.
              simpl in Hgmr'.
              apply input_meta_facts_come_from_input in Hsound'; [|assumption].
              simpl in Hsound'. fwd. apply Hsound'p2. eassumption. }
            apply Hgmr'. assumption.
          + apply Lists.List.Forall_map in Hhyps1. rewrite Forall_forall in Hhyps1.
            specialize (Hhyps1 _ Hx).
            eapply steps_preserves_known_facts. 2: eassumption.
            eauto using crt1n_transitive. }
        split; reflexivity. }
      epose proof (Classical_Prop.classic (exists num, In (meta_dfact _ (Some n) num) (known_facts (node_states g3 n)))) as Hor.
      destruct Hor as [Hor|Hor].
      { fwd. exists g3.
        split; [eauto using crt1n_transitive|]. simpl. cbv [knows_fact].
        eapply steps_preserves_meta_facts_correct with (g' := g3) in Hmf.
        all: try eassumption.
        2: { eauto using crt1n_transitive. }
        cbv [meta_facts_correct meta_facts_correct_at_node] in Hmf.
        move Hmf at bottom. epose_dep Hmf. specialize (Hmf Hor).
        right. eexists. eapply Hmf. assumption. }
      eassert (Hlast_step: comp_step g3 _).
      { eapply LearnFact with (n := n) (f := normal_dfact _ _).
        simpl. split.
        { eauto. }
        eassumption. }
      fwd. eexists. split.
      { (*first, step to a state where node n knows all the hypotheses;
            then, one final step where n deduces the conclusion*)
        eapply crt1n_transitive.
        { exact Hg1. }
        eapply crt1n_transitive.
        { exact Hg2. }
        eapply crt1n_transitive.
        { exact Hg3. }
        eapply rt1n_trans. 2: apply rt1n_refl. eassumption. }
        simpl. cbv [knows_fact]. simpl. right. exists n.
        destr (node_eqb n n); try congruence. simpl. auto.
    - simpl in Hfin. fwd.
      destruct Hlayout as (_&_&Hml).
      specialize Hml with (1 := Hr).
      cbv [knows_datalog_fact].
      enough (forall len,
               exists g' : graph_state,
                 comp_step^* g g' /\
                   (forall n : Node,
                       In n (firstn len all_nodes) ->
                       exists num : nat, knows_fact g' (meta_dfact target_rel (Some n) num))) as H'.
      { specialize (H' (length all_nodes)). rewrite firstn_all in H'.
        fwd. eexists. split; eauto.
        destruct (is_input target_rel) eqn:E.
        { cbv [good_rules] in rules_good.
          specialize (rules_good a_node).
          specialize (Hml a_node).
          rewrite Forall_forall in rules_good. apply rules_good in Hml.
          simpl in Hml. congruence. }
        intros n0. apply H'p1. destruct Hall_nodes as [H' ?]. apply H'. auto. }
      intros len. induction len.
      { exists g. split; [apply rt1n_refl|]. simpl. contradiction. }

      destruct IHlen as (g1&Hg1&Hhypsg1).

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
      epose_dep Hg2. specialize' Hg2.
      { eauto using steps_preserves_sanity. }
      specialize' Hg2.
      { erewrite comp_steps_pres_inputs by eauto. assumption. }
      specialize (Hg2 ltac:(eassumption)). specialize' Hg2.
      { eapply Forall_impl; [|eassumption].
        intros. eapply comp_steps_preserves_datalog_facts; eassumption. }
      destruct Hg2 as (g2&Hg2&Hhypsg2).

      pose proof node_can_find_all_conclusions as Hg3.

      specialize (Hg3 g2 l n target_rel).
      specialize' Hg3.
      { eauto using steps_preserves_sanity. }
      specialize' Hg3.
      { erewrite comp_steps_pres_inputs with (g := g) by eauto using crt1n_transitive. assumption. }
      specialize' Hg3.
      { eapply steps_preserves_meta_facts_correct; eauto using crt1n_transitive. }
      specialize' Hg3.
      { intros args g' Hsteps Hargs.
        apply Hfin.
        move Hgmr at bottom. move Hpii at bottom.
        cbv [good_meta_rules] in Hgmr. eapply Hgmr in Hpii.
        2: { simpl. intros R' S' H'' x0. fwd. intros. symmetry. apply H''p2. }
        pose proof good_layout_sound as Hsound.
        specialize (Hsound g g' ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(eauto using crt1n_transitive)).
        destruct Hpii as [Hpii|Hpii].
        { exfalso. move Hr at bottom.
          move rules_good at bottom. cbv [good_rules] in rules_good.
          move Hlayout at bottom. destruct Hlayout as [Hlayout' _].
          apply Hlayout' in Hr. fwd.
          epose_dep rules_good. rewrite Forall_forall in rules_good.
          apply rules_good in Hr. simpl in Hr.
          move Hinp at bottom. destruct Hinp as [Hinp _].
          rewrite Forall_forall in Hinp. simpl in Hpii.
          apply Hinp in Hpii. simpl in Hpii.
          congruence. }
        apply Hpii.
        erewrite <- comp_steps_pres_inputs with (g' := g') by eauto using crt1n_transitive.
        apply Hsound. simpl. auto. }
      destruct Hg3 as (g3&Hg3&Hhyps3a&Hhyps3b).

      eexists.
      split.
      { eapply crt1n_transitive.
        { exact Hg1. }
        eapply crt1n_transitive.
        { exact Hg2. }
        eapply crt1n_transitive.
        { exact Hg3. }
        eapply rt1n_trans. 2: apply rt1n_refl.
        eapply LearnFact with (f := meta_dfact target_rel (Some n) _).
        simpl. split; [reflexivity|]. cbv [can_learn_meta_fact_at_node].
        eexists. split.
        { apply Hgood. eassumption. }
        simpl. split; [reflexivity|]. split.
        { apply Forall_forall.
          eapply Forall_impl; [|eassumption].
          simpl. intros R' HR'.
          cbv [same_msgs_received] in Hhyps3b. rewrite <- Hhyps3b.
          eapply expect_num_R_facts_incl; [eassumption|].
          eapply steps_preserves_known_facts. eassumption. }
        split.
        { eassumption. }
        reflexivity. }
      rewrite Hn. intros n' Hn'. rewrite in_app_iff in Hn'.
      destruct Hn' as [Hn'|Hn'].
      { apply Hhypsg1 in Hn'. fwd. eexists.
        eapply steps_preserves_facts. 1: eassumption.
        { (*oops i already proved htis earlier*)
          eapply crt1n_transitive.
        { exact Hg2. }
        eapply crt1n_transitive.
        { exact Hg3. }
        eapply rt1n_trans. 2: apply rt1n_refl.
        eapply LearnFact with (f := meta_dfact target_rel (Some n) _).
        simpl. split; [reflexivity|]. cbv [can_learn_meta_fact_at_node].
        eexists. split.
        { apply Hgood. eassumption. }
        simpl. split; [reflexivity|]. split.
        { apply Forall_forall.
          eapply Forall_impl; [|eassumption].
          simpl. intros R' HR'.
          cbv [same_msgs_received] in Hhyps3b. rewrite <- Hhyps3b.
          eapply expect_num_R_facts_incl; [eassumption|].
          eapply steps_preserves_known_facts. eassumption. }
        split.
        { eassumption. }
        reflexivity.
        (*end repeated stuff*) } }
      destruct Hn' as [?|?]; [subst|contradiction].
      eexists. cbv [knows_fact]. simpl. right.
      exists n'. destr (node_eqb n' n'); [|congruence]. simpl. left. reflexivity.
  Qed.

  Lemma inputs_came_from_inputs g R args :
    sane_graph g ->
    is_input R = true ->
    knows_fact g (normal_dfact R args) ->
    In (normal_dfact R args) (input_facts g).
  Proof.
    intros Hsane HR Hargs. cbv [knows_fact] in Hargs.
    destruct Hargs as [Hargs|Hargs]; auto. fwd.
    cbv [sane_graph] in Hsane. destruct Hsane as (_&_&_&_&_&Hsp1&Hsp2).
    (*oops, not true*)
  Abort.

  Lemma correct_impl_consistent g f :
    good_inputs g.(input_facts) ->
    graph_correct_for g (rel_of f) ->
    prog_impl_implication p (fact_in_inputs g.(input_facts)) f ->
    knows_datalog_fact g f ->
    consistent g f.
  Proof.
    intros Hinp Hsound Himpl Hf.
    pose proof Hsound as Hsound'.
    destruct f; simpl.
    { constructor. }
    epose proof (Hsound (meta_fact mf_rel _) ltac:(simpl; reflexivity)) as Hsound.
    specialize' Hsound.
    { split.
      - simpl. exact Hf.
      - simpl. intros. instantiate (1 := fun _ => _). simpl. reflexivity. }
    intros.
    destruct (is_input mf_rel) eqn:E.
    { apply input_meta_facts_come_from_input in Himpl, Hsound; try assumption.
      simpl in Himpl, Hsound. fwd. rewrite Himplp2. rewrite Hsoundp2. reflexivity. }
    eapply hmfs_unique in Hsound. 3: exact Himpl.
    2: { simpl. intros R' S' H'' x0. fwd. intros. symmetry. apply H''p2. }
    destruct Hsound as [Hsound|Hsound].
    { destruct Hinp as [Hinp _].
      rewrite Forall_forall in Hinp. specialize (Hinp _ Hsound).
      simpl in Hinp. congruence. }
    rewrite <- Hsound. reflexivity.
  Qed.

  Definition finite {T} (S0 : T -> _) :=
    exists l, forall x, S0 x -> In x l.

  Lemma fact_in_inputs_finite fs R S :
    fact_in_inputs fs (meta_fact R S) ->
    finite S.
  Proof.
    simpl. intros H. fwd. cbv [finite].
    exists (flat_map (fun f => match f with
                       | normal_dfact R args => [args]
                       | meta_dfact _ _ _ => []
                       end) fs).
    intros. apply in_flat_map. eexists. rewrite <- Hp2. split; [eassumption|].
    simpl. auto.
  Qed.

  Definition meta_facts_finite (p : list rule) :=
    forall Q,
      (forall R S, Q (meta_fact R S) -> finite S) ->
      (forall R S, prog_impl_implication p Q (meta_fact R S) -> finite S).

  Context (Hfinite : meta_facts_finite p).

  Lemma good_layout_complete g :
    good_inputs g.(input_facts) ->
    sane_graph g ->
    meta_facts_correct rules g ->
    graph_correct g ->
    graph_complete g.
  Proof.
    intros Hinp Hsane Hmfc Hsound.
    cbv [graph_complete].
    intros f H.
    (*it's possible to do this without generalizing g, but i don't want to*)
    remember (fact_in_inputs g.(input_facts)) as Q eqn:E.
    revert g E Hinp Hsane Hmfc Hsound. induction H; intros g E Hinp Hsane Hmfc Hsound; subst.
    - exists g. eauto using fact_in_inputs_knows_datalog_fact.
    - assert (Hg1: exists g1, comp_step^* g g1 /\ Forall (knows_datalog_fact g1) l).
      { clear H0 H. induction H1.
        - eauto.
        - fwd. move H at bottom. specialize (H g1).
          specialize' H.
          { erewrite <- comp_steps_pres_inputs with (g := g) (g' := g1) by eauto. reflexivity. }
          specialize' H.
          { erewrite comp_steps_pres_inputs with (g := g) (g' := g1) by eauto. assumption. }
          specialize' H.
          { eauto using steps_preserves_sanity. }
          specialize' H.
          { eauto using steps_preserves_meta_facts_correct. }
          specialize' H.
          { eapply good_layout_sound; eassumption. }
          destruct H as (g2&Hstep2&Hg2).
          eexists. split.
          { eapply crt1n_transitive.
            { apply IHForallp0. }
            apply Hstep2. }
          constructor; auto.
          eapply Forall_impl; [|apply IHForallp1].
          eauto using comp_steps_preserves_datalog_facts. }
      clear H1.
      destruct Hg1 as (g1&Hstep1&Hg1).
      apply Exists_exists in H. destruct H as (r&Hr1&Hr2).
      pose proof good_layout_complete'' as H'.
      specialize (H' r l g1 x).
      specialize' H'.
      { erewrite comp_steps_pres_inputs with (g := g) (g' := g1) by eauto. assumption. }
      specialize' H'.
      { eauto using steps_preserves_sanity. }
      specialize' H'.
      { eauto using steps_preserves_meta_facts_correct. }

      specialize' H'.
      { eapply good_layout_sound; eassumption. }
      specialize (H' ltac:(assumption)).
      specialize' H'.
      { apply Forall_forall. intros f' Hf'. destruct f'; [constructor|].
        apply correct_impl_consistent.
        - erewrite comp_steps_pres_inputs with (g := g) by eauto. assumption.
        - intros ? ? ?. eapply good_layout_sound; eassumption.
        - rewrite Forall_forall in H0.
          erewrite comp_steps_pres_inputs with (g := g) by eauto.
          apply H0. assumption.
        - rewrite Forall_forall in Hg1. auto. }
      specialize' H'.
      { cbv [finite_fact]. destruct x; [constructor|].
        eapply Hfinite.
        2: { eapply prog_impl_step; [|eassumption].
             apply Exists_exists. eauto. }
        apply fact_in_inputs_finite. }
      specialize (H' ltac:(assumption) ltac:(assumption)).
      destruct H' as (g2&Hstep2&Hg2). exists g2.
      split; [eauto using crt1n_transitive|].
      assumption.
  Qed.
End DistributedDatalog.
Check good_layout_sound. Print good_meta_rules. Print good_prog.
