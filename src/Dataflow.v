From Stdlib Require Import List Bool.
From Datalog Require Import Datalog Tactics.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.
From Stdlib Require Import Lia.
From ATL Require Import Relations. (*TODO i did not actually mean to use trc from here; should i use the stdlib thing instead?*)
From Datalog Require Import List.

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
  Context {node_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (node_eqb x y)}.
  Context (is_input : rel -> bool).
  Context {rel_eqb : rel -> rel -> bool}.
  Context {rel_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (rel_eqb x y)}.
  
  Inductive dfact :=
  | normal_dfact (nf_rel: rel) (nf_args: list T)
  | meta_dfact (mf_rel: rel) (source: option Node) (expected_msgs: nat) (*number of messages that node "source" will ever send about mf_rel*).

  Let clause := clause rel var fn.
  Let rule := rule rel var fn aggregator T.
  Let fact := fact rel T.

  Inductive drule :=
  | normal_drule (rule_concls : list clause) (rule_hyps : list clause)
  | agg_drule (rule_agg : aggregator) (target_rel : rel) (source_rel : rel)
  | meta_drule (target_rel : rel) (source_rels : list rel).    
  
  Definition drule_good (r : drule) :=
    match r with
    | normal_drule cs _ => Forall (fun R => is_input R = false) (map fact_R cs)
    | agg_drule _ target_rel _ => is_input target_rel = false
    | meta_drule _ _ => True
    end.

  Definition good_rules rules :=
    forall (n : Node), Forall drule_good (rules n).
  
  (*we can assume this wlog, since any normal rules violating it are useless*)
  Definition good_prog (p : list rule) :=
    forall R f Rs,
      In (meta_rule R f Rs) p ->
      forall concls hyps R',
        In (normal_rule concls hyps) p ->
        In R (map fact_R concls) ->
        In R' (map fact_R hyps) ->
        In R' Rs.

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

  Context (p : list rule) (rules : Node -> list drule).
  Context (rules_good : good_rules rules) (prog_good : good_prog p) (layout_good : good_layout p rules).
  
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

  Definition Layout := Node -> list drule.

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
  Proof.
    intros H Hincl. cbv [expect_num_R_facts] in *.
    destruct (is_input R); auto.
    fwd. eexists. split; eauto.
    eapply Forall2_impl; [|eassumption].
    simpl. auto.
  Qed.

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
              | _ => progress fwd
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

  Hint Constructors Existsn : core.
  Lemma Existsn_S (X : Type) P n (l : list X) :
    Existsn P (S n) l ->
    exists l1 x l2,
      l = l1 ++ x :: l2 /\
        P x /\
        Existsn P n (l1 ++ l2).
  Proof.
    induction l; invert 1.
    - specialize (IHl ltac:(assumption)). fwd. do 3 eexists. split.
      { apply app_comm_cons. }
      simpl. auto.
    - exists nil. simpl. eauto.
  Qed.

  Lemma Existsn_app (X : Type) P n1 n2 (l1 l2 : list X) :
    Existsn P n1 l1 ->
    Existsn P n2 l2 ->
    Existsn P (n1 + n2) (l1 ++ l2).
  Proof.
    intros H1. revert n2 l2.
    induction H1; intros; simpl; eauto.
  Qed.
  
  Lemma Existsn_split (X : Type) P n (l1 l2 : list X) :
    Existsn P n (l1 ++ l2) ->
    exists n1 n2,
      n = n1 + n2 /\
        Existsn P n1 l1 /\
        Existsn P n2 l2.
  Proof.
    revert n. induction l1; intros n H.
    - simpl in H. exists 0, n. auto.
    - invert H.
      + specialize (IHl1 _ ltac:(eassumption)). fwd. eauto 6.
      + specialize (IHl1 _ ltac:(eassumption)). fwd.
        do 2 eexists. split; [|eauto]. lia.
  Qed.

  From Stdlib Require Import Permutation.
  Lemma Existsn_perm (X : Type) P n (l1 l2 : list X) :
    Existsn P n l1 ->
    Permutation l1 l2 ->
    Existsn P n l2.
  Proof.
    intros H Hperm. revert n H. induction Hperm; intros n H.
    - auto.
    - invert H; eauto.
    - do 2 match goal with
        | H: Existsn _ _ (_ :: _) |- _ => invert H
        end; auto.
    - eauto.
  Qed.

  Lemma Existsn_0_Forall_not U P (l : list U) :
    Existsn P 0 l ->
    Forall (fun x => ~P x) l.
  Proof. induction l; invert 1; auto. Qed.

  Lemma Forall_not_Existsn_0 U P (l : list U) :
    Forall (fun x => ~P x) l ->
    Existsn P 0 l.
  Proof. induction 1; auto. Qed.
  
  Lemma list_set_Existsn_1 U (S : U -> _) l x :
    is_list_set S l ->
    S x ->
    Existsn (eq x) 1 l.
  Proof.
    intros Hls Hx. destruct Hls as [H1 H2].
    apply H1 in Hx. apply in_split in Hx. fwd.
    apply NoDup_remove_2 in H2. rewrite in_app_iff in H2.
    replace 1 with (0 + 1) by lia. apply Existsn_app.
    - apply Forall_not_Existsn_0. apply Forall_forall. intros ? ? ?. subst. auto.
    - apply Existsn_yes; auto.
      apply Forall_not_Existsn_0. apply Forall_forall. intros ? ? ?. subst. auto.
  Qed.

  Lemma Existsn_map U1 U2 P n l (f : U1 -> U2) :
    Existsn P n (map f l) <-> Existsn (fun x => P (f x)) n l.
  Proof.
    revert n. induction l; intros n; simpl; split; invert 1; auto.
    - apply Existsn_no; auto. apply IHl. auto.
    - apply Existsn_yes; auto. apply IHl. auto.
    - apply Existsn_no; auto. apply IHl. auto.
    - apply Existsn_yes; auto. apply IHl. auto.
  Qed.
      
  Lemma Existsn_iff U (P1 P2 : U -> _) n l :
    Existsn P1 n l ->
    (forall x, P1 x <-> P2 x) ->
    Existsn P2 n l.
  Proof.
    intros H1 H2. induction H1; auto.
    - apply Existsn_no; auto. rewrite <- H2. auto.
    - apply Existsn_yes; auto. rewrite <- H2. auto.
  Qed.
      
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
      + intros R. specialize (Hinp_sane R). destruct (is_input R); t.
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
      + intros R. specialize (Hinp_sane R). pose proof rules_good as Hr.
        specialize (Hr n).
        destruct (is_input R) eqn:ER; t.
        exfalso.
        cbv [can_learn_normal_fact_at_node] in Hp1. fwd. destruct r; fwd.
        -- rewrite Forall_forall in Hr. specialize (Hr _ ltac:(eassumption)).
           simpl in Hr. apply Lists.List.Forall_map in Hr. rewrite Forall_forall in Hr.
           apply Exists_exists in Hp1p1p0. fwd. specialize (Hr _ ltac:(eassumption)).
           invert Hp1p1p0p1. congruence.
        -- rewrite Forall_forall in Hr. specialize (Hr _ ltac:(eassumption)).
           simpl in Hr. congruence.
        -- contradiction.
  Qed.

  Definition meta_facts_correct_at_node rules n ns :=
    forall R num,
      In (meta_dfact R (Some n) num) ns.(known_facts) ->
      Forall (fun r =>
                match r with
                | normal_drule concls hyps =>
                    In R (map fact_R concls) ->
                    Forall (fun R' => expect_num_R_facts R' ns.(known_facts) (ns.(msgs_received) R')) (map fact_R hyps)
                | agg_drule _ target_rel source_rel =>
                    R = target_rel ->
                    expect_num_R_facts source_rel ns.(known_facts) (ns.(msgs_received) source_rel)
                | meta_drule _ _ => True
                end)
        rules /\
        (forall args : list T,
            can_learn_normal_fact_at_node rules ns R args ->
            In (normal_dfact R args) (known_facts ns)).

  Definition meta_facts_correct rules g :=
    forall n, meta_facts_correct_at_node (rules n) n (g.(node_states) n).
  
  Lemma fold_left_add_repeat n m q :
    fold_left Nat.add (repeat n m) q = n * m + q.
  Proof.
    revert q. induction m; simpl; try lia.
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
    - rewrite IHtrc.
      + eapply expect_num_R_facts_msgs_received_stable_step; eassumption.
      + eauto using steps_preserves_sanity.
      + erewrite comp_steps_pres_inputs by (eapply TrcFront; eauto). assumption.
      + erewrite expect_num_R_facts_msgs_received_stable_step by eassumption.
        eapply expect_num_R_facts_incl.
        -- eassumption.
        -- eapply step_preserves_known_facts. eassumption.
  Qed.

  Lemma can_learn_normal_fact_at_node_relevant_normal_facts_incl rules0 ns ns' R args :
    can_learn_normal_fact_at_node rules0 ns R args ->
    (forall R' args',
        In (normal_dfact R' args') ns.(known_facts) ->
        Exists (fun r => exists concls hyps,
                    r = normal_drule concls hyps /\
                      In R (map fact_R concls) /\
                      In R' (map fact_R hyps))
               rules0 ->
        In (normal_dfact R' args') ns'.(known_facts)) ->
    (forall R',
        Exists (fun r => exists a, r = agg_drule a R R') rules0 ->
        ns'.(msgs_received) R' = ns.(msgs_received) R' /\
          (forall args',
            In (normal_dfact R' args') ns.(known_facts) <->
            In (normal_dfact R' args') ns'.(known_facts)) /\
          (forall n num,
              In (meta_dfact R' n num) (known_facts ns) ->
              In (meta_dfact R' n num) (known_facts ns'))) ->
    can_learn_normal_fact_at_node rules0 ns' R args.
  Proof.
    intros Hlearn Hnr Har. cbv [can_learn_normal_fact_at_node] in *. fwd.
    eexists. split; [eassumption|]. destruct r; fwd.
    - do 2 eexists. split; [eassumption|]. split; [eassumption|].
      intros R' args' H'. apply Hnr; auto.
      apply Exists_exists. eexists. split; [eassumption|]. simpl.
      apply Exists_exists in Hlearnp1p0. fwd. invert Hlearnp1p0p1.
      do 2 eexists. split; [reflexivity|].
      split.
      { apply in_map. assumption. }
      eapply Forall2_forget_l in Hlearnp1p1. rewrite Forall_forall in Hlearnp1p1.
      specialize (Hlearnp1p1 _ H'). fwd. invert Hlearnp1p1p1. apply in_map.
      assumption.
    - epose_dep Har. specialize' Har.
      { apply Exists_exists. eauto. }
      fwd. split.
      { rewrite Harp0.
        eapply expect_num_R_facts_relevant_mfs_incl; [eassumption|].
        assumption. }
      eexists. split; eauto.
      cbv [is_list_set] in *. fwd. split; auto.
      intros. rewrite <- Harp1. auto.
    - contradiction.
  Qed.

  (* Lemma can_learn_normal_fact_at_node_normal_facts_incl rules0 ns ns' R args : *)
  (*   can_learn_normal_fact_at_node rules0 ns R args -> *)
  (*   (forall R' args', *)
  (*       In (normal_dfact R' args') ns.(known_facts) -> *)
  (*       In (normal_dfact R' args') ns'.(known_facts)) -> *)
  (*   can_learn_normal_fact_at_node rules0 ns' R args. *)
  (* Proof. eauto using can_learn_normal_fact_at_node_relevant_normal_facts_incl. Qed. *)

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
        specialize Hmf with (1 := H'). fwd.
        split.
        -- eapply Forall_impl; [|eassumption].
           simpl. intros r Hr. destruct r; auto.
           ++ intros Hcs.
              specialize (Hr Hcs).
              eapply Forall_impl; [|eassumption].
              simpl. intros R' HR'. destr (rel_eqb nf_rel R').
              2: { eapply expect_num_R_facts_incl; eauto with incl. }
              exfalso.
              eapply expect_num_R_facts_no_travellers with (g := g); try eassumption.
              rewrite H. apply in_app_iff. simpl. eauto.
           ++ intros. subst. specialize (Hr eq_refl).
              destr (rel_eqb nf_rel source_rel).
              2: { eapply expect_num_R_facts_incl; eauto with incl. }
              exfalso.
              eapply expect_num_R_facts_no_travellers with (g := g); try eassumption.
              rewrite H. apply in_app_iff. simpl. eauto.
        -- intros args Hargs. right. apply Hmfp1. move Hmfp0 at bottom.
           eapply can_learn_normal_fact_at_node_relevant_normal_facts_incl; [eassumption| |].
           ++ simpl. intros R' args' [HR'|HR'] Hex; auto. invert HR'. exfalso.
              apply Exists_exists in Hex. rewrite Forall_forall in Hmfp0.
              fwd.
              apply Hmfp0 in Hexp0. specialize (Hexp0 Hexp1p1).
              rewrite Forall_forall in Hexp0.
              specialize (Hexp0 _ Hexp1p2).
              eapply expect_num_R_facts_no_travellers with (g := g); try eassumption.
              rewrite H. apply in_app_iff. simpl. eauto.
           ++ simpl. intros R' Hr. destr (rel_eqb nf_rel R').
              --- exfalso. apply Exists_exists in Hr. fwd.
                  rewrite Forall_forall in Hmfp0. specialize (Hmfp0 _ Hrp0).
                  simpl in Hmfp0. specialize (Hmfp0 eq_refl).
                  eapply expect_num_R_facts_no_travellers with (g := g); try eassumption.
                  rewrite H. apply in_app_iff. simpl. eauto.
              --- split; [reflexivity|]. split.
                  +++ intros. split; auto. intros [?|?]; auto. congruence.
                  +++ intros ? ? [?|?]; auto. congruence.
      + cbv [meta_facts_correct_at_node]. simpl. intros R num [H'|H'].
        2: { pose proof H' as H'0.
             apply Hmf in H'. fwd. split.
             - eapply Forall_impl; [|eassumption].
               simpl. intros r Hr. destruct r; auto.
               + intros.
                 eapply Forall_impl; [|eauto]. simpl.
                 intros. eapply expect_num_R_facts_incl; [eassumption|].
                 auto with incl.
               + intros. subst. specialize (Hr eq_refl).
                 intros. eapply expect_num_R_facts_incl; [eassumption|].
                 auto with incl.
             - intros args Hargs. right. apply H'p1.
               eapply can_learn_normal_fact_at_node_relevant_normal_facts_incl; [eassumption| |].
               + simpl. intros ? ? [?|?]; [congruence|auto].
               + simpl. intros R' HR'. split; auto. split.
                 { intros. split; auto. intros [?|?]; [congruence|auto]. }
                 intros ? ? [H'|?]; auto. invert H'.
                 apply Exists_exists in HR'. fwd.
                 rewrite Forall_forall in H'p0. specialize (H'p0 _ HR'p0).
                 simpl in H'p0. specialize (H'p0 eq_refl).
                 assert (H': forall g R n num,
                            sane_graph g ->
                            knows_fact g (meta_dfact R n num) ->
                            if is_input R then n = None
                            else exists n0, n = Some n0).
                 { admit. }
                 assert (H'': forall g R n num1 num2,
                            sane_graph g ->
                            knows_fact g (meta_dfact R n num1) ->
                            knows_fact g (meta_dfact R n num2) ->
                            num1 = num2).
                 { admit. }
                 epose_dep H'. specialize (H' Hs'). specialize' H'.
                 { cbv [knows_fact]. simpl. right. exists n'.
                   destr (node_eqb n' n'); [|congruence].
                   simpl. left. reflexivity. }
                 cbv [expect_num_R_facts] in H'p0.
                 destruct (is_input R').
                 -- subst. epose_dep H''. specialize (H'' Hs').
                    specialize' H''.
                    { cbv [knows_fact]. simpl. right. exists n'.
                      destr (node_eqb n' n'); [|congruence].
                      simpl. left. reflexivity. }
                    specialize' H''.
                    { right. simpl. exists n'.
                      destr (node_eqb n' n'); [|congruence].
                      simpl. right. eassumption. }
                    subst. assumption.
                 -- fwd.
                    apply Forall2_forget_r in H'p0p0.
                    rewrite Forall_forall in H'p0p0.
                    specialize (H'p0p0 n0).
                    specialize' H'p0p0.
                    { destruct Hall_nodes as [HH _]. apply HH. constructor. }
                    fwd.
                    epose_dep H''. specialize (H'' Hs').
                    specialize' H''.
                    { cbv [knows_fact]. simpl. right. exists n'.
                      destr (node_eqb n' n'); [|congruence].
                      simpl. left. reflexivity. }
                    specialize' H''.
                    { right. simpl. exists n'.
                      destr (node_eqb n' n'); [|congruence].
                      simpl. right. eassumption. }
                    subst. assumption. }
        invert H'.
        cbv [sane_graph] in Hs. destruct Hs as (_&HmfSome&Htrav&_).
        rewrite H in Htrav. epose_dep Htrav.
        rewrite in_app_iff in Htrav. simpl in Htrav.
        specialize (Htrav ltac:(eauto)).
        apply HmfSome in Htrav.
        specialize (Hmf _ _ _ Htrav). fwd. split.
        -- eapply Forall_impl; [|exact Hmfp0].
           simpl. intros r Hr. destruct r; auto.
           ++ intros Hcs. specialize (Hr Hcs).
              eapply Forall_impl; [|exact Hr].
              simpl.
              intros. eapply expect_num_R_facts_incl; [eassumption|].
              auto with incl.
           ++ intros. subst. specialize (Hr eq_refl).
              intros. eapply expect_num_R_facts_incl; [eassumption|].
              auto with incl.
        -- intros args Hargs. right. apply Hmfp1.
           eapply can_learn_normal_fact_at_node_normal_facts_incl; [eassumption|].
           simpl. intros ? ? [?|?]; [congruence|auto].
    - rename H into Hf.
      cbv [meta_facts_correct] in *.
      intros n'. simpl.
      destr (node_eqb n n'); auto.
      destruct f; simpl in *; fwd.
      + pose proof Hmf as Hmf'.
        specialize (Hmf n'). cbv [meta_facts_correct_at_node] in *. simpl.
        intros R num [H'|H']; [discriminate|].
        specialize Hmf with (1 := H'). fwd. split.
        -- eapply Forall_impl; [|eassumption].
           simpl. intros r Hr. destruct r; auto.
           intros Hcs. specialize (Hr Hcs).
           eapply Forall_impl; [|eassumption].
           simpl. intros c Hc.
           eapply expect_num_R_facts_incl; eauto with incl.
        -- intros args Hargs. right. apply Hmfp1. move Hmfp0 at bottom.
           eapply can_learn_normal_fact_at_node_relevant_normal_facts_incl; [eassumption|].
           simpl. intros R' args' [HR'|HR'] Hex; auto. invert HR'.
           apply Exists_exists in Hex. rewrite Forall_forall in Hmfp0.
           fwd. apply Hmfp0 in Hexp0. specialize (Hexp0 Hexp1p0).
           rewrite Forall_forall in Hexp0.
           specialize (Hexp0 _ Hexp1p1).
           move Hmf' at bottom. cbv [expect_num_R_facts] in Hexp0.
           destruct (is_input R') eqn:Ex.
           { exfalso. move Hs' at bottom. cbv [sane_graph] in Hs'. simpl in Hs'.
             destruct Hs' as (_&_&_&_&_&_&Hinp_sane).
             specialize (Hinp_sane R'). rewrite Ex in Hinp_sane.
             specialize (Hinp_sane n'). destr (node_eqb n' n'); [|congruence].
             simpl in Hinp_sane. destr (rel_eqb R' R'); [|congruence].
             discriminate Hinp_sane. }
           fwd. apply Forall2_forget_r in Hexp0p0. rewrite Forall_forall in Hexp0p0.
           specialize (Hexp0p0 n'). specialize' Hexp0p0.
           { destruct Hall_nodes as [H ?]. apply H. constructor. }
           fwd. specialize (Hmf' _ _ _ ltac:(eassumption)). fwd. apply Hmf'p1.
           assumption.
      + cbv [meta_facts_correct_at_node]. simpl. intros R num [H'|H'].
        2: { apply Hmf in H'. fwd. split.
             - eapply Forall_impl; [|eassumption].
               simpl. intros r Hr. destruct r; auto. intros.
               eapply Forall_impl; [|eauto]. simpl.
               intros. eapply expect_num_R_facts_incl; [eassumption|].
               auto with incl.
             - intros args Hargs. right. apply H'p1.
               eapply can_learn_normal_fact_at_node_normal_facts_incl; [eassumption|].
               simpl. intros ? ? [?|?]; [congruence|auto]. }
        invert H'.
        cbv [can_learn_meta_fact_at_node] in Hfp1. fwd. move Hs' at top.
        split.
        -- apply Forall_forall. intros r Hr. destruct r.
           ++ intros HR. pose proof Hfp1p0 as Hfp1p0'.
              cbv [good_layout] in layout_good. destruct layout_good as (Hn&_&_&Hm).
              eassert (In _ _) as Hr'.
              { apply Hn. eexists. eassumption. }
              apply Hm in Hfp1p0'. fwd.
              pose proof prog_good as Hp. cbv [good_prog] in Hp.
              specialize (Hp _ _ _ Hfp1p0').
              specialize Hp with (1 := Hr') (2 := HR).
              rewrite Hn in Hr'. fwd.
              apply Forall_forall.
              intros R' HR'.
              apply Hp in HR'.
              apply Hfp1p1p1 in HR'.
              eapply expect_num_R_facts_incl; [eassumption|].
              auto with incl.
           ++ constructor. (*TODO this will get harder*)
           ++ constructor.
        -- intros args Hargs. right. apply Hfp1p1p2.
           eapply can_learn_normal_fact_at_node_normal_facts_incl; [eassumption|].
           simpl. intros R' args' [H'|H']; [congruence|]. assumption.
  Qed.

  Definition noncyclic_aggregation (p : list rule) :=
    well_founded (fun R1 R2 => exists Rs f, In R2 Rs /\ In (meta_rule R1 f Rs) p).

  Definition rel_edge (rules : Layout) R1 R2 :=
    exists n a, (*In R2 Rs /\*) In (*(meta_drule R1 Rs)*) (agg_drule a R2 R1) (rules n).

  Definition dnoncyclic_aggregation (rules : Layout) :=
    well_founded (rel_edge rules).
  
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
      { eapply Relations.TrcFront. 2: apply Relations.TrcRefl.
        apply ReceiveFact. eassumption. }
      simpl. destr (node_eqb n n); [|congruence].
      apply receive_fact_at_node_receives_facts.
    - exists g. split.
      { apply Relations.TrcRefl. }
      assumption.
  Qed.

  Lemma steps_preserves_known_facts g g' n :
    comp_step^* g g' ->
    incl (g.(node_states) n).(known_facts) (g'.(node_states) n).(known_facts).
  Proof.
    induction 1; auto with incl.
    eapply incl_tran; eauto using step_preserves_known_facts.
    About incl_tran. (*HWY would you call it that*)
  Qed.
    
  Hint Resolve TrcRefl TrcFront : core.
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
      { eapply trc_trans; eassumption. }
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
        { eapply TrcFront.
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
      specialize (Hinp_sane R). rewrite ER in Hinp_sane.
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
    - erewrite comp_steps_pres_inputs by (eapply TrcFront; eauto). assumption.
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
    eauto using Relations.trc_trans.
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
      { eapply Relations.trc_trans; eassumption. }
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
  
  Definition graph_sound_for g R :=
    forall g',
      comp_step^* g g' ->
      good_inputs g'.(input_facts) ->
      forall f,
        rel_of f = R ->
        knows_datalog_fact g' f ->
        prog_impl_implication p (fact_in_inputs g.(input_facts)) f.

  Definition graph_complete_for (g : graph_state) (R : rel) :=
    forall f,
      prog_impl_implication p (fact_in_inputs g.(input_facts)) f ->
      exists g' f',
        comp_step^* g g' /\
          knows_datalog_fact g f'.

  Definition good_meta_rules :=
    forall Q,
      (forall R' S',
          Q (meta_fact R' S') ->
          forall x,
            Q (normal_fact R' x) <-> S' x) ->
      (forall R S,
          prog_impl_implication p Q (meta_fact R S) ->
          forall x,
            prog_impl_implication p Q (normal_fact R x) <-> S x).

  (*requires some hypothesis about the source program: for each rule, for each assignment of facts to hypotheses, we get at most one fact as a conclusion*)
  (*this lemma is very stupid.  should be able to not have th e hypothesis, only conclude the second conjunct about g', and just say that g' has all msgs_received and msgs_sent being the same*)

  Definition same_msgs_received g g' :=
    forall n,
      (g.(node_states) n).(msgs_received) = (g'.(node_states) n).(msgs_received).  

  (*These things should come from datalog/src/Interpreter.v,
    which is currently very far from compiling.*)
  Axiom good_rule : rule -> Prop.
  Axiom step_everybody : list rule -> list fact -> list fact.
  Axiom step_everybody_complete :
    forall p hyps' facts f,
      Forall good_rule p ->
      incl hyps' facts ->
      Exists (fun r => rule_impl r f hyps') p ->
      In f (step_everybody p facts).
  
  (*this should follow from good_prog p + well-foundedness of meta_rule edges*)
  Definition no_R_cycles R (r : rule) :=
    match r with
    | normal_rule concls hyps =>
        In R (map fact_R concls) ->
        In R (map fact_R hyps) ->
        False
    | agg_rule _ _ _ => True (*TODO*)
    | meta_rule _ _ _ => True
    end.  

  Definition add_facts ns fs :=
    {| known_facts := fs ++ ns.(known_facts);
      msgs_received := ns.(msgs_received);
      msgs_sent := ns.(msgs_sent); |}.

  Definition add_facts_at_node g n fs :=
    {| node_states := fun n' => if node_eqb n n' then
                               add_facts (g.(node_states) n) fs
                             else
                               g.(node_states) n;
      travellers := g.(travellers);
      input_facts := g.(input_facts); |}.

  (* Definition normal_dfact_of_fact (f : fact) : option dfact := *)
  (*   match f with *)
  (*   | normal_fact R args => Some (normal_dfact R args) *)
  (*   |  *)
  
  Lemma node_can_find_all_conclusions g n R :
    Forall good_rule p ->
    Forall (no_R_cycles R) p ->
    exists g',
      comp_step^* g g' /\
        (forall args,
            can_learn_normal_fact_at_node (rules n) (node_states g' n) R args ->
            In (normal_dfact R args) (known_facts (node_states g' n))) /\
        same_msgs_received g g'.
  Proof.
    intros Hp Hl.
    (* exists (add_facts_at_node g n (flat_map (fun f => *)
    (*                                       match f with *)
    (*                                       | normal_fact R' args => *)
    (*                                           if rel_eqb R R' then *)
    (*                                             [normal_dfact R' args] *)
    (*                                           else *)
    (*                                             [] *)
    (*                                       | _ => [] *)
    (*                                       end))). *)
  Admitted.

  Lemma good_layout_complete' r hyps g R f :
    good_inputs g.(input_facts) ->
    good_meta_rules ->
    sane_graph g ->
    meta_facts_correct rules g ->
    (forall R', rel_edge rules R' R -> graph_sound_for g R') ->
    Forall (knows_datalog_fact g) hyps ->
    In r p ->
    rule_impl r f hyps ->
    rel_of f = R ->
     exists g',
       comp_step^* g g' /\
         knows_datalog_fact g' f.
  Proof.
    intros Hinp Hmr Hsane Hmf Hrels Hhyps Hr Himpl Hf.
    pose proof layout_good as Hgood.
    pose proof Hgood as Hgood'.
    invert Himpl.
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
          eapply steps_preserves_meta_facts_correct in Hmf; cycle -1.
          { exact Hstep1. }
          all: try eassumption.
          cbv [meta_facts_correct meta_facts_correct_at_node] in Hmf.
          specialize Hmf with (1 := Hor). destruct Hmf as (_&Hmf). eauto. }
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
      eapply knows_datalog_fact_knows_num_R_facts in Hmhyp. fwd.
      pose proof Hmhyp as Hmhyp'.
      eapply node_can_receive_meta_facts in Hmhyp.
      2: { eauto using steps_preserves_sanity. }
      2: { erewrite comp_steps_pres_inputs by eauto. assumption. }
      destruct Hmhyp as (g2&Hg2&Hnum).

      pose proof node_can_receive_expected_facts as Hrcv.
      specialize Hrcv with (g := g2).
      Fail specialize Hrcv with (1 := Hnum). (*hmm*) Print meta_facts_correct_at_node.
      epose_dep Hrcv. specialize' Hrcv.
      { eapply steps_preserves_sanity; eauto using trc_trans. }
      specialize' Hrcv.
      { erewrite comp_steps_pres_inputs. 1: eassumption. eauto using trc_trans. }
      specialize' Hrcv.
      { eapply steps_preserves_knows_there_are_num_R_facts; eauto using trc_trans. }
      specialize (Hrcv Hnum). destruct Hrcv as (g3&Hg3&Hnum').
      
      eenough (Hcan: can_learn_normal_fact_at_node (rules n) (node_states g3 n) _ _).
      { epose proof (Classical_Prop.classic (exists num, In (meta_dfact _ (Some n) num) (known_facts (node_states g3 n)))) as Hor.
        destruct Hor as [Hor|Hor].
        { fwd. exists g3. split; [eauto using Relations.trc_trans|]. simpl. cbv [knows_fact].
          eapply steps_preserves_meta_facts_correct with (g' := g3) in Hmf.
          all: try eassumption.
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
      { rewrite <- Hnum' in *. eapply expect_num_R_facts_incl; [eassumption|].
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
                 Relations.trc comp_step g g' /\
                   (forall n : Node,
                       In n (firstn len all_nodes) ->
                       exists num : nat, knows_fact g' (meta_dfact target_rel (Some n) num))) as H'.
      { specialize (H' (length all_nodes)). rewrite firstn_all in H'. fwd.
        eexists. split; eauto.
        destruct (is_input target_rel).
        { admit. }
        intros n. apply H'p1. destruct Hall_nodes as [H' ?]. apply H'. auto. }
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
      epose_dep Hg2. specialize' Hg2.
      { eauto using steps_preserves_sanity. }
      specialize' Hg2.
      { erewrite comp_steps_pres_inputs by eauto. assumption. }
      specialize (Hg2 ltac:(eassumption)). specialize' Hg2.
      { eapply Forall_impl; [|eassumption].
        intros. eapply comp_steps_preserves_datalog_facts; eassumption. }
      destruct Hg2 as (g2&Hg2&Hhyps2).

      pose proof node_can_find_all_conclusions as Hg3.
      
      specialize (Hg3 g2 n target_rel).
      specialize' Hg3. { admit. }
      specialize' Hg3. { admit. }
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
  Admitted.
    
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
