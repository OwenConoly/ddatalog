From Stdlib Require Import List Bool.
From Datalog Require Import Datalog Tactics.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.
From Stdlib Require Import Lia.
From ATL Require Import Relations. (*TODO i did not actually mean to use trc from here; should i use the stdlib thing instead?*)
From Datalog Require Import List.
From Stdlib Require Import Relations.Relation_Operators.


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
  Context {T_eqb : T -> T -> bool}.
  Context {T_eqb_spec : EqDecider T_eqb}.
  
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
    | meta_drule R _ => is_input R = false
    end.

  Definition good_rules rules :=
    forall (n : Node), Forall drule_good (rules n).
  
  (*we can assume this wlog, since any normal rules violating it are useless*)
  Definition good_prog (p : list rule) :=
    forall R f Rs,
      In (meta_rule R f Rs) p ->
      (forall concls hyps R',
        In (normal_rule concls hyps) p ->
        In R (map fact_R concls) ->
        In R' (map fact_R hyps) ->
        In R' Rs) /\
        (forall a source_rel,
            In (agg_rule a R source_rel) p ->
            In source_rel Rs).

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

  Context (p : list rule) (rules : Node -> list drule).
  Context (rules_good : good_rules rules) (prog_good : good_prog p) (Hlayout : good_layout p rules) (Hgmr : good_meta_rules p).
  
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
      + intros R. specialize (Hinp_sane R). pose proof rules_good as Hr.
        specialize (Hr n).
        destruct (is_input R) eqn:ER; t.
        2: { split; t. intros ?. eapply Hinp_sanep1. t.
             cbv [can_learn_meta_fact_at_node] in Hp1. fwd.
             move rules_good at bottom. cbv [good_rules] in rules_good.
             epose_dep  rules_good. rewrite Forall_forall in rules_good.
             apply rules_good in Hp1p0. simpl in Hp1p0. congruence. }
        split; t.
        2: { intros ?. eapply Hinp_sanep1. t. }
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
  
  (*TODO make this proof less long and terrible*)
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
                 pose proof reasonable_meta_fact_nodes as H'.
                 pose proof mfs_unique as H''.
                 epose_dep H'. specialize (H' Hs' Hinp). specialize' H'.
                 { cbv [knows_fact]. simpl. right. exists n'.
                   destr (node_eqb n' n'); [|congruence].
                   simpl. left. reflexivity. }
                 cbv [expect_num_R_facts] in H'p0.
                 destruct (is_input R').
                 -- subst. epose_dep H''. specialize (H'' Hs' Hinp).
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
                    epose_dep H''. specialize (H'' Hs' Hinp).
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
           eapply can_learn_normal_fact_at_node_relevant_normal_facts_incl; [eassumption| |].
           ++ simpl. intros ? ? [?|?]; [congruence|auto].
           ++ simpl. intros R' HR'. split; auto. split.
              { intros. split; auto. intros [?|?]; [congruence|auto]. }
              intros ? ? [H'|?]; auto. invert H'.
              apply Exists_exists in HR'. fwd.
              rewrite Forall_forall in Hmfp0. specialize (Hmfp0 _ HR'p0).
              simpl in Hmfp0. specialize (Hmfp0 eq_refl).
              pose proof reasonable_meta_fact_nodes as H'.
              pose proof mfs_unique as H''.
              epose_dep H'. specialize (H' Hs' Hinp). specialize' H'.
              { cbv [knows_fact]. simpl. right. exists n'.
                destr (node_eqb n' n'); [|congruence].
                simpl. left. reflexivity. }
              cbv [expect_num_R_facts] in Hmfp0.
              (*why do we know that R' is not an input?*)
              destruct (is_input R'); [congruence|].
              --- fwd.
                  apply Forall2_forget_r in Hmfp0p0.
                  rewrite Forall_forall in Hmfp0p0.
                  specialize (Hmfp0p0 n0).
                  specialize' Hmfp0p0.
                  { destruct Hall_nodes as [HH _]. apply HH. constructor. }
                  fwd.
                  epose_dep H''. specialize (H'' Hs' Hinp).
                  specialize' H''.
                  { cbv [knows_fact]. simpl. right. exists n0.
                    destr (node_eqb n0 n0); [|congruence].
                    simpl. left. reflexivity. }
                  specialize' H''.
                  { right. simpl. exists n0.
                    destr (node_eqb n0 n0); [|congruence].
                    simpl. right. eassumption. }
                  subst. assumption.
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
           ++ intros Hcs. specialize (Hr Hcs).
              eapply Forall_impl; [|exact Hr].
              simpl.
              intros. eapply expect_num_R_facts_incl; [eassumption|].
              auto with incl.
           ++ intros. subst. specialize (Hr eq_refl).
              intros. eapply expect_num_R_facts_incl; [eassumption|].
              auto with incl.
        -- intros args Hargs. right. apply Hmfp1. move Hmfp0 at bottom.
           eapply can_learn_normal_fact_at_node_relevant_normal_facts_incl; [eassumption| |].
           ++ simpl. intros R' args' [HR'|HR'] Hex; auto. invert HR'.
              apply Exists_exists in Hex. rewrite Forall_forall in Hmfp0.
              fwd. apply Hmfp0 in Hexp0. specialize (Hexp0 Hexp1p1).
              rewrite Forall_forall in Hexp0.
              specialize (Hexp0 _ Hexp1p2).
              move Hmf' at bottom. cbv [expect_num_R_facts] in Hexp0.
              destruct (is_input R') eqn:Ex.
              { exfalso. move Hs' at bottom. cbv [sane_graph] in Hs'. simpl in Hs'.
                destruct Hs' as (_&_&_&_&_&_&Hinp_sane).
                specialize (Hinp_sane R'). rewrite Ex in Hinp_sane. fwd.
                specialize (Hinp_sanep0 n'). destr (node_eqb n' n'); [|congruence].
                simpl in Hinp_sanep0. destr (rel_eqb R' R'); [|congruence].
                discriminate Hinp_sanep0. }
              fwd. apply Forall2_forget_r in Hexp0p0. rewrite Forall_forall in Hexp0p0.
              specialize (Hexp0p0 n'). specialize' Hexp0p0.
              { destruct Hall_nodes as [H ?]. apply H. constructor. }
              fwd. specialize (Hmf' _ _ _ ltac:(eassumption)). fwd. apply Hmf'p1.
              assumption.
           ++ simpl. intros R' HR'. ssplit; auto.
              2: { intros ? ? [?|?]; [congruence|auto]. }
              intros args'. split; auto. intros [Hargs'|Hargs']; auto.
              invert Hargs'.
              apply Exists_exists in HR'. rewrite Forall_forall in Hmfp0.
              fwd. apply Hmfp0 in HR'p0. specialize (HR'p0 eq_refl).
              move Hmf' at bottom. cbv [expect_num_R_facts] in HR'p0.
              destruct (is_input R') eqn:Ex.
              { exfalso. move Hs' at bottom. cbv [sane_graph] in Hs'. simpl in Hs'.
                destruct Hs' as (_&_&_&_&_&_&Hinp_sane).
                specialize (Hinp_sane R'). rewrite Ex in Hinp_sane. fwd.
                specialize (Hinp_sanep0 n'). destr (node_eqb n' n'); [|congruence].
                simpl in Hinp_sanep0. destr (rel_eqb R' R'); [|congruence].
                discriminate Hinp_sanep0. }
              fwd. apply Forall2_forget_r in HR'p0p0. rewrite Forall_forall in HR'p0p0.
              specialize (HR'p0p0 n'). specialize' HR'p0p0.
              { destruct Hall_nodes as [H ?]. apply H. constructor. }
              fwd. specialize (Hmf' _ _ _ ltac:(eassumption)). fwd. apply Hmf'p1.
              assumption.
      + cbv [meta_facts_correct_at_node]. simpl. intros R num [H'|H'].
        2: { apply Hmf in H'. fwd. split.
             - eapply Forall_impl; [|eassumption].
               simpl. intros r Hr. destruct r; auto.
               ++ intros Hcs. specialize (Hr Hcs).
                  eapply Forall_impl; [|exact Hr].
                  simpl.
                  intros. eapply expect_num_R_facts_incl; [eassumption|].
                  auto with incl.
               ++ intros. subst. specialize (Hr eq_refl).
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
              pose proof reasonable_meta_fact_nodes as H'.
              pose proof mfs_unique as H''.
              epose_dep H'. specialize (H' Hs' Hinp). specialize' H'.
              { cbv [knows_fact]. simpl. right. exists n'.
                destr (node_eqb n' n'); [|congruence].
                simpl. left. reflexivity. }
              cbv [expect_num_R_facts] in H'p0.
              (*why do we know that R' is not an input?*)
              destruct (is_input R'); [congruence|].
              --- fwd.
                  apply Forall2_forget_r in H'p0p0.
                  rewrite Forall_forall in H'p0p0.
                  specialize (H'p0p0 n0).
                  specialize' H'p0p0.
                  { destruct Hall_nodes as [HH _]. apply HH. constructor. }
                  fwd.
                  epose_dep H''. specialize (H'' Hs' Hinp).
                  specialize' H''.
                  { cbv [knows_fact]. simpl. right. exists n0.
                    destr (node_eqb n0 n0); [|congruence].
                    simpl. left. reflexivity. }
                  specialize' H''.
                  { right. simpl. exists n0.
                    destr (node_eqb n0 n0); [|congruence].
                    simpl. right. eassumption. }
                  subst. assumption. }
        invert H'.
        cbv [can_learn_meta_fact_at_node] in Hfp1. fwd. move Hs' at top.
        split.
        -- apply Forall_forall. intros r Hr. destruct r.
           ++ intros HR. pose proof Hfp1p0 as Hfp1p0'.
              cbv [good_layout] in Hlayout. destruct Hlayout as (Hn&_&_&Hm).
              eassert (In _ _) as Hr'.
              { apply Hn. eexists. eassumption. }
              apply Hm in Hfp1p0'. fwd.
              pose proof prog_good as Hp. cbv [good_prog] in Hp.
              specialize (Hp _ _ _ Hfp1p0'). destruct Hp as (Hp&_).
              specialize Hp with (1 := Hr') (2 := HR).
              rewrite Hn in Hr'. fwd.
              apply Forall_forall.
              intros R' HR'.
              apply Hp in HR'.
              apply Hfp1p1p1 in HR'.
              eapply expect_num_R_facts_incl; [eassumption|].
              auto with incl.
           ++ intros. subst. pose proof Hfp1p0 as Hfp1p0'.
              cbv [good_layout] in Hlayout. destruct Hlayout as (_&Ha&_&Hm).
              eassert (In _ _) as Hr'.
              { apply Ha. eexists. eassumption. }
              apply Hm in Hfp1p0'. fwd.
              pose proof prog_good as Hp. cbv [good_prog] in Hp.
              specialize (Hp _ _ _ Hfp1p0'). destruct Hp as (_&Hp).
              specialize (Hp _ _ ltac:(eassumption)).
              rewrite Ha in Hr'. fwd.
              specialize (Hfp1p1p1 _ Hp).
              eapply expect_num_R_facts_incl; [eassumption|].
              auto with incl.
           ++ constructor.
        -- intros args Hargs. right. apply Hfp1p1p2.
           eapply can_learn_normal_fact_at_node_relevant_normal_facts_incl; [eassumption| |].
           ++ simpl. intros R' args' [H'|H'] ?; [congruence|]. assumption.
           ++ simpl. simpl. intros R' HR'. split; auto. split.
              { intros. split; auto. intros [?|?]; [congruence|auto]. }
              intros ? ? [H'|?]; auto. invert H'.
              apply Exists_exists in HR'. fwd.
              pose proof Hfp1p0 as Hfp1p0'.
              cbv [good_layout] in Hlayout. destruct Hlayout as (_&Ha&_&Hm).
              eassert (In _ _) as Hr'.
              { apply Ha. eexists. eassumption. }
              apply Hm in Hfp1p0'. fwd.
              pose proof prog_good as Hp. cbv [good_prog] in Hp.
              specialize (Hp _ _ _ Hfp1p0'). destruct Hp as (_&Hp).
              specialize (Hp _ _ ltac:(eassumption)).
              rewrite Ha in Hr'. fwd.
              specialize (Hfp1p1p1 _ Hp).
              move Hfp1p1p1 at bottom.
              pose proof reasonable_meta_fact_nodes as H'.
              pose proof mfs_unique as H''.
              epose_dep H'. specialize (H' Hs' Hinp). specialize' H'.
              { cbv [knows_fact]. simpl. right. exists n'.
                destr (node_eqb n' n'); [|congruence].
                simpl. left. reflexivity. }
              cbv [expect_num_R_facts] in Hfp1p1p1.
              (*why do we know that R' is not an input?*)
              destruct (is_input R'); [congruence|].
              --- fwd.
                  apply Forall2_forget_r in Hfp1p1p1p0.
                  rewrite Forall_forall in Hfp1p1p1p0.
                  specialize (Hfp1p1p1p0 n0).
                  specialize' Hfp1p1p1p0.
                  { destruct Hall_nodes as [HH _]. apply HH. constructor. }
                  fwd.
                  epose_dep H''. specialize (H'' Hs' Hinp).
                  specialize' H''.
                  { cbv [knows_fact]. simpl. right. exists n0.
                    destr (node_eqb n0 n0); [|congruence].
                    simpl. left. reflexivity. }
                  specialize' H''.
                  { right. simpl. exists n0.
                    destr (node_eqb n0 n0); [|congruence].
                    simpl. right. eassumption. }
                  subst. assumption.
  Qed.

  Definition noncyclic_aggregation :=
    well_founded (fun R1 R2 => exists Rs f, In R2 Rs /\ In (meta_rule R1 f Rs) p).
  
  Definition rel_edge R1 R2 :=
    exists r, In r p /\
           match r with
           | agg_rule _ R2' R1' => R2' = R2 /\ R1' = R1
           | meta_rule R' _ Rs' => R' = R2 /\ In R1 Rs'
           | normal_rule _ _ => False
           end.
  
  Definition dnoncyclic_aggregation :=
    well_founded rel_edge.
  
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

  Definition consistent g f :=
    match f with
    | normal_fact _ _ => True
    | meta_fact R S' =>
        forall args,
          knows_fact g (normal_dfact R args) <-> S' args
    end.
  
  Definition graph_correct_for g R :=
    (forall f',
        rel_of f' = R ->
        (knows_datalog_fact g f' /\ consistent g f') ->
        prog_impl_implication p (fact_in_inputs g.(input_facts)) f').
  
  Definition graph_sound_for g R :=
    forall g',
      comp_step^* g g' ->
      graph_correct_for g' R.

  Definition graph_relatively_sound_for g R :=
    forall g' g'',
      comp_step^* g g' ->      
      comp_step g' g'' ->
      (forall R0, graph_correct_for g' R0) ->
      graph_correct_for g'' R.

  Definition graph_complete_for (g : graph_state) (R : rel) :=
    forall f,
      rel_of f = R ->
      prog_impl_implication p (fact_in_inputs g.(input_facts)) f ->
      exists g',
        comp_step^* g g' /\
          knows_datalog_fact g' f.

  Notation "R ^+" := (clos_trans _ R) (format "R '^+'").

  Definition is_edge (r : rule) R1 R2 :=
    match r with
    | normal_rule concls hyps => In R2 (map fact_R concls) /\ In R1 (map fact_R hyps)
    | agg_rule _ target_rel source_rel => R2 = target_rel /\ R1 = source_rel
    | meta_rule R _ Rs => R2 = R /\ In R1 Rs
    end.
  
  Definition any_edge R1 R2 :=
    exists r, In r p /\ is_edge r R1 R2.

  Definition rel_edge' R1 R2 :=
    exists R3, rel_edge R1 R3 /\ any_edge^* R3 R2.

  Print trc.

  Inductive trc' {A : Type} (R : A -> A -> Prop) : A -> list A -> A -> Prop :=
  | TrcRefl' x : trc' _ x [] x
  | TrcFront' x y l z :
    R x y ->
    trc' _ y l z ->
    trc' _ x (y :: l) z.

  Definition graph_correct_until g R :=
    forall R0, rel_edge'^+ R0 R -> graph_correct_for g R0.
  
  Definition graph_relatively_complete_for g R :=
    forall f,
      rel_of f = R ->
      prog_impl_implication p (fact_in_inputs (input_facts g)) f ->
      exists l g',
        trc' comp_step g l g' /\
          (graph_correct_until g R ->
           Forall (fun g0 => graph_correct_until g0 R) l ->
           knows_datalog_fact g' f).

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
    (* Forall good_rule p -> *)
    (* Forall (no_R_cycles R) p -> *)
    exists g',
      comp_step^* g g' /\
        (forall args,
            can_learn_normal_fact_at_node (rules n) (node_states g' n) R args ->
            In (normal_dfact R args) (known_facts (node_states g' n))) /\
        same_msgs_received g g'.
  Proof.
    (* intros Hp Hl. *)
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

  Lemma no_learning_inputs g n R args :
    can_learn_normal_fact_at_node (rules n) (node_states g n) R args ->
    is_input R = false.
  Proof.
    intros H. cbv [can_learn_normal_fact_at_node] in H. fwd.
    cbv [good_rules] in rules_good. specialize (rules_good n).
    rewrite Forall_forall in rules_good.
    specialize (rules_good _ ltac:(eassumption)).
    destruct r; fwd; simpl in rules_good.
    - apply Exists_exists in Hp1p0. fwd. invert Hp1p0p1.
      apply Lists.List.Forall_map in rules_good.
      rewrite Forall_forall in rules_good.
      apply rules_good. assumption.
    - assumption.
    - contradiction.
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
    apply IHtrc.
    - eauto using steps_preserves_sanity.
    - eauto using comp_steps_preserves_datalog_facts.
    - assumption.
  Qed.

  Lemma consistent_preserved g g' R S :
    sane_graph g ->
    knows_datalog_fact g (meta_fact R S) ->
    consistent g (meta_fact R S) ->
    comp_step^* g g' ->
    consistent g' (meta_fact R S).
  Proof.
    intros Hs Hk Hc Hstep. cbv [consistent].
    cbv [consistent] in Hc. intros args. rewrite <- Hc. clear Hc.
    split.
    - eauto using knows_meta_fact_steps_learns_nothing.
    - eauto using steps_preserves_facts.
  Qed.    

  Definition set_of fs R :=
    dedup T_eqb (flat_map (fun f =>
                             match f with
                             | normal_dfact R0 [x] => if rel_eqb R R0 then [x] else []
                             | _ => []
                             end) fs).

  Lemma set_of_spec fs R :
    is_list_set (fun x => In (normal_dfact R [x]) fs) (set_of fs R).
  Proof.
    cbv [is_list_set]. split.
    - intros. cbv [set_of]. rewrite <- dedup_preserves_In.
      rewrite in_flat_map. split; intros H.
      + eexists. split; [eassumption|]. simpl. destr (rel_eqb R R); simpl; eauto.
      + fwd. destruct x0; try contradiction.
        destruct nf_args; try contradiction.
        destruct nf_args; try contradiction.
        destr (rel_eqb R nf_rel); try contradiction.
        destruct Hp1; try contradiction.
        subst. assumption.
    - cbv [set_of]. apply NoDup_dedup.
  Qed.

  (*this looks like something that should be proved from the simpler hypothesis that interp_agg a is commutative.  but I'm not particularly attached to the fold_right semantics here, so i won't bother to do that*)
  Context (aggregation_commutative : forall a vals1 vals2 S,
              is_list_set S vals1 ->
              is_list_set S vals2 ->
              fold_right (interp_agg a) (agg_id a) vals1 =
                fold_right (interp_agg a) (agg_id a) vals2).

  Axiom (blah: forall R1 R2, rel_edge R1 R2 -> R1 <> R2).
  
  Lemma good_layout_complete'' r hyps g R f :
    good_inputs g.(input_facts) ->
    sane_graph g ->
    meta_facts_correct rules g ->
    Forall (knows_datalog_fact g) hyps ->
    Forall (consistent g) hyps ->
    In r p ->
    rule_impl r f hyps ->
    rel_of f = R ->
     exists g',
       comp_step^* g g' /\
         ((forall R', rel_edge R' R -> graph_correct_for g' R') ->
          knows_datalog_fact g' f).
  Proof.
    intros Hinp Hsane Hmf Hhyps1 Hhyps2 Hr Himpl Hf.
    pose proof Hlayout as Hgood.
    pose proof Hgood as Hgood'.
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
      intros R' args' H'. rewrite Lists.List.Forall_map in Hhypsg1.
      rewrite Forall_forall in Hhypsg1. apply Hhypsg1 in H'. exact H'.
    - cbv [good_layout] in Hgood. destruct Hgood as (_&Hgood&_).
      apply Hgood in Hr. clear Hgood.
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
      Fail specialize Hrcv with (1 := Hnum). (*hmm*) Print meta_facts_correct_at_node.
      epose_dep Hrcv. specialize' Hrcv.
      { eapply steps_preserves_sanity; eauto using trc_trans. }
      specialize' Hrcv.
      { erewrite comp_steps_pres_inputs. 1: eassumption. eauto using trc_trans. }
      specialize' Hrcv.
      { eapply steps_preserves_knows_there_are_num_R_facts; eauto using trc_trans. }
      specialize (Hrcv Hnum). destruct Hrcv as (g3&Hg3&Hnum').

      eassert (Hcan: can_learn_normal_fact_at_node (rules n) (node_states g3 n) _ _).
      { cbv [can_learn_normal_fact_at_node].
        eexists. split; [eassumption|]. simpl.
        split.
        { rewrite <- Hnum' in *. eapply expect_num_R_facts_incl; [eassumption|].
          eapply steps_preserves_known_facts. eassumption. }
        eexists. split.
        { apply set_of_spec. }
        split; reflexivity. }
      (*   destruct H as (Hp1&Hp2). split. 2: exact Hp2. *)

      assert (H': (forall R', rel_edge R' target_rel -> graph_correct_for g3 R') ->
                    fold_right (interp_agg rule_agg) (agg_id rule_agg) vals =
                      fold_right (interp_agg rule_agg) (agg_id rule_agg) (set_of (g3.(node_states) n).(known_facts) source_rel)).
      { intros Hcor. eapply aggregation_commutative. 2: apply set_of_spec.
        move H at bottom. cbv [is_list_set] in H. fwd. split; [|assumption].
        intros x. split; intros Hx.
        + cbv [graph_correct_for] in Hcor.
          specialize (Hcor source_rel). specialize' Hcor.
          { cbv [rel_edge]. cbv [good_layout] in Hgood'.
          destruct Hgood' as (_&Hgood'&_). eexists. split.
          { apply Hgood'. eauto. }
          simpl. auto. }
          pose proof Hcor as Hcor'.
          specialize (Hcor (normal_fact source_rel [x]) ltac:(reflexivity)).
          specialize' Hcor.
          { simpl. eauto. }
          specialize (Hcor' (meta_fact source_rel S) ltac:(reflexivity)).
          specialize' Hcor'.
          { split.
            - eapply comp_steps_preserves_datalog_facts.
              1: eassumption. eauto using Relations.trc_trans.
            - eapply consistent_preserved; try eassumption. eauto using trc_trans. }
          (*should follow from Hrels plus Hrels'*)
          move Hgmr at bottom.
          apply Hp0.
          cbv [good_meta_rules] in Hgmr. rewrite <- Hgmr. 1,3: eassumption.
          simpl. intros R' S' H' x0. fwd.
          intros. symmetry. apply H'p2.
        + apply Lists.List.Forall_map in Hhyps1. rewrite Forall_forall in Hhyps1.
          specialize (Hhyps1 _ Hx).
          eapply steps_preserves_known_facts. 2: eassumption.
          eauto using Relations.trc_trans. }

      epose proof (Classical_Prop.classic (exists num, In (meta_dfact _ (Some n) num) (known_facts (node_states g3 n)))) as Hor.
      destruct Hor as [Hor|Hor].
      { fwd. exists g3. split; [eauto using Relations.trc_trans|]. simpl. cbv [knows_fact].
        eapply steps_preserves_meta_facts_correct with (g' := g3) in Hmf.
        all: try eassumption.
        2: { eauto using Relations.trc_trans. }
        cbv [meta_facts_correct meta_facts_correct_at_node] in Hmf.
        move Hmf at bottom. epose_dep Hmf. specialize (Hmf Hor).
        intros Hcor. right. eexists. eapply Hmf. rewrite H' by assumption.
        assumption. }
      eassert (Hlast_step: comp_step g3 _).
      { eapply LearnFact with (n := n) (f := normal_dfact _ _).
        simpl. split.
        { eauto. }
        eassumption. }
      eexists. split.
      { (*first, step to a state where node n knows all the hypotheses;
            then, one final step where n deduces the conclusion*)
        eapply Relations.trc_trans.
        { exact Hg1. }
        eapply Relations.trc_trans.
        { exact Hg2. }
        eapply Relations.trc_trans.
        { exact Hg3. }
        eapply TrcFront. 2: apply TrcRefl. eassumption. }
        simpl. cbv [knows_fact]. simpl. right. exists n.
        destr (node_eqb n n); try congruence.
        simpl. rewrite H'. 1: auto. intros.
        admit.
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
        destruct (is_input target_rel) eqn:E.
        { cbv [good_rules] in rules_good.
          specialize (Hgood a_node). specialize (rules_good a_node).
          rewrite Forall_forall in rules_good. apply rules_good in Hgood.
          simpl in Hgood. congruence. }
        intros ? n. apply H'p1. destruct Hall_nodes as [H' ?]. apply H'. auto. }
      intros len. induction len.
      { exists g. split; [apply Relations.TrcRefl|]. simpl. contradiction. }

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
      
      specialize (Hg3 g2 n target_rel).
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
      { apply Hhypsg1 in Hn'. fwd. eexists.
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

  Lemma any_edge_spec (r : rule) f hyps :
    rule_impl r f hyps ->
    Forall (fun R => is_edge r R (rel_of f)) (map rel_of hyps).
  Proof.
    invert 1; simpl in *.
    - apply Exists_exists in H0. fwd. invert H0p1.
      apply Forall_map. apply Forall_map. apply Forall2_forget_l in H1.
      eapply Forall_impl; [|eassumption]. simpl.
      intros [R' args'] H. fwd. invert Hp1. simpl. auto using in_map.
    - constructor; simpl; auto. apply Forall_map. apply Forall_map.
      simpl. apply Forall_forall. auto.
    -  apply Forall_map. apply Forall_zip. eapply Forall2_impl_strong.
       2: { apply Forall2_true. assumption. }
       simpl. auto.
  Qed.

  Lemma graph_sound_for_preserved g R g' :
    graph_sound_for g R ->
    comp_step^* g g' ->
    graph_sound_for g' R.
  Proof.
    intros H Hstep. cbv [graph_sound_for]. intros.
    apply H. eauto using trc_trans.
  Qed.

  Lemma ct_crt (A : Type) R (x y : A) :
    R^+ x y ->
    exists z, R^* x z /\ R z y.
  Proof. induction 1; fwd; eauto using trc_trans. Qed.

  Hint Constructors clos_trans : core.
  Lemma crt_ct' (A : Type) R (x y z : A) :
    R^* x z ->
    R^+ z y ->
    R^+ x y.
  Proof. induction 1; eauto. Qed.

  Lemma crt_ct (A : Type) R (x y z : A) :
    R^* x z ->
    R z y ->
    R^+ x y.
  Proof. induction 1; fwd; eauto using crt_ct'. Qed.
  
  Lemma smth_about_edges R0 R R' :
    any_edge R0 R ->
    rel_edge'^+ R' R0 ->
    rel_edge'^+ R' R.
  Proof.
    intros H1 H2. apply ct_crt in H2. fwd.
    eapply crt_ct. 1: eassumption. clear H2p0.
    cbv [rel_edge'] in *. fwd. eauto using trc_trans.
  Qed.

  Lemma hmfs_unique Q R S S' :
    (forall (R' : rel) (S' : list T -> Prop),
        Q (meta_fact R' S') -> forall x : list T, Q (normal_fact R' x) <-> S' x) -> 
    prog_impl_implication p Q (meta_fact R S) ->
    prog_impl_implication p Q (meta_fact R S') ->
    forall args, S args <-> S' args.
  Proof.
    intros HQ H1 H2 args. cbv [good_meta_rules] in Hgmr.
    eapply Hgmr in H1, H2; try eassumption.
    rewrite <- H1, <- H2. reflexivity.
  Qed.
  
  Lemma sound_impl_consistent g f :
    good_inputs g.(input_facts) ->
    graph_sound_for g (rel_of f) ->
    prog_impl_implication p (fact_in_inputs g.(input_facts)) f ->
    knows_datalog_fact g f ->
    consistent g f.
  Proof.
    intros Hinp Hsound Himpl Hf.
    pose proof Hsound as Hsound'.
    specialize (Hsound g ltac:(eauto)).
    destruct f; simpl.
    { constructor. }
    epose proof (Hsound (meta_fact mf_rel _) ltac:(simpl; reflexivity)) as Hsound.
    specialize' Hsound.
    { split.
      - simpl. exact Hf.
      - simpl. intros. instantiate (1 := fun _ => _). simpl. reflexivity. }
    cbv [good_meta_rules] in Hgmr.
    intros.
    eapply hmfs_unique in Himpl. 3: exact Hsound.
    2: { simpl. intros R' S' H'' x0. fwd. intros. symmetry. apply H''p2. }
    rewrite <- Himpl. reflexivity.
  Qed.

  Lemma trc'_trc {X : Type} (R : X -> _) x l y :
    trc' R x l y ->
    trc R x y.
  Proof. induction 1; eauto. Qed.
  Hint Resolve trc'_trc : core.

  Hint Constructors trc' : core.
  Lemma trc'_trans {X : Type} (R : X -> _) x l1 y l2 z :
    trc' R x l1 y ->
    trc' R y l2 z ->
    trc' R x (l1 ++ l2) z.
  Proof. induction 1; simpl; eauto. Qed.

  Lemma trc'_end {X : Type} (R : X -> _) x l y :
    trc' R x l y ->
    In y (x :: l).
  Proof. induction 1; simpl; eauto. Qed.

  Lemma graph_correct_until_any_edge g R1 R2 :
    any_edge R1 R2 ->
    graph_correct_until g R2 ->
    graph_correct_until g R1.
  Proof.
    intros H1 H2. cbv [graph_correct_until]. intros. apply H2.
    eapply smth_about_edges; eassumption.
  Qed.
  Hint Resolve graph_correct_until_any_edge : core.
  
  Lemma good_layout_complete' g R :
    good_inputs g.(input_facts) ->
    sane_graph g ->
    meta_facts_correct rules g ->
    graph_relatively_complete_for g R.
  Proof.
    intros Hinp Hsane Hmfc.
    cbv [graph_relatively_complete_for].
    intros f Hf H. subst.
    (*it's possible to do this without generalizing g, but i don't want to*)
    remember (fact_in_inputs g.(input_facts)) as Q eqn:E.
    revert g E Hinp Hsane Hmfc. induction H; intros g E Hinp Hsane Hmfc; subst.
    - exists nil, g. eauto using fact_in_inputs_knows_datalog_fact.
    - assert (HR': Forall (fun R => any_edge R (rel_of x)) (map rel_of l)).
      { apply Exists_exists in H. fwd.
        eapply Forall_impl.
        2: { apply any_edge_spec. eassumption. }
        simpl. cbv [any_edge]. eauto. }
      assert (Hg1: exists gs g1, trc' comp_step g gs g1 /\
                             (graph_correct_until g (rel_of x) ->
                              Forall (fun g0 => graph_correct_until g0 (rel_of x)) gs ->
                              Forall (knows_datalog_fact g1) l)).
      { clear H0 H. induction H1.
        - eauto.
        - simpl in HR'. invert HR'. specialize (IHForall ltac:(assumption)).
          fwd. move H at bottom. specialize (H g1).
          specialize' H.
          { erewrite <- comp_steps_pres_inputs with (g := g) (g' := g1) by eauto. reflexivity. }
          specialize' H.
          { erewrite comp_steps_pres_inputs with (g := g) (g' := g1) by eauto. assumption. }
          specialize' H.
          { eauto using steps_preserves_sanity. }
          specialize' H.
          { eauto using steps_preserves_meta_facts_correct. }
          (* specialize' H. *)
          (* { intros R' HR'. eapply graph_sound_for_preserved. 2: eassumption. *)
          (*   apply IHR. eapply smth_about_edges; eassumption. } *)
          destruct H as (gs2&g2&Hstep2&Hg2).
          eexists. eexists. split.
          { eapply trc'_trans.
            { apply IHForallp0. }
            apply Hstep2. }
          intros H1' H2'. apply Forall_app in H2'. fwd.
          constructor.
          -- apply Hg2.
             ++ apply trc'_end in IHForallp0. destruct IHForallp0.
                --- subst. eauto.
                --- rewrite Forall_forall in H2'p0. eauto.
             ++ eapply Forall_impl; [|eassumption]. eauto.
          -- eapply Forall_impl; [|apply IHForallp1].
             ++ eauto using comp_steps_preserves_datalog_facts.
             ++ assumption.
             ++ eauto. }
      clear H1 HR'.
      destruct Hg1 as (gs1&g1&Hstep1&Hg1).
      apply Exists_exists in H. destruct H as (r&Hr1&Hr2).
      pose proof good_layout_complete'' as H'.
      specialize (H' r l g1 (rel_of x) x).
      specialize' H'.
      { erewrite comp_steps_pres_inputs with (g := g) (g' := g1) by eauto. assumption. }
      specialize' H'.
      { eauto using steps_preserves_sanity. }
      specialize' H'.
      { eauto using steps_preserves_meta_facts_correct. }
      (* { intros R' HR'. eapply graph_sound_for_preserved. 2: eassumption. *)
      (*   apply IHR. apply t_step. cbv [rel_edge']. eauto. } *)
      specialize (H' ltac:(assumption)).
      specialize' H'.
      (*this next thing is terrible.  should be a nice way to state something equivalent as a lemma.*)
      { apply Forall_forall. intros f' Hf'. destruct f'; [constructor|].
        assert (Hsmf_rel : graph_sound_for g mf_rel).
        { eapply IHR. simpl. invert Hr2.
          + exfalso. apply in_map_iff in Hf'. fwd. destruct x. congruence.
          + simpl. apply t_step. cbv [rel_edge']. eexists. split.
            -- cbv [rel_edge]. eexists. split; [eassumption|]. simpl.
               destruct Hf' as [Hf'|Hf'].
               ++ invert Hf'. eauto.
               ++ apply in_map_iff in Hf'. fwd. congruence.
            -- auto.
          + simpl. apply t_step. cbv [rel_edge']. eexists. split.
            -- cbv [rel_edge]. eexists. split; [eassumption|]. simpl.
               cbv [zip] in Hf'. apply in_map_iff in Hf'. fwd.
               apply in_combine_l in Hf'p1. eauto.
            -- auto. }
        apply sound_impl_consistent.
        - erewrite comp_steps_pres_inputs by eassumption. assumption.
        - eapply graph_sound_for_preserved. 2: eassumption.
          assumption.
        - rewrite Forall_forall in H0.
          erewrite comp_steps_pres_inputs by eassumption.
          apply H0. assumption.
        - rewrite Forall_forall in Hg1. auto. }
      specialize (H' ltac:(assumption) ltac:(assumption) eq_refl).
      destruct H' as (g2&Hstep2&Hg2). eauto using trc_trans.
  Qed.

  Lemma list_em U (l : list U) P Q :
    Forall (fun x => P x \/ Q x) l ->
    Forall P l \/ Exists Q l.
  Proof.
    induction 1; auto.
    do 2 match goal with | H: _ \/ _ |- _ => destruct H end; auto.
  Qed.

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
  Qed. Search knows_datalog_fact meta_fact.

  Lemma meta_fact_ext (r : rule) R S S' hyps :
    (forall x, S x <-> S' x) ->
    rule_impl r (meta_fact R S) hyps ->
    rule_impl r (meta_fact R S') hyps.
  Proof.
    intros H1 H2. invert H2.
    constructor; auto. intros. rewrite <- H1. auto.
  Qed.

  Lemma good_layout_sound'' g g' R :
    good_inputs g.(input_facts) ->
    sane_graph g ->
    (forall f',
        knows_datalog_fact g f' /\ consistent g f' ->
        prog_impl_implication p (fact_in_inputs g.(input_facts)) f') ->
    graph_relatively_complete_for g' R ->
    (*^note: we only use completeness for normal facts here
      could go like: soundness for smaller rels -> completeness for normal R fact -> soundness for meta R fact -> completeness for meta R fact...
      the only question is, what do i want "completeness" to mean for meta facts?
      i think, as usual, it should not mean any unnecessary things.  so, not consistency.*)
    comp_step g g' ->
    graph_correct_for g' R.
  Proof.
    intros Hinp Hsane Hsound Hrel Hstep f ? (Hf1&Hf2). subst.
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
              { destruct Hlayout as (H'&_). apply H'. eauto. }
              econstructor.
              --- apply Exists_exists. eauto.
              --- eassumption.
           ++ apply Forall_map. apply Forall_forall. intros [R' args'] H'.
              apply Hsound. simpl. eauto 6.
        -- eapply prog_impl_step.
           ++ apply Exists_exists. eexists. split.
              { destruct Hlayout as (_&H'&_). apply H'. eauto. }
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
              destruct Hlayout as (_&_&_&Hl). specialize (Hl _ _ _ ltac:(eassumption)).
              fwd.
              eapply prog_impl_step.
              --- apply Exists_exists. eexists. split; [eassumption|].
                  eenough _ as H'. 1: eapply meta_fact_ext; [|exact H'].
                  2: { eapply meta_rule_impl with (source_sets := map (fun R args => knows_fact g (normal_dfact R args)) source_rels).
                     { rewrite length_map. reflexivity. }
                     intros. reflexivity. }
                  move Hgmr at bottom. cbv [good_meta_rules] in Hgmr.
                  intros args. rewrite <- Hgmr with (S := target_set _).
                  3: { eapply prog_impl_step.
                       { apply Exists_exists. eexists.
                         split; [eassumption|]. eassumption. }
                       apply Forall_zip. apply Forall2_map_r. apply Forall2_same.
                       apply Forall_forall. intros R' HR'.
                       apply Hsound. split.
                       { eapply something_about_expect_num_R_facts; eauto. }
                       simpl. reflexivity. }
                  2: { simpl. intros R' S' H'' x0. fwd.
                       intros. symmetry. apply H''p2. }
                  rewrite <- Hf2. split; intros Hargs.
                  +++ apply Hrel in Hargs; [|reflexivity]. fwd.
                      eapply knows_meta_fact_steps_learns_nothing; eauto.
                      { eauto using step_preserves_sanity. }
                      { simpl. rewrite E. assumption. }
                      apply Hargsp1. admit.
                  +++ apply Hsound. simpl. split; [|constructor].
                      apply only_one_fact_learned in Hargs.
                      destruct Hargs; [assumption|congruence].
              --- apply Forall_zip. apply Forall2_map_r. apply Forall2_same.
                  apply Forall_forall. intros R HR.
                  apply Hsound. split.
                  +++ eapply something_about_expect_num_R_facts; try eassumption. auto.
                  +++ simpl. intros. reflexivity.
                      Unshelve. exact (fun _ => True). (*where did this come from*)
  Admitted.

  Check good_layout_sound''. Check good_layout_complete'.
  Print graph_relatively_complete_for.
  Lemma good_layout_sound' g g' :
    (forall R0, graph_correct_for g R) ->
    graph_relatively_complete_for g R ->
    comp_step g g' ->
    graph_

  (*funny name*)
  Lemma derelativize_soundness g :
    (forall R, graph_correct_for g R) ->
    (forall R, graph_relatively_sound_for g R) ->
    forall R, graph_sound_for g R.
  Proof.
    intros Hinit Hrelative R. cbv [graph_sound_for].
    intros g' Hsteps. induction Hsteps.
    - apply Hinit.
    - apply IHHsteps.
      + intros R0. specialize (Hrelative R0).
        cbv [graph_relatively_sound_for] in Hrelative.
        eapply Hrelative. 3: eassumption. all: auto.
      + intros R0. cbv [graph_relatively_sound_for]. intros.
        eapply Hrelative. 2: exact H1. all: eauto.
  Qed.

  Lemma derelativize_completeness g :
    (forall R, graph_sound_for g R) ->
    (forall R, graph_relatively_complete_for g R) ->
    forall R, graph_complete_for g R.
  Proof.
    intros Hs Hc R. cbv [graph_complete_for].
    intros f ? Hf. subst.
    cbv [graph_relatively_complete_for] in Hc.
    specialize (Hc _ _ eq_refl Hf).
    fwd. eexists. split; [eassumption|]. apply Hcp1.
    intros. apply Hs. assumption.
  Qed.
  
  Lemma good_layout_sound' g R :
    well_founded rel_edge'^+ ->
    good_inputs g.(input_facts) ->
    sane_graph g ->
    meta_facts_correct rules g ->
    graph_relatively_sound_for g R /\ graph_relatively_complete_for g R.
  Proof.
    intros Hwf Hinp Hsane Hmfs. specialize (Hwf R). induction Hwf.
    assert (Hc : graph_relatively_complete_for g x).
    { eapply good_layout_complete'; try assumption.
      intros R' HR'. apply H1 in HR'. fwd. assumption. }
    split; [|assumption].
    cbv [graph_sound_for].
      - assumption.
      - 
    

  Lemma 
  syntax error
End DistributedDatalog.
