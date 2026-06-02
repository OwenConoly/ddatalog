(* Correctness of [EncodeLayout.compile] against the trie-join semantics of [EncodeNode],
   for the *bare-variable* (SuperNice) fragment: every hypothesis/conclusion argument is a
   bare variable [var_expr].  (Function-application arguments in premises/conclusions are not yet
   handled by the compiler -- see EncodeLayout.generate_join / compile_concl -- and are out of
   scope here.)

   The chain is:

     source datalog  --(rename, EncodeLayout)-->  lowered_program
        |  Datalog.prog_impl_fact                     |  EncodeNode.lprog_impl_fact (= Datalog on ids)
        |                                             |  ===  EncodeNode.hw_prog_impl_fact
        +---------------------------------------------+      (this file: per-rule bridge)

   [EncodeNode.hw_prog_correct] already reduces whole-node correctness to the per-rule predicate
   [hw_rule_matches].  This file works toward [hw_rule_matches] for rules the (now fixed)
   [compile_rule] produces, i.e. the *generic-join correctness*: the trie-join query
   [generate_query] admits exactly the variable bindings under which the lowered rule fires. *)

From Datalog Require Import Datalog.
From Stdlib Require Import List Bool ZArith Lia.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Datatypes.Result.
From DatalogRocq Require Import HardwareProgram EncodeLayout EncodeNode ComputableGraph.
From DatalogRocq Require Import DistributedDatalog EncodeDistributed ConnectedTopology.
From DatalogRocq Require Import ForwardingCorrect.

Import ListNotations.

Section EncodeLayoutCorrect.

Context {var aggregator T : Type}.
Context `{sig : signature nat aggregator T}.
Context {context : map.map var T} {context_ok : map.ok context}.
Context {var_eqb : var -> var -> bool}
        {var_eqb_spec : forall x y : var, BoolSpec (x = y) (x <> y) (var_eqb x y)}.
Context {var_idx_map : map.map var nat}.   (* used by compute_permutation *)
Context {var_idx_map_ok : map.ok var_idx_map}.

Notation lowered_fact := (@HardwareProgram.lowered_fact var).
Notation lowered_rule := (@HardwareProgram.lowered_rule var aggregator).
Notation generate_query := (@EncodeLayout.generate_query var var_eqb).
Notation generate_join := (@EncodeLayout.generate_join var var_eqb).
Notation compute_var_order := (@EncodeLayout.compute_var_order var).

(* the tuple of a (normal) ground fact; meta facts (never produced by the bare fragment)
   read as []. *)
Definition nfargs (f : Datalog.fact rel_id T) : list T :=
  match f with Datalog.normal_fact _ a => a | _ => [] end.

(*----Trie-generation facts (toward hooking up compile_rule)----*)

(* [permutation_eqb] reflects list equality; needed to read off [generate_trie]'s output. *)
Lemma permutation_eqb_eq (p1 p2 : list nat) :
  EncodeLayout.permutation_eqb p1 p2 = true -> p1 = p2.
Proof.
  unfold EncodeLayout.permutation_eqb. intros H.
  destruct (Nat.eqb_spec (length p1) (length p2)) as [Hlen|]; [|discriminate].
  revert p2 Hlen H. induction p1 as [|x p1 IH]; intros [|y p2] Hlen H;
    simpl in *; try discriminate; [reflexivity|].
  apply andb_true_iff in H. destruct H as [Hxy Hrest].
  apply Nat.eqb_eq in Hxy. subst y. f_equal. apply IH; [lia | exact Hrest].
Qed.

(*----Reading the compiler's lowered AST as a Datalog program----*)

(* A [lowered_rule] IS a [Datalog] rule over numeric ids ([rel_id]/[fn_id]) at the source's
   [var]/[aggregator] -- exactly the rule the trie-join semantics verifies.  So there is NO
   [lowered -> Datalog] conversion: the compiler emits these rules in their final type, and
   ([EncodeLayout.global_rename_rule]/[compile_rule]) error out on any non-[normal_rule], so a
   lowered program is normal by construction.  A lowered fact/expr likewise IS a [Datalog]
   clause/expr over numeric ids. *)

(* A [normal_rule] fires (env-free, since its conclusion is a [normal_fact]) exactly when some
   context interprets all its hypothesis clauses to [hyps'] and one conclusion clause to [f]. *)
Lemma lrule_impl_iff (concls hyps : list lowered_fact)
    (env : list (Datalog.fact rel_id T) -> rel_id -> list T -> Prop)
    (f : Datalog.fact rel_id T) (hyps' : list (Datalog.fact rel_id T)) :
  rule_impl env (Datalog.normal_rule concls hyps) f hyps' <->
  exists R args ctx,
    f = Datalog.normal_fact R args /\
    Forall2 (interp_clause ctx) hyps hyps' /\
    Exists (fun c => interp_clause ctx c (Datalog.normal_fact R args)) concls.
Proof.
  split.
  - intros H. inversion H; subst.
    match goal with Hn : Datalog.non_meta_rule_impl _ _ _ _ |- _ => inversion Hn; subst end.
    do 3 eexists. split; [reflexivity|]. split; eassumption.
  - intros [R [args [ctx [-> [Hfa Hex]]]]].
    apply Datalog.simple_rule_impl. eapply Datalog.normal_rule_impl; eassumption.
Qed.

(*----The bare-variable fragment----*)

Definition bare_fact (lf : lowered_fact) : Prop :=
  Forall (fun e => exists v, e = var_expr v) lf.(Datalog.clause_args).

(* The compiler only produces [normal_rule]s; a rule is *bare* when all its clause arguments
   are bare variables. *)
Definition bare_rule (lr : lowered_rule) : Prop :=
  match lr with
  | Datalog.normal_rule concls hyps => Forall bare_fact hyps /\ Forall bare_fact concls
  | _ => False
  end.

(* For a bare fact, [compute_var_order] (which drops function args) keeps every argument, so
   its length is the fact's arity and arg positions line up with variable positions. *)
Lemma bare_compute_var_order_length (lf : lowered_fact) :
  bare_fact lf -> length (compute_var_order lf) = length lf.(Datalog.clause_args).
Proof.
  unfold bare_fact, EncodeLayout.compute_var_order. intros H.
  induction lf.(Datalog.clause_args) as [|a args IH]; simpl in *.
  - reflexivity.
  - inversion H as [|x l [v Hv] H']; subst. simpl. rewrite IH; auto.
Qed.

(*----generate_query: shape lemmas (proved)----*)

(* One join per variable in the ordering. *)
Lemma generate_query_length (tb : list trie) (ord : list var) (hyps : list lowered_fact) :
  length (generate_query tb ord hyps) = length ord.
Proof. unfold EncodeLayout.generate_query. apply length_map. Qed.

(* The i-th join is the join for the i-th variable in the ordering (default-free form). *)
Lemma generate_query_nth_error (tb : list trie) (ord : list var)
    (hyps : list lowered_fact) (i : nat) :
  nth_error (generate_query tb ord hyps) i
  = option_map (fun v => generate_join tb v hyps) (nth_error ord i).
Proof. unfold EncodeLayout.generate_query. apply nth_error_map. Qed.

(*----Binding <-> context----*)

(* A binding [vals] over a [NoDup] ordering [ord] induces the datalog context that the lowered
   rule is evaluated under: position [i] in the ordering is variable [nth i ord], holding value
   [nth i vals]. *)
Definition ctx_of (ord : list var) (vals : list T) : option context :=
  map.of_list_zip ord vals.

(* The induced context exists whenever the binding has one value per ordering slot. *)
Lemma ctx_of_exists (ord : list var) (vals : list T) :
  length ord = length vals -> exists ctx, ctx_of ord vals = Some ctx.
Proof.
  intros H. unfold ctx_of, map.of_list_zip.
  apply (map.sameLength_putmany_of_list ord vals map.empty H).
Qed.

(* And it maps the i-th ordering variable to the i-th value (ordering is duplicate-free). *)
Lemma ctx_of_get (ord : list var) (vals : list T) (ctx : context) (i : nat) (v : var) (t : T) :
  NoDup ord ->
  ctx_of ord vals = Some ctx ->
  nth_error ord i = Some v ->
  nth_error vals i = Some t ->
  map.get ctx v = Some t.
Proof.
  intros Hnd Hctx Hi Hv. unfold ctx_of, map.of_list_zip in Hctx.
  eapply (map.putmany_of_list_zip_get_newval
            (key_eqb := var_eqb) (key_eq_dec := var_eqb_spec)); eauto.
Qed.

(*----join_output_fact: projection characterization (proved)----*)

(* The inner fold of [join_output_fact] succeeds with [out] iff every index reads its value. *)
Lemma project_vals_ok (vals : list T) (idxs : list nat) (out : list T) :
  fold_right (fun idx acc =>
    match acc, nth_error vals idx with
    | Some vs, Some v => Some (v :: vs)
    | _, _ => None
    end) (Some []) idxs = Some out
  <-> Forall2 (fun idx v => nth_error vals idx = Some v) idxs out.
Proof.
  revert out. induction idxs as [|idx idxs IH]; intros out; simpl.
  - split; intros H; [injection H as <-; constructor | inversion H; reflexivity].
  - split.
    + intros H.
      destruct (fold_right _ (Some []) idxs) as [vs|] eqn:E;
        destruct (nth_error vals idx) as [v|] eqn:Ev; try discriminate.
      injection H as <-. constructor; [exact Ev | apply IH; reflexivity].
    + intros H. inversion H as [|idx0 v idxs0 out0 Hv Hrest Heq1 Heq2]; subst.
      apply IH in Hrest. rewrite Hrest, Hv. reflexivity.
Qed.

(* Hence the whole [join_output_fact] in terms of the projected tuple. *)
Lemma join_output_fact_spec (vals : list T) (jo : join_output) (f : Datalog.fact rel_id T) :
  join_output_fact vals jo = Some f
  <-> exists out, f = Datalog.normal_fact jo.(output_rel) out /\
                  Forall2 (fun idx v => nth_error vals idx = Some v)
                          jo.(output_var_indices) out.
Proof.
  unfold join_output_fact.
  destruct (fold_right _ (Some []) jo.(output_var_indices)) as [out|] eqn:E.
  - split.
    + intros H; injection H as <-. exists out. split; [reflexivity | apply project_vals_ok; exact E].
    + intros [out' [Hf Hfa]]. apply project_vals_ok in Hfa.
      rewrite Hfa in E. injection E as <-. rewrite Hf. reflexivity.
  - split; [discriminate|].
    intros [out' [Hf Hfa]]. apply project_vals_ok in Hfa. rewrite Hfa in E. discriminate.
Qed.

(*----Conclusion projection: join_output_fact <-> interp_fact (bare concls)----*)

Lemma interp_var_iff (ctx : context) (v : var) (x : T) :
  interp_expr ctx (var_expr v) x <-> map.get ctx v = Some x.
Proof.
  split.
  - intros H; inversion H; subst; assumption.
  - intros H; constructor; assumption.
Qed.

(* The induced context reads the i-th ordering variable as the i-th binding value. *)
Lemma ctx_get_eq_nth (ord : list var) (vals : list T) (ctx : context) (idx : nat) (v : var) :
  NoDup ord -> length ord = length vals -> ctx_of ord vals = Some ctx ->
  nth_error ord idx = Some v ->
  map.get ctx v = nth_error vals idx.
Proof.
  intros Hnd Hlen Hctx Hord.
  assert (Hlt : idx < length ord) by (apply nth_error_Some; congruence).
  destruct (nth_error vals idx) as [t|] eqn:Ev.
  - eapply ctx_of_get; eauto.
  - apply nth_error_None in Ev. lia.
Qed.

(* Bare conclusion args paired with their ordering indices: interpreting the args under the
   induced context yields exactly the values the indices project from the binding. *)
Lemma corr_bridge (ord : list var) (vals : list T) (ctx : context) :
  NoDup ord -> length ord = length vals -> ctx_of ord vals = Some ctx ->
  forall args idxs out,
  Forall2 (fun e idx => exists v, e = var_expr v /\ nth_error ord idx = Some v) args idxs ->
  ( Forall2 (interp_expr ctx) (args) out
    <-> Forall2 (fun idx v => nth_error vals idx = Some v) idxs out ).
Proof.
  intros Hnd Hlen Hctx args idxs out Hcorr. revert out.
  induction Hcorr as [| e idx args idxs [v [He Hov]] Hc IH]; intros out; subst.
  - simpl. split; intros H; inversion H; constructor.
  - simpl. split.
    + intros H. inversion H as [|e0 x args0 out0 Hx Hrest]; subst.
      constructor.
      * apply interp_var_iff in Hx.
        rewrite (ctx_get_eq_nth ord vals ctx idx v Hnd Hlen Hctx Hov) in Hx. exact Hx.
      * apply IH; exact Hrest.
    + intros H. inversion H as [|idx0 x idxs0 out0 Hx Hrest]; subst.
      constructor.
      * apply interp_var_iff.
        rewrite (ctx_get_eq_nth ord vals ctx idx v Hnd Hlen Hctx Hov). exact Hx.
      * apply IH; exact Hrest.
Qed.

(* The conclusion side, fully connected: the trie-join's output equals the lowered rule's
   conclusion fact under the induced context.  [Hcorr] is the structural fact that
   [compile_concl] establishes for bare conclusions (each output index is the ordering
   index of the corresponding variable). *)
Lemma join_output_fact_interp (concl : lowered_fact) (ord : list var) (vals : list T)
    (ctx : context) (jo : join_output) (f : Datalog.fact rel_id T) :
  NoDup ord -> length ord = length vals -> ctx_of ord vals = Some ctx ->
  jo.(output_rel) = concl.(Datalog.clause_rel) ->
  Forall2 (fun e idx => exists v, e = var_expr v /\ nth_error ord idx = Some v)
          concl.(Datalog.clause_args) jo.(output_var_indices) ->
  ( join_output_fact vals jo = Some f <-> interp_clause ctx concl f ).
Proof.
  intros Hnd Hlen Hctx Hrel Hcorr. rewrite join_output_fact_spec. split.
  - intros [out [Hf Hfa]]. exists out. split.
    + apply (corr_bridge ord vals ctx Hnd Hlen Hctx _ _ _ Hcorr). exact Hfa.
    + subst f. rewrite Hrel. reflexivity.
  - intros [args' [Hfa Heq]]. exists args'. split.
    + subst f. rewrite Hrel. reflexivity.
    + apply (corr_bridge ord vals ctx Hnd Hlen Hctx _ _ _ Hcorr). exact Hfa.
Qed.

(*============================================================================*)
(*  compute_permutation is a NoDup permutation list of the right length        *)
(*============================================================================*)

Notation ccount := (@EncodeLayout.count_occ var var_eqb).
Notation cperm_aux := (@EncodeLayout.compute_perm_aux var var_idx_map).
Notation cperm := (@EncodeLayout.compute_permutation var var_eqb var_idx_map).
Notation bbm := (@EncodeLayout.build_base_map var var_eqb var_idx_map).

Definition mget0 (m : var_idx_map) (v : var) : nat :=
  match map.get m v with Some n => n | None => 0 end.

Lemma var_eqb_refl (v : var) : var_eqb v v = true.
Proof. destruct (var_eqb_spec v v); congruence. Qed.

Lemma var_eqb_eq (a b : var) : a = b -> var_eqb a b = true.
Proof. intros ->. apply var_eqb_refl. Qed.

Lemma var_eqb_neq (a b : var) : a <> b -> var_eqb a b = false.
Proof. intros H. destruct (var_eqb_spec a b); congruence. Qed.

(*----count_occ / firstn helpers----*)

Lemma count_occ_cons (q x : var) (l : list var) :
  ccount q (x :: l) = (if var_eqb x q then 1 else 0) + ccount q l.
Proof. reflexivity. Qed.

Lemma count_occ_app (v : var) (l1 l2 : list var) :
  ccount v (l1 ++ l2) = ccount v l1 + ccount v l2.
Proof. induction l1 as [|x l1 IH]; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma firstn_S_nth (l : list var) (i : nat) (d : var) :
  i < length l -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  revert i. induction l as [|x xs IH]; intros i Hi; simpl in *.
  - lia.
  - destruct i as [|i']; simpl; [reflexivity|].
    rewrite (IH i') by lia. reflexivity.
Qed.

Lemma count_occ_firstn_S (v : var) (l : list var) (i : nat) (d : var) :
  i < length l ->
  ccount v (firstn (S i) l) = ccount v (firstn i l) + (if var_eqb (nth i l d) v then 1 else 0).
Proof.
  intros Hi. rewrite (firstn_S_nth l i d Hi), count_occ_app. simpl. lia.
Qed.

Lemma count_firstn_mono (v : var) (l : list var) (i j : nat) :
  i <= j -> ccount v (firstn i l) <= ccount v (firstn j l).
Proof.
  intros Hij. induction Hij as [|j Hij IH]; [lia|].
  destruct (Nat.lt_ge_cases j (length l)) as [Hlt|Hge].
  - rewrite (count_occ_firstn_S v l j v Hlt). lia.
  - rewrite (firstn_all2 (n := S j) l) by lia.
    rewrite (firstn_all2 (n := j) l) in IH by lia. lia.
Qed.

Lemma count_firstn_strict (v : var) (l : list var) (i j : nat) (d : var) :
  i < j -> nth i l d = v -> i < length l ->
  ccount v (firstn i l) < ccount v (firstn j l).
Proof.
  intros Hij Hnth Hi.
  apply Nat.lt_le_trans with (m := ccount v (firstn (S i) l)).
  - rewrite (count_occ_firstn_S v l i d Hi), Hnth, var_eqb_refl. lia.
  - apply count_firstn_mono. lia.
Qed.

(* Occurrence index of position i is strictly below the total count of that variable. *)
Lemma occ_lt_count (v : var) (l : list var) (i : nat) (d : var) :
  i < length l -> nth i l d = v ->
  ccount v (firstn i l) < ccount v l.
Proof.
  intros Hi Hnth.
  assert (H1 : ccount v (firstn (S i) l) = ccount v (firstn i l) + 1).
  { rewrite (count_occ_firstn_S v l i d Hi), Hnth, var_eqb_refl. lia. }
  assert (H2 : ccount v (firstn (S i) l) <= ccount v (firstn (length l) l)).
  { apply count_firstn_mono. lia. }
  rewrite firstn_all in H2. lia.
Qed.

(*----length and value characterization of compute_perm_aux----*)

Lemma cperm_aux_length (l : list var) (bm om : var_idx_map) :
  length (cperm_aux l bm om) = length l.
Proof. revert om. induction l as [|v vs IH]; intros om; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma cperm_aux_cons (v : var) (vs : list var) (bm om : var_idx_map) :
  cperm_aux (v :: vs) bm om
  = (mget0 bm v + mget0 om v) :: cperm_aux vs bm (map.put om v (mget0 om v + 1)).
Proof. reflexivity. Qed.

Lemma mget0_put_same (m : var_idx_map) (v : var) (n : nat) :
  mget0 (map.put m v n) v = n.
Proof. unfold mget0. rewrite map.get_put_same. reflexivity. Qed.

Lemma mget0_put_diff (m : var_idx_map) (v w : var) (n : nat) :
  v <> w -> mget0 (map.put m v n) w = mget0 m w.
Proof. intros H. unfold mget0. rewrite map.get_put_diff by congruence. reflexivity. Qed.

(* nth value produced for position i: base of its variable, plus how many times that variable
   already occurred (in [om] and in the prefix consumed so far). *)
Lemma cperm_aux_nth (bm : var_idx_map) (l : list var) :
  forall (om : var_idx_map) (i : nat) (d : var),
  i < length l ->
  nth i (cperm_aux l bm om) 0 =
    mget0 bm (nth i l d) + mget0 om (nth i l d) + ccount (nth i l d) (firstn i l).
Proof.
  induction l as [|v vs IH]; intros om i d Hi; simpl in Hi; [lia|].
  rewrite cperm_aux_cons. destruct i as [|i'].
  - cbn [nth firstn EncodeLayout.count_occ]. lia.
  - cbn [nth]. rewrite (IH (map.put om v (mget0 om v + 1)) i' d) by lia.
    change (firstn (S i') (v :: vs)) with (v :: firstn i' vs).
    rewrite (count_occ_cons (nth i' vs d) v (firstn i' vs)).
    destruct (var_eqb_spec v (nth i' vs d)) as [Heq|Hne].
    + change (if true then 1 else 0) with 1. rewrite Heq, mget0_put_same. lia.
    + change (if false then 1 else 0) with 0.
      rewrite (mget0_put_diff om v (nth i' vs d) (mget0 om v + 1) Hne). lia.
Qed.

(*----base offsets assigned by build_base_map----*)

(* The offset build_base_map assigns to v's first occurrence in [desired]. *)
Fixpoint base_fn (desired original : list var) (offset : nat) (v : var) : nat :=
  match desired with
  | [] => offset
  | w :: ws => if var_eqb w v then offset
               else base_fn ws original (offset + ccount w original) v
  end.

Lemma base_fn_ge (desired original : list var) (offset : nat) (v : var) :
  offset <= base_fn desired original offset v.
Proof.
  revert offset. induction desired as [|w ws IH]; intros offset; simpl; [lia|].
  destruct (var_eqb w v); [lia|]. specialize (IH (offset + ccount w original)). lia.
Qed.

Lemma bbm_cons (w : var) (ws original : list var) (offset : nat) (m : var_idx_map) :
  bbm (w :: ws) original offset m
  = bbm ws original (offset + ccount w original) (map.put m w offset).
Proof. reflexivity. Qed.

Lemma build_base_map_get_notin (desired original : list var) (offset : nat)
    (m : var_idx_map) (v : var) :
  ~ In v desired -> map.get (bbm desired original offset m) v = map.get m v.
Proof.
  revert offset m. induction desired as [|w ws IH]; intros offset m Hnin; [reflexivity|].
  rewrite bbm_cons, IH by (simpl in Hnin; tauto).
  rewrite map.get_put_diff by (simpl in Hnin; intuition congruence). reflexivity.
Qed.

Lemma build_base_map_get (desired original : list var) (offset : nat)
    (m : var_idx_map) (v : var) :
  NoDup desired -> In v desired ->
  map.get (bbm desired original offset m) v = Some (base_fn desired original offset v).
Proof.
  revert offset m. induction desired as [|w ws IH]; intros offset m Hnd Hin;
    simpl in Hin; [contradiction|].
  rewrite bbm_cons. inversion Hnd as [|x l Hwnin Hnd' Heqd]; subst.
  cbn [base_fn]. destruct (var_eqb_spec w v) as [Heq|Hne].
  - subst w. rewrite build_base_map_get_notin by exact Hwnin.
    rewrite map.get_put_same. reflexivity.
  - destruct Hin as [Hwv|Hin']; [congruence|]. apply IH; assumption.
Qed.

(* Distinct variables get disjoint blocks [base, base+count): one block lies entirely below
   the other. *)
Lemma base_fn_mono (desired original : list var) (offset : nat) (v w : var) :
  NoDup desired -> In v desired -> In w desired -> v <> w ->
  base_fn desired original offset v + ccount v original <= base_fn desired original offset w
  \/ base_fn desired original offset w + ccount w original <= base_fn desired original offset v.
Proof.
  revert offset. induction desired as [|u us IH]; intros offset Hnd Hv Hw Hvw;
    simpl in Hv, Hw; [contradiction|].
  inversion Hnd as [|x l Hunin Hnd' Heqd]; subst.
  cbn [base_fn].
  destruct (var_eqb_spec u v) as [Huv|Huv]; destruct (var_eqb_spec u w) as [Huw|Huw].
  - congruence.
  - subst u. destruct Hw as [Hwv|Hwin]; [congruence|].
    left. pose proof (base_fn_ge us original (offset + ccount v original) w). lia.
  - subst u. destruct Hv as [Hvu|Hvin]; [congruence|].
    right. pose proof (base_fn_ge us original (offset + ccount w original) v). lia.
  - destruct Hv as [Hvu|Hvin]; [congruence|]. destruct Hw as [Hwu|Hwin]; [congruence|].
    apply (IH (offset + ccount u original) Hnd' Hvin Hwin Hvw).
Qed.

(*----compute_permutation: length, value, NoDup----*)

Lemma mget0_empty (v : var) : mget0 map.empty v = 0.
Proof. unfold mget0. rewrite map.get_empty. reflexivity. Qed.

Lemma compute_permutation_length (original desired : list var) :
  length (cperm original desired) = length original.
Proof. unfold EncodeLayout.compute_permutation. apply cperm_aux_length. Qed.

Lemma compute_permutation_nth (original desired : list var) (i : nat) (d : var) :
  i < length original ->
  nth i (cperm original desired) 0 =
    mget0 (bbm desired original 0 map.empty) (nth i original d)
      + ccount (nth i original d) (firstn i original).
Proof.
  intros Hi. unfold EncodeLayout.compute_permutation.
  rewrite (cperm_aux_nth (bbm desired original 0 map.empty) original map.empty i d Hi).
  rewrite mget0_empty. lia.
Qed.

(* The value at position i is [base(vi) + occ_i] with [occ_i < count vi]; distinct positions
   thus get distinct values. *)
Lemma cperm_val_neq (original desired : list var) (d : var) (i j : nat) :
  NoDup desired -> (forall v, In v original -> In v desired) ->
  i < j -> j < length original ->
  nth i (cperm original desired) 0 <> nth j (cperm original desired) 0.
Proof.
  intros Hnd Hcov Hij Hj.
  assert (Hi : i < length original) by lia.
  pose (vi := nth i original d). pose (vj := nth j original d).
  assert (Hivd : In vi desired) by (apply Hcov; apply nth_In; lia).
  assert (Hjvd : In vj desired) by (apply Hcov; apply nth_In; lia).
  rewrite (compute_permutation_nth original desired i d Hi).
  rewrite (compute_permutation_nth original desired j d Hj).
  fold vi vj.
  assert (Hbi : mget0 (bbm desired original 0 map.empty) vi = base_fn desired original 0 vi)
    by (unfold mget0; rewrite (build_base_map_get desired original 0 map.empty vi Hnd Hivd); reflexivity).
  assert (Hbj : mget0 (bbm desired original 0 map.empty) vj = base_fn desired original 0 vj)
    by (unfold mget0; rewrite (build_base_map_get desired original 0 map.empty vj Hnd Hjvd); reflexivity).
  rewrite Hbi, Hbj.
  pose proof (occ_lt_count vi original i d Hi eq_refl) as Hoi.
  pose proof (occ_lt_count vj original j d Hj eq_refl) as Hoj.
  destruct (var_eqb_spec vi vj) as [Hvv|Hvv].
  - (* same variable: strict growth of occurrence count *)
    rewrite <- Hvv.
    pose proof (count_firstn_strict vi original i j d Hij eq_refl Hi) as Hgrow. lia.
  - destruct (base_fn_mono desired original 0 vi vj Hnd Hivd Hjvd Hvv) as [Hle|Hle]; lia.
Qed.

Lemma compute_permutation_NoDup (original desired : list var) :
  NoDup desired -> (forall v, In v original -> In v desired) ->
  NoDup (cperm original desired).
Proof.
  intros Hnd Hcov. destruct original as [|d0 orig'] eqn:Eo.
  - unfold EncodeLayout.compute_permutation. simpl. constructor.
  - apply (proj2 (NoDup_nth (cperm (d0 :: orig') desired) 0)).
    intros i j Hi Hj Heq.
    rewrite compute_permutation_length in Hi, Hj.
    destruct (Nat.lt_trichotomy i j) as [Hlt|[Heqij|Hgt]].
    + exfalso. exact (cperm_val_neq (d0 :: orig') desired d0 i j Hnd Hcov Hlt Hj Heq).
    + exact Heqij.
    + exfalso. exact (cperm_val_neq (d0 :: orig') desired d0 j i Hnd Hcov Hgt Hi (eq_sym Heq)).
Qed.

(*============================================================================*)
(*  Characterizing generate_join's entry list                                  *)
(*============================================================================*)

Lemma zip3_app {A B C : Type} (a1 a2 : list A) (b1 b2 : list B) (c1 c2 : list C) :
  length a1 = length b1 -> length a1 = length c1 ->
  zip3 (a1 ++ a2) (b1 ++ b2) (c1 ++ c2) = zip3 a1 b1 c1 ++ zip3 a2 b2 c2.
Proof.
  revert b1 c1. induction a1 as [|x a1 IH]; intros b1 c1 Hb Hc.
  - destruct b1; [|discriminate]. destruct c1; [|discriminate]. reflexivity.
  - destruct b1 as [|y b1]; [discriminate|]. destruct c1 as [|z c1]; [discriminate|].
    simpl. rewrite IH by (simpl in *; lia). reflexivity.
Qed.

(* The inner fold over a hypothesis's argument positions: pushes one (tid, level, clause)
   per position, newest first. *)
Lemma inner_fold_spec (t : trie) (clause : nat) (idxs : list nat) (ts levels cs : list nat) :
  fold_left (fun (inner_acc : list nat * list nat * list nat) (arg_idx : nat) =>
               let '(ts', levels', cs') := inner_acc in
               (t.(tid) :: ts', nth arg_idx t.(tperm) 0 :: levels', clause :: cs'))
            idxs (ts, levels, cs)
  = (rev (map (fun _ : nat => t.(tid)) idxs) ++ ts,
     rev (map (fun a : nat => nth a t.(tperm) 0) idxs) ++ levels,
     rev (map (fun _ : nat => clause) idxs) ++ cs).
Proof.
  revert ts levels cs. induction idxs as [|a idxs IH]; intros ts levels cs; [reflexivity|].
  simpl. rewrite IH. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma zip3_map3 {A X Y Z : Type} (f : A -> X) (g : A -> Y) (h : A -> Z) (l : list A) :
  zip3 (map f l) (map g l) (map h l) = map (fun a => (f a, g a, h a)) l.
Proof. induction l as [|x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(* The flat list of entries generate_join produces (forward order). *)
Definition gj_entries (tb : list trie) (v : var) (hyps : list lowered_fact)
  : list (trie_id * nat * clause_id) :=
  flat_map (fun ci => let '(c, t_hyp) := ci in let '(t, hyp) := t_hyp in
              map (fun a => (t.(tid), nth a t.(tperm) 0, c))
                  (get_hyp_arg_indices (var_eqb := var_eqb) hyp.(Datalog.clause_args) v 0))
           (combine (seq 0 (length (combine tb hyps))) (combine tb hyps)).

(* The outer fold over (trie, hypothesis) pairs, tracking the clause counter. *)
Lemma outer_fold_spec (v : var) (pairs : list (trie * lowered_fact)) :
  forall (clause0 : nat) (ts levels cs : list nat),
  length ts = length levels -> length levels = length cs ->
  match fold_left (fun (acc : list nat * list nat * list nat * nat) (pair : trie * lowered_fact) =>
      let '(ts, levels, cs, clause) := acc in
      let '(t, hyp) := pair in
      let '(ts', levels', cs') :=
        fold_left (fun (inner_acc : list nat * list nat * list nat) (arg_idx : nat) =>
          let '(ts', levels', cs') := inner_acc in
          (t.(tid) :: ts', nth arg_idx t.(tperm) 0 :: levels', clause :: cs'))
          (get_hyp_arg_indices (var_eqb := var_eqb) hyp.(Datalog.clause_args) v 0) (ts, levels, cs) in
      (ts', levels', cs', S clause))
      pairs (ts, levels, cs, clause0)
  with (ts', levels', cs', _) =>
    length ts' = length levels' /\ length levels' = length cs' /\
    zip3 (rev ts') (rev levels') (rev cs')
      = zip3 (rev ts) (rev levels) (rev cs)
        ++ flat_map (fun ci => let '(c, t_hyp) := ci in let '(t, hyp) := t_hyp in
                map (fun a => (t.(tid), nth a t.(tperm) 0, c))
                    (get_hyp_arg_indices (var_eqb := var_eqb) hyp.(Datalog.clause_args) v 0))
             (combine (seq clause0 (length pairs)) pairs)
  end.
Proof.
  induction pairs as [|[t hyp] pairs IH]; intros clause0 ts levels cs Hl1 Hl2.
  - simpl. rewrite app_nil_r. auto.
  - cbn [fold_left]. rewrite inner_fold_spec.
    set (idxs := get_hyp_arg_indices (var_eqb := var_eqb) hyp.(Datalog.clause_args) v 0).
    assert (HpA : length (rev (map (fun _ : nat => t.(tid)) idxs) ++ ts)
                = length (rev (map (fun a : nat => nth a t.(tperm) 0) idxs) ++ levels))
      by (rewrite !length_app, !length_rev, !length_map; f_equal; exact Hl1).
    assert (HpB : length (rev (map (fun a : nat => nth a t.(tperm) 0) idxs) ++ levels)
                = length (rev (map (fun _ : nat => clause0) idxs) ++ cs))
      by (rewrite !length_app, !length_rev, !length_map; f_equal; exact Hl2).
    specialize (IH (S clause0) _ _ _ HpA HpB).
    destruct (fold_left _ pairs _) as [[[ts' levels'] cs'] clause'].
    destruct IH as [HL1 [HL2 Hz]].
    split; [exact HL1|]. split; [exact HL2|].
    rewrite Hz, !rev_app_distr, !rev_involutive.
    rewrite (zip3_app (rev ts) _ (rev levels) _ (rev cs)) by (rewrite !length_rev; lia).
    rewrite zip3_map3. rewrite <- app_assoc. f_equal.
Qed.

Lemma generate_join_entries (tb : list trie) (v : var) (hyps : list lowered_fact) :
  zip3 (generate_join tb v hyps).(HardwareProgram.tries)
       (generate_join tb v hyps).(trie_levels)
       (generate_join tb v hyps).(clauses)
  = gj_entries tb v hyps.
Proof.
  unfold EncodeLayout.generate_join, gj_entries.
  pose proof (outer_fold_spec v (combine tb hyps) 0 [] [] [] eq_refl eq_refl) as H.
  destruct (fold_left _ (combine tb hyps) _) as [[[ts' levels'] cs'] clause'].
  destruct H as [_ [_ Hz]]. simpl. exact Hz.
Qed.

(*----helpers for the generic-join correctness----*)

Lemma Forall2_nth_error_iff {A B : Type} (P : A -> B -> Prop) (l1 : list A) (l2 : list B) :
  Forall2 P l1 l2 <->
  (length l1 = length l2 /\
   forall i x y, nth_error l1 i = Some x -> nth_error l2 i = Some y -> P x y).
Proof.
  split.
  - intros H. induction H as [|x y l1 l2 Hxy HF IH].
    + split; [reflexivity|]. intros [|i]; discriminate.
    + destruct IH as [Hlen IHn]. split; [simpl; congruence|].
      intros [|i] x0 y0; simpl; intros Hx Hy.
      * injection Hx as <-. injection Hy as <-. exact Hxy.
      * eapply IHn; eauto.
  - revert l2. induction l1 as [|x l1 IH]; intros l2 [Hlen Hn].
    + destruct l2; [constructor | discriminate].
    + destruct l2 as [|y l2]; [discriminate|]. constructor.
      * apply (Hn 0 x y); reflexivity.
      * apply IH. split; [simpl in Hlen; congruence|].
        intros i x0 y0 Hx Hy. apply (Hn (S i) x0 y0); assumption.
Qed.

(* Membership in an "enumerate": [combine (seq s n) l] with [n = length l]. *)
Lemma In_combine_seq {A : Type} (l : list A) (s c : nat) (x : A) :
  In (c, x) (combine (seq s (length l)) l) <->
  (exists k, c = s + k /\ nth_error l k = Some x).
Proof.
  revert s. induction l as [|a l IH]; intros s; simpl.
  - split; [contradiction|]. intros [k [_ Hk]]. destruct k; discriminate.
  - split.
    + intros [Heq | Hin].
      * inversion Heq; subst. exists 0. split; [lia | reflexivity].
      * apply IH in Hin. destruct Hin as [k [-> Hk]]. exists (S k). split; [lia | exact Hk].
    + intros [k [-> Hk]]. destruct k as [|k]; simpl in Hk.
      * injection Hk as <-. left. f_equal; lia.
      * right. apply IH. exists k. split; [lia | exact Hk].
Qed.

(* Membership in the argument-position list. *)
Lemma get_hyp_arg_indices_In
    (args : list (@HardwareProgram.lowered_expr var)) (v : var) (i a : nat) :
  In a (EncodeLayout.get_hyp_arg_indices (var_eqb := var_eqb) args v i) <->
  (exists k, a = i + k /\ nth_error args k = Some (var_expr v)).
Proof.
  revert i. induction args as [|arg args IH]; intros i; simpl.
  - split; [contradiction|]. intros [k [_ Hk]]. destruct k; discriminate.
  - destruct arg as [v' | f l].
    + destruct (var_eqb_spec v v') as [Heqv | Hne].
      * subst v'. split.
        -- intros [-> | Hin].
           ++ exists 0. split; [lia | reflexivity].
           ++ apply IH in Hin. destruct Hin as [k [-> Hk]]. exists (S k). split; [lia | exact Hk].
        -- intros [k [Hak Hk]]. destruct k as [|k]; simpl in Hk.
           ++ left; lia.
           ++ right. apply IH. exists k. split; [lia | exact Hk].
      * split.
        -- intros Hin. apply IH in Hin. destruct Hin as [k [-> Hk]]. exists (S k). split; [lia | exact Hk].
        -- intros [k [Hak Hk]]. destruct k as [|k]; simpl in Hk.
           ++ injection Hk as <-. congruence.
           ++ apply IH. exists k. split; [lia | exact Hk].
    + split.
      * intros Hin. apply IH in Hin. destruct Hin as [k [-> Hk]]. exists (S k). split; [lia | exact Hk].
      * intros [k [Hak Hk]]. destruct k as [|k]; simpl in Hk.
        -- discriminate.
        -- apply IH. exists k. split; [lia | exact Hk].
Qed.

(* Membership in generate_join's entry list. *)
Lemma gj_entries_In (tb : list trie) (v : var) (hyps : list lowered_fact)
    (e : trie_id * nat * clause_id) :
  In e (gj_entries tb v hyps) <->
  (exists c t hyp a,
     nth_error (combine tb hyps) c = Some (t, hyp) /\
     nth_error hyp.(Datalog.clause_args) a = Some (var_expr v) /\
     e = (t.(tid), nth a t.(tperm) 0, c)).
Proof.
  unfold gj_entries. rewrite in_flat_map. split.
  - intros [[c [t hyp]] [Hin Hin2]].
    apply In_combine_seq in Hin. destruct Hin as [k [Hck Hk]]. simpl in Hck; subst c.
    apply in_map_iff in Hin2. destruct Hin2 as [a [He Ha]].
    apply (get_hyp_arg_indices_In hyp.(Datalog.clause_args) v 0 a) in Ha.
    destruct Ha as [a' [-> Ha']]. rewrite Nat.add_0_l in He.
    exists k, t, hyp, a'. split; [exact Hk | split; [exact Ha' | symmetry; exact He]].
  - intros [c [t [hyp [a [Hk [Ha ->]]]]]].
    exists (c, (t, hyp)). split.
    + apply In_combine_seq. exists c. split; [lia | exact Hk].
    + apply in_map_iff. exists a. split; [reflexivity|].
      apply (get_hyp_arg_indices_In hyp.(Datalog.clause_args) v 0 a). exists a. split; [lia | exact Ha].
Qed.

(* Reading a lowered fact as a datalog fact, factored. *)
Lemma interp_lfact_iff (ctx : context) (lf : lowered_fact) (R : rel_id) (tup : list T) :
  interp_clause ctx lf (Datalog.normal_fact R tup) <->
  R = lf.(Datalog.clause_rel) /\ Forall2 (interp_expr ctx) (lf.(Datalog.clause_args)) tup.
Proof.
  split.
  - intros [nf_args [HF Heq]]. injection Heq as HR Htup. subst. split; [reflexivity | assumption].
  - intros [HR HF]. subst R. exists tup. split; [exact HF | reflexivity].
Qed.

(* For bare args, the per-position interpretation condition. *)
Lemma bare_interp_args_iff (ctx : context)
    (args : list (@HardwareProgram.lowered_expr var)) (tup : list T) :
  Forall (fun e => exists v, e = var_expr v) args ->
  ( Forall2 (interp_expr ctx) (args) tup <->
    (length args = length tup /\
     forall a w, nth_error args a = Some (var_expr w) -> nth_error tup a = map.get ctx w) ).
Proof.
  intros Hbare. rewrite Forall2_nth_error_iff. split.
  - intros [Hlen Hpt]. split; [exact Hlen|]. intros a w Haw.
    assert (Hargs : a < length args).
    { apply (proj1 (nth_error_Some args a)). rewrite Haw. discriminate. }
    assert (Hat : nth_error tup a <> None).
    { apply (proj2 (nth_error_Some tup a)). rewrite <- Hlen. exact Hargs. }
    destruct (nth_error tup a) as [y|] eqn:Hy; [|congruence].
    specialize (Hpt a _ _ Haw Hy). apply interp_var_iff in Hpt. symmetry; exact Hpt.
  - intros [Hlen Hpt]. split; [exact Hlen|]. intros a arg y Earg Hy.
    assert (Hw : exists w, arg = var_expr w)
      by (rewrite Forall_forall in Hbare; apply Hbare; eapply nth_error_In; exact Earg).
    destruct Hw as [w ->]. apply interp_var_iff.
    specialize (Hpt a w Earg). rewrite Hy in Hpt. symmetry; exact Hpt.
Qed.

(*============================================================================*)
(*  Core obligation: generic-join correctness (bare fragment)                 *)
(*============================================================================*)

(* The trie-join [generate_query tb ord hyps] admits binding [vals] (against the global trie
   table [tries] and hypothesis tuples [hyps']) exactly when the induced context interprets
   every (renamed) hypothesis to the corresponding tuple.

   Structural preconditions [Htb] capture what the *fixed* [compile_hyps] guarantees: the i-th
   per-hyp trie indexes the i-th hypothesis's relation with the permutation computed for that
   hypothesis, and is registered in the table.  This is the heart of the proof; the index
   bookkeeping is discharged by [trie_read_NoDup] (already proved in EncodeNode) once the
   permutation is shown to be [NoDup].

   Proof sketch (both directions):
   - (->) Given satisfying [vals], take [ctx := ctx_of ord vals].  For hypothesis i with bare
     args, [join_sat] for each variable position forces [nth (pos of v in ord) vals] to equal
     [trie_read tperm_i tup_i level]; [trie_read_NoDup] rewrites that to [nth_error tup_i argpos],
     which is exactly [interp_expr ctx (var_expr v)].  Assemble [interp_fact ctx (h_i) (..)].
   - (<-) Given [ctx] interpreting all hyps, read [vals := map (ctx) ord]; each join entry reads
     back the matching tuple column by the same [trie_read_NoDup] identity. *)
Theorem generate_query_correct
    (ord : list var) (hyps : list lowered_fact) (tb : list trie) (tries : list trie)
    (vals : list T) (hyps' : list (Datalog.fact rel_id T)) (dt : trie) (dh : lowered_fact) :
  NoDup ord ->
  Forall bare_fact hyps ->
  length tb = length hyps ->
  length hyps' = length hyps ->
  length vals = length ord ->
  (forall v, In v (flat_map compute_var_order hyps) -> In v ord) ->
  (forall i, i < length hyps ->
     (nth i tb dt).(trel) = (nth i hyps dh).(Datalog.clause_rel) /\
     (nth i tb dt).(tperm) = EncodeLayout.compute_permutation (var_eqb := var_eqb)
                                (compute_var_order (nth i hyps dh)) ord /\
     lookup_trie tries (nth i tb dt).(tid) = Some (nth i tb dt) /\
     exists tup, nth i hyps' (Datalog.normal_fact 0 []) =
                   Datalog.normal_fact (nth i hyps dh).(Datalog.clause_rel) tup /\
                 length tup = length (nth i hyps dh).(Datalog.clause_args)) ->
  ( query_sat tries (generate_query tb ord hyps) vals hyps'
    <-> exists ctx, ctx_of ord vals = Some ctx /\
                    Forall2 (interp_clause ctx) (hyps) hyps' ).
Proof.
  intros Hnd Hbare Htbl Hhl Hvl Hcov Hstruct.
  destruct (ctx_of_exists ord vals (eq_sym Hvl)) as [ctx Hctx].
  assert (Hcomb : forall c, c < length hyps ->
            nth_error (combine tb hyps) c = Some (nth c tb dt, nth c hyps dh)).
  { intros c Hc. rewrite (nth_error_nth' _ (dt, dh)) by (rewrite length_combine; lia).
    rewrite combine_nth by lia. reflexivity. }
  assert (Hcombinv : forall c t hyp, nth_error (combine tb hyps) c = Some (t, hyp) ->
            c < length hyps /\ t = nth c tb dt /\ hyp = nth c hyps dh).
  { intros c t hyp H. assert (Hc : c < length hyps).
    { assert (Hne : nth_error (combine tb hyps) c <> None) by (rewrite H; discriminate).
      apply nth_error_Some in Hne. rewrite length_combine in Hne. lia. }
    rewrite Hcomb in H by lia. injection H as <- <-. auto. }
  (* per-(c,a) bridge: a join entry holds iff the c-th tuple's a-th column is the value *)
  assert (Hentry : forall c a w u tupc,
            c < length hyps ->
            nth c hyps' (Datalog.normal_fact 0 []) =
              Datalog.normal_fact (nth c hyps dh).(Datalog.clause_rel) tupc ->
            nth_error (nth c hyps dh).(Datalog.clause_args) a = Some (var_expr w) ->
            ( join_entry_sat tries hyps' u ((nth c tb dt).(tid), nth a (nth c tb dt).(tperm) 0, c)
              <-> nth_error tupc a = Some u )).
  { intros c a w u tupc Hc Hnf Haw.
    destruct (Hstruct c Hc) as [Htrel [Htperm [Hlook [tup0 [Hnf0 Hltup]]]]].
    rewrite Hnf0 in Hnf. injection Hnf as Htup. subst tup0.
    assert (Hbarec : bare_fact (nth c hyps dh))
      by (rewrite Forall_forall in Hbare; apply Hbare; apply nth_In; lia).
    assert (Hnodupp : NoDup (nth c tb dt).(tperm)).
    { rewrite Htperm. apply compute_permutation_NoDup; [exact Hnd|].
      intros v Hv. apply Hcov, in_flat_map.
      exists (nth c hyps dh). split; [apply nth_In; lia | exact Hv]. }
    assert (Halt : a < length (nth c hyps dh).(Datalog.clause_args)) by (apply nth_error_Some; congruence).
    assert (Harity : a < length (nth c tb dt).(tperm)).
    { rewrite Htperm, compute_permutation_length, bare_compute_var_order_length by exact Hbarec.
      exact Halt. }
    assert (Hnh : nth_error hyps' c = Some (Datalog.normal_fact (nth c hyps dh).(Datalog.clause_rel) tupc)).
    { rewrite (nth_error_nth' hyps' (Datalog.normal_fact 0 [])) by lia. rewrite Hnf0. reflexivity. }
    unfold join_entry_sat. split.
    - intros [t' [tup' [Hl' [Hn' Hr]]]].
      rewrite Hlook in Hl'. injection Hl' as <-.
      rewrite Hnh in Hn'. rewrite Htrel in Hn'. injection Hn' as Hn'.
      rewrite (trie_read_NoDup _ _ a Hnodupp Harity) in Hr.
      rewrite Hn'. exact Hr.
    - intros Ht.
      exists (nth c tb dt), tupc.
      split; [exact Hlook | split].
      + rewrite Hnh. rewrite Htrel. reflexivity.
      + rewrite (trie_read_NoDup _ _ a Hnodupp Harity). exact Ht. }
  (* query_sat reduced to a per-(ordering-position) form *)
  assert (Hqs : query_sat tries (generate_query tb ord hyps) vals hyps' <->
    (forall i v, nth_error ord i = Some v ->
       exists vi, nth_error vals i = Some vi /\
         forall e, In e (gj_entries tb v hyps) -> join_entry_sat tries hyps' vi e)).
  { unfold query_sat. split.
    - intros [_ HF] i v Hiv. rewrite Forall_forall in HF.
      assert (Hin : In (i, generate_join tb v hyps)
        (combine (seq 0 (length (generate_query tb ord hyps))) (generate_query tb ord hyps))).
      { apply In_combine_seq. exists i. split; [lia|].
        rewrite generate_query_nth_error, Hiv. reflexivity. }
      specialize (HF _ Hin). simpl in HF. destruct HF as [vi [Hvi HFe]].
      exists vi. split; [exact Hvi|]. rewrite <- generate_join_entries, <- Forall_forall. exact HFe.
    - intros H. split.
      + rewrite generate_query_length. exact Hvl.
      + rewrite Forall_forall. intros [i j] Hin.
        apply In_combine_seq in Hin. destruct Hin as [k [Hik Hk]]. simpl in Hik; subst i.
        rewrite generate_query_nth_error in Hk.
        destruct (nth_error ord k) as [v|] eqn:Hov2; simpl in Hk; [|discriminate].
        injection Hk as <-. simpl. specialize (H k v Hov2). destruct H as [vi [Hvi HFe]].
        exists vi. split; [exact Hvi|]. rewrite generate_join_entries, Forall_forall. exact HFe. }
  (* the common pointwise condition *)
  pose (Ccond := forall c a w, c < length hyps ->
          nth_error (nth c hyps dh).(Datalog.clause_args) a = Some (var_expr w) ->
          nth_error (nfargs (nth c hyps' (Datalog.normal_fact 0 []))) a = map.get ctx w).
  assert (Hq_iff : query_sat tries (generate_query tb ord hyps) vals hyps' <-> Ccond).
  { rewrite Hqs. unfold Ccond. split.
    - intros H c a w Hc Haw.
      destruct (Hstruct c Hc) as [_ [_ [_ [tupc [Hnf _]]]]].
      assert (Inw : In w ord).
      { apply Hcov, in_flat_map. exists (nth c hyps dh). split; [apply nth_In; lia|].
        unfold compute_var_order, EncodeLayout.compute_var_order. apply in_flat_map.
        exists (var_expr w). split; [eapply nth_error_In; exact Haw | simpl; auto]. }
      destruct (In_nth_error _ _ Inw) as [i Hi].
      specialize (H i w Hi). destruct H as [vi [Hvi HFe]].
      assert (Hin_e : In ((nth c tb dt).(tid), nth a (nth c tb dt).(tperm) 0, c) (gj_entries tb w hyps)).
      { apply gj_entries_In. exists c, (nth c tb dt), (nth c hyps dh), a.
        split; [apply Hcomb; lia | split; [exact Haw | reflexivity]]. }
      specialize (HFe _ Hin_e). apply (Hentry c a w vi tupc Hc Hnf Haw) in HFe.
      replace (nfargs (nth c hyps' (Datalog.normal_fact 0 []))) with tupc
        by (rewrite Hnf; reflexivity).
      rewrite HFe, (ctx_get_eq_nth ord vals ctx i w Hnd (eq_sym Hvl) Hctx Hi). symmetry; exact Hvi.
    - intros H i v Hiv.
      assert (Hilt : i < length ord) by (apply nth_error_Some; congruence).
      destruct (nth_error vals i) as [vi|] eqn:Hvi; [|exfalso; apply nth_error_None in Hvi; lia].
      exists vi. split; [reflexivity|]. intros e He.
      apply gj_entries_In in He. destruct He as [c [t [hyp [a [Hce [Hae ->]]]]]].
      destruct (Hcombinv _ _ _ Hce) as [Hc [-> ->]].
      destruct (Hstruct c Hc) as [_ [_ [_ [tupc [Hnf _]]]]].
      apply (Hentry c a v vi tupc Hc Hnf Hae).
      specialize (H c a v Hc Hae).
      replace (nfargs (nth c hyps' (Datalog.normal_fact 0 []))) with tupc in H
        by (rewrite Hnf; reflexivity).
      rewrite H, (ctx_get_eq_nth ord vals ctx i v Hnd (eq_sym Hvl) Hctx Hiv). exact Hvi. }
  assert (Hi_iff : Forall2 (interp_clause ctx) (hyps) hyps' <-> Ccond).
  { rewrite Forall2_nth_error_iff. unfold Ccond. split.
    - intros [Hlen Hpt] c a w Hc Haw.
      assert (Hbarec : bare_fact (nth c hyps dh))
        by (rewrite Forall_forall in Hbare; apply Hbare; apply nth_In; lia).
      destruct (Hstruct c Hc) as [_ [_ [_ [tupc [Hnf _]]]]].
      assert (P1 : nth_error (hyps) c = Some ((nth c hyps dh)))
        by (rewrite (nth_error_nth' hyps dh) by lia; reflexivity).
      assert (P2 : nth_error hyps' c =
                     Some (Datalog.normal_fact (nth c hyps dh).(Datalog.clause_rel) tupc)).
      { rewrite (nth_error_nth' hyps' (Datalog.normal_fact 0 [])) by lia. rewrite Hnf. reflexivity. }
      specialize (Hpt c _ _ P1 P2).
      apply interp_lfact_iff in Hpt. destruct Hpt as [_ HF2].
      apply bare_interp_args_iff in HF2; [|exact Hbarec].
      destruct HF2 as [_ HF2pt].
      replace (nfargs (nth c hyps' (Datalog.normal_fact 0 []))) with tupc
        by (rewrite Hnf; reflexivity).
      apply HF2pt; exact Haw.
    - intros H. split; [exact (eq_sym Hhl)|]. intros c xf yf Hxf Hyf.
      change (nth_error hyps c = Some xf) in Hxf.
      assert (Hc : c < length hyps).
      { assert (Hne : nth_error hyps c <> None) by (rewrite Hxf; discriminate).
        apply nth_error_Some in Hne. exact Hne. }
      assert (Exf : nth c hyps dh = xf) by (apply (nth_error_nth hyps c dh); exact Hxf).
      assert (Hbarec : bare_fact (nth c hyps dh))
        by (rewrite Forall_forall in Hbare; apply Hbare; apply nth_In; lia).
      destruct (Hstruct c Hc) as [_ [_ [_ [tupc [Hnf Hltup]]]]].
      assert (Eyf : yf = Datalog.normal_fact (nth c hyps dh).(Datalog.clause_rel) tupc).
      { assert (Hyn : nth c hyps' (Datalog.normal_fact 0 []) = yf)
          by (apply (nth_error_nth hyps' c (Datalog.normal_fact 0 [])); exact Hyf).
        rewrite <- Hyn. exact Hnf. }
      subst xf yf.
      apply interp_lfact_iff. split.
      + reflexivity.
      + apply bare_interp_args_iff; [exact Hbarec|]. split.
        * symmetry; exact Hltup.
        * intros a w Haw. specialize (H c a w Hc Haw).
          replace (nfargs (nth c hyps' (Datalog.normal_fact 0 []))) with tupc in H
            by (rewrite Hnf; reflexivity).
          exact H. }
  rewrite Hq_iff. split.
  - intros HC. exists ctx. split; [exact Hctx | apply Hi_iff; exact HC].
  - intros [ctx' [Hctx' Hf]]. assert (ctx' = ctx) by congruence. subst ctx'. apply Hi_iff; exact Hf.
Qed.

(*============================================================================*)
(*  Assembly: a compiled hardware rule matches its lowered rule (bare frag.)  *)
(*============================================================================*)

(* A left element of a [Forall2] has a related right element. *)
Lemma Forall2_In_l {A B : Type} (P : A -> B -> Prop) (l1 : list A) (l2 : list B) (a : A) :
  Forall2 P l1 l2 -> In a l1 -> exists b, In b l2 /\ P a b.
Proof.
  intros HF Hin. induction HF as [|x y l1 l2 Hxy HF IH].
  - inversion Hin.
  - destruct Hin as [-> | Hin].
    + exists y. split; [left; reflexivity | assumption].
    + destruct (IH Hin) as [b [Hbin Hpab]]. exists b. split; [right; assumption | assumption].
Qed.

(* A lowered conclusion IS a [Datalog] clause, so [Exists] over it needs no relabelling. *)
Lemma Exists_lfact (P : lowered_fact -> Prop) (l : list lowered_fact) :
  Exists (fun c => P (c)) l <-> Exists P (l).
Proof. reflexivity. Qed.

(* The per-conclusion fact [compile_concl] establishes: the conclusion is bare and each output
   index is the ordering position of the corresponding variable. *)
Definition concl_corr (ord : list var) (c : lowered_fact) (jo : join_output) : Prop :=
  jo.(output_rel) = c.(Datalog.clause_rel) /\
  Forall2 (fun e idx => exists v, e = var_expr v /\ nth_error ord idx = Some v)
          c.(Datalog.clause_args) jo.(output_var_indices).

(* Lifting [join_output_fact_interp] over the whole conclusion list: under the induced context,
   the trie-join's conclusion outputs are exactly the lowered rule's conclusion facts. *)
Lemma concl_exists_iff (ord : list var) (vals : list T) (ctx : context)
    (concls : list lowered_fact) (jos : list join_output) (f : Datalog.fact rel_id T) :
  NoDup ord -> length ord = length vals -> ctx_of ord vals = Some ctx ->
  Forall2 (concl_corr ord) concls jos ->
  ( Exists (fun jo => join_output_fact vals jo = Some f) jos <->
    Exists (fun c => interp_clause ctx (c) f) concls ).
Proof.
  intros Hnd Hlen Hctx HF. induction HF as [| c jo concls jos [Hrel Hcorr] HF IH].
  - simpl. split; intros HE; inversion HE.
  - rewrite !Exists_cons, IH,
      (join_output_fact_interp c ord vals ctx jo f Hnd Hlen Hctx Hrel Hcorr).
    reflexivity.
Qed.

(* Variables appearing in a corresponding conclusion live in the ordering. *)
Lemma corr_args_vars_in_ord (ord : list var)
    (args : list (@HardwareProgram.lowered_expr var)) (idxs : list nat) (v : var) :
  Forall2 (fun e idx => exists w, e = var_expr w /\ nth_error ord idx = Some w) args idxs ->
  In v (flat_map vars_of_expr (args)) -> In v ord.
Proof.
  intros HF. induction HF as [|e idx args idxs [w [-> Hwo]] HF IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst v. eapply nth_error_In; exact Hwo.
    + apply IH; exact Hin.
Qed.

(* Transport an [Exists interp_fact] over the conclusion list across two contexts that agree on
   the ordering (the conclusion variables, by [concl_corr], are all in the ordering). *)
Lemma exists_interp_transport (concls : list lowered_fact) (jos : list join_output)
    (ord : list var) (ctx ctx' : context) (f : Datalog.fact rel_id T) :
  Forall2 (concl_corr ord) concls jos ->
  (forall v, In v ord -> map.get ctx v = map.get ctx' v) ->
  Exists (fun c => interp_clause ctx (c) f) concls ->
  Exists (fun c => interp_clause ctx' (c) f) concls.
Proof.
  intros HF Hag Hex. induction HF as [|c jo concls jos [Hrel Hcorr] HF IH].
  - inversion Hex.
  - rewrite Exists_cons in Hex. rewrite Exists_cons. destruct Hex as [Hc | Hrest].
    + left. eapply Datalog.interp_clause_agree_on; [exact Hc|].
      apply Forall_forall. intros v Hvin. red. apply Hag.
      eapply (corr_args_vars_in_ord ord c.(Datalog.clause_args) jo.(output_var_indices) v Hcorr). exact Hvin.
    + right. apply IH; exact Hrest.
Qed.

(* A bare hypothesis's datalog variables coincide with its [compute_var_order]. *)
Lemma bare_vars_in_cvo (h : lowered_fact) (v : var) :
  bare_fact h -> In v (Datalog.vars_of_clause (h)) -> In v (compute_var_order h).
Proof.
  intros Hb Hin.
  assert (Hin' : In v (flat_map vars_of_expr (h.(Datalog.clause_args)))) by exact Hin.
  apply in_flat_map in Hin'. destruct Hin' as [e [Hein Hve]].
  unfold bare_fact in Hb. rewrite Forall_forall in Hb. destruct (Hb e Hein) as [w Hw]. subst e.
  simpl in Hve. destruct Hve as [Heq | []]. subst v.
  unfold EncodeLayout.compute_var_order. apply in_flat_map.
  exists (var_expr w). split; [exact Hein | simpl; auto].
Qed.

(*----per-hypothesis relation/arity facts----*)

(* the per-clause [hsig] shape check, exactly as in [EncodeNode.hw_rule_impl]. *)
Notation hsig_ok := (fun (sg : rel_id * nat) (fct : Datalog.fact rel_id T) =>
  match fct with
  | Datalog.normal_fact R args => R = fst sg /\ length args = snd sg
  | _ => False
  end).

(* Each hypothesis fact is the [normal_fact] with the clause's relation and arity, read off
   from [interp_clause]. *)
Lemma interp_hyp_arity (ctx : context) (rule_hyps : list lowered_fact)
    (hyps' : list (Datalog.fact rel_id T)) (dh : lowered_fact) (i : nat) :
  Forall2 (interp_clause ctx) (rule_hyps) hyps' ->
  i < length rule_hyps ->
  exists tup, nth i hyps' (Datalog.normal_fact 0 []) =
                Datalog.normal_fact (nth i rule_hyps dh).(Datalog.clause_rel) tup /\
              length tup = length (nth i rule_hyps dh).(Datalog.clause_args).
Proof.
  intros HF Hi. apply Forall2_nth_error_iff in HF. destruct HF as [Hlen Hpt].
  assert (P1 : nth_error (rule_hyps) i = Some ((nth i rule_hyps dh)))
    by (rewrite (nth_error_nth' rule_hyps dh) by lia; reflexivity).
  assert (Hib : i < length hyps') by (rewrite <- Hlen; exact Hi).
  assert (P2 : nth_error hyps' i = Some (nth i hyps' (Datalog.normal_fact 0 [])))
    by (apply nth_error_nth'; exact Hib).
  specialize (Hpt i _ _ P1 P2).
  destruct Hpt as [tup [HFa Hyeq]]. exists tup. split.
  - exact Hyeq.
  - apply Forall2_length in HFa. symmetry; exact HFa.
Qed.

(* The [hsig] shape check is exactly what [interp_clause] over the hypotheses provides. *)
Lemma interp_hyps_hsig (ctx : context) (rule_hyps : list lowered_fact)
    (hyps' : list (Datalog.fact rel_id T)) :
  Forall2 (interp_clause ctx) (rule_hyps) hyps' ->
  Forall2 hsig_ok
          (map (fun h => (h.(Datalog.clause_rel), length h.(Datalog.clause_args))) rule_hyps) hyps'.
Proof.
  revert hyps'. induction rule_hyps as [|h lhs IH]; intros hyps' HF.
  - simpl in HF. inversion HF. simpl. constructor.
  - inversion HF as [|x y xs ys Hxy HFrest]; subst.
    rewrite map_cons. constructor.
    + destruct Hxy as [tup [HFa Hyeq]]. subst y. cbn. split; [reflexivity|].
      apply Forall2_length in HFa. symmetry; exact HFa.
    + apply IH; exact HFrest.
Qed.

(* Conversely, the [hsig] shape check yields the per-hypothesis relation/arity facts. *)
Lemma hsig_length (rule_hyps : list lowered_fact) (hyps' : list (Datalog.fact rel_id T)) :
  Forall2 hsig_ok
          (map (fun h => (h.(Datalog.clause_rel), length h.(Datalog.clause_args))) rule_hyps) hyps' ->
  length hyps' = length rule_hyps.
Proof.
  intros HF. apply Forall2_length in HF. rewrite length_map in HF. symmetry; exact HF.
Qed.

Lemma hsig_arity (rule_hyps : list lowered_fact) (hyps' : list (Datalog.fact rel_id T))
    (dh : lowered_fact) (i : nat) :
  Forall2 hsig_ok
          (map (fun h => (h.(Datalog.clause_rel), length h.(Datalog.clause_args))) rule_hyps) hyps' ->
  i < length rule_hyps ->
  exists tup, nth i hyps' (Datalog.normal_fact 0 []) =
                Datalog.normal_fact (nth i rule_hyps dh).(Datalog.clause_rel) tup /\
              length tup = length (nth i rule_hyps dh).(Datalog.clause_args).
Proof.
  intros HF Hi. apply Forall2_nth_error_iff in HF. destruct HF as [Hlen Hpt].
  rewrite length_map in Hlen.
  assert (P1 : nth_error (map (fun h => (h.(Datalog.clause_rel), length h.(Datalog.clause_args))) rule_hyps) i
             = Some ((nth i rule_hyps dh).(Datalog.clause_rel), length (nth i rule_hyps dh).(Datalog.clause_args)))
    by (rewrite nth_error_map, (nth_error_nth' rule_hyps dh) by lia; reflexivity).
  assert (Hib : i < length hyps') by (rewrite <- Hlen; exact Hi).
  assert (P2 : nth_error hyps' i = Some (nth i hyps' (Datalog.normal_fact 0 [])))
    by (apply nth_error_nth'; exact Hib).
  specialize (Hpt i _ _ P1 P2). cbn in Hpt.
  destruct (nth i hyps' (Datalog.normal_fact 0 [])) as [R tup | R mg ms]; [|contradiction].
  destruct Hpt as [HR Hl]. exists tup. split.
  - rewrite HR. reflexivity.
  - exact Hl.
Qed.

(* MAIN PER-RULE BRIDGE: a hardware rule whose query, conclusions, and signature are what
   [compile_rule] emits for a bare lowered rule [lr] -- over an ordering [ord] that is exactly
   [lr]'s hypothesis variables, with per-hypothesis tries [tb] registered in [tries] -- derives
   exactly the facts [lr] derives.  This discharges [EncodeNode.hw_rule_matches] for compiled
   rules (bare/SuperNice fragment), combining [generate_query_correct] (hypotheses) with
   [concl_exists_iff] (conclusions). *)
Theorem hw_rule_correct
    (concls hyps : list lowered_fact) (hr : hardware_rule)
    (env : list (Datalog.fact rel_id T) -> rel_id -> list T -> Prop)
    (ord : list var) (tb : list trie) (tries : list trie) (dt : trie) (dh : lowered_fact) :
  NoDup ord ->
  Forall bare_fact hyps ->
  Forall bare_fact concls ->
  length tb = length hyps ->
  (forall v, In v (flat_map compute_var_order hyps) -> In v ord) ->
  (forall v, In v ord -> In v (flat_map compute_var_order hyps)) ->
  hr.(hhyps) = generate_query tb ord hyps ->
  hr.(hsig) = map (fun h => (h.(Datalog.clause_rel), length h.(Datalog.clause_args))) hyps ->
  Forall2 (concl_corr ord) concls hr.(hconcls) ->
  (forall i, i < length hyps ->
     (nth i tb dt).(trel) = (nth i hyps dh).(Datalog.clause_rel) /\
     (nth i tb dt).(tperm) = EncodeLayout.compute_permutation (var_eqb := var_eqb)
                               (compute_var_order (nth i hyps dh)) ord /\
     lookup_trie tries (nth i tb dt).(tid) = Some (nth i tb dt)) ->
  hw_rule_matches tries env (Datalog.normal_rule concls hyps) hr.
Proof.
  intros Hnd Hbareh Hbarec Htbl Hcov Hord_sub Hhhyps Hhsig Hconcl Htrie.
  intros f hyps'. unfold hw_rule_impl. split.
  - (* hardware derivation -> datalog derivation *)
    intros [Hsig [vals [Hqs [jo [Hin Hjo]]]]].
    rewrite Hhsig in Hsig.
    pose proof (hsig_length _ _ Hsig) as Hlenh.
    assert (Hvl : length vals = length ord).
    { destruct Hqs as [Hqlen _]. rewrite Hhhyps, generate_query_length in Hqlen. exact Hqlen. }
    assert (Hstruct : forall i, i < length hyps ->
       (nth i tb dt).(trel) = (nth i hyps dh).(Datalog.clause_rel) /\
       (nth i tb dt).(tperm) = EncodeLayout.compute_permutation (var_eqb := var_eqb)
                                 (compute_var_order (nth i hyps dh)) ord /\
       lookup_trie tries (nth i tb dt).(tid) = Some (nth i tb dt) /\
       exists tup, nth i hyps' (Datalog.normal_fact 0 []) =
                     Datalog.normal_fact (nth i hyps dh).(Datalog.clause_rel) tup /\
                   length tup = length (nth i hyps dh).(Datalog.clause_args)).
    { intros i Hi. destruct (Htrie i Hi) as [H1 [H2 H3]].
      destruct (hsig_arity hyps hyps' dh i Hsig Hi) as [tup [Hnf Hlt]].
      repeat split; try assumption. exists tup. split; assumption. }
    rewrite Hhhyps in Hqs.
    apply (proj1 (generate_query_correct ord hyps tb tries vals hyps' dt dh
                    Hnd Hbareh Htbl Hlenh Hvl Hcov Hstruct)) in Hqs.
    destruct Hqs as [ctx [Hctx Hfa]].
    (* the produced fact comes from a conclusion clause, hence is a normal fact *)
    assert (Hexf : Exists (fun c => interp_clause ctx c f) concls).
    { apply (proj1 (concl_exists_iff ord vals ctx concls hr.(hconcls) f
                      Hnd (eq_sym Hvl) Hctx Hconcl)).
      apply Exists_exists. exists jo. split; [exact Hin | exact Hjo]. }
    apply Exists_exists in Hexf. destruct Hexf as [c [Hcin [nf_args [Hcargs Hfeq]]]].
    apply (proj2 (lrule_impl_iff concls hyps env f hyps')).
    exists (c.(Datalog.clause_rel)), nf_args, ctx. split; [exact Hfeq|]. split; [exact Hfa|].
    rewrite <- Hfeq. apply Exists_exists. exists c. split; [exact Hcin|]. exists nf_args. auto.
  - (* datalog derivation -> hardware derivation *)
    intros Hri. apply lrule_impl_iff in Hri.
    destruct Hri as [R [args [ctx [-> [Hfa Hex]]]]].
    (* the context is defined on every ordering variable (= hypothesis variable) *)
    assert (Hdom : forall v, In v ord -> exists t, map.get ctx v = Some t).
    { intros v Hv. apply Hord_sub in Hv. apply in_flat_map in Hv.
      destruct Hv as [h [Hh Hvco]].
      assert (Hbh : bare_fact h) by (rewrite Forall_forall in Hbareh; auto).
      assert (HLvar : In (var_expr v) h.(Datalog.clause_args)).
      { unfold EncodeLayout.compute_var_order in Hvco. apply in_flat_map in Hvco.
        destruct Hvco as [arg [Harg Hva]]. unfold bare_fact in Hbh. rewrite Forall_forall in Hbh.
        destruct (Hbh arg Harg) as [w Hw]. subst arg. simpl in Hva.
        destruct Hva as [Heq | []]. subst w. exact Harg. }
      destruct (Forall2_In_l _ _ _ (h) Hfa Hh) as [y [_ Hint]].
      destruct Hint as [tup [HFa Hyeq]].
      destruct (Forall2_In_l _ _ _ (var_expr v) HFa HLvar) as [u [_ Hiu]].
      apply interp_var_iff in Hiu. exists u. exact Hiu. }
    (* build the binding [vals] from the context over the ordering *)
    assert (HforallOrd : Forall (fun v => In v ord) ord)
      by (apply Forall_forall; intros; assumption).
    destruct (map.getmany_of_list_exists ctx (fun v => In v ord) ord HforallOrd Hdom)
      as [vals Hvals].
    pose proof (map.getmany_of_list_length _ _ _ Hvals) as Hlenov.
    destruct (ctx_of_exists ord vals Hlenov) as [ctx' Hctx'].
    assert (Hagree : forall v, In v ord -> map.get ctx' v = map.get ctx v).
    { intros v Hv. destruct (In_nth_error _ _ Hv) as [i Hi].
      assert (Hilt : i < length ord) by (apply nth_error_Some; congruence).
      destruct (nth_error vals i) as [t|] eqn:Evt;
        [|exfalso; apply nth_error_None in Evt; lia].
      rewrite (ctx_get_eq_nth ord vals ctx' i v Hnd Hlenov Hctx' Hi), Evt.
      symmetry. exact (map.getmany_of_list_get ord i ctx vals v t Hvals Hi Evt). }
    (* transport the hypotheses' interpretation to [ctx'] *)
    assert (Hfa' : Forall2 (interp_clause ctx') (hyps) hyps').
    { eapply Forall2_impl_strong; [|exact Hfa].
      intros lf y Hif Hinlf _.
      eapply Datalog.interp_clause_agree_on; [exact Hif|].
      apply Forall_forall. intros v Hvin. red. symmetry. apply Hagree.
      apply Hcov. apply in_flat_map. exists lf. split; [exact Hinlf|].
      apply bare_vars_in_cvo; [rewrite Forall_forall in Hbareh; auto | exact Hvin]. }
    assert (Hlenh : length hyps' = length hyps).
    { pose proof Hfa as HfaC. apply Forall2_nth_error_iff in HfaC.
      destruct HfaC as [Hl _]. exact (eq_sym Hl). }
    assert (Hstruct : forall i, i < length hyps ->
       (nth i tb dt).(trel) = (nth i hyps dh).(Datalog.clause_rel) /\
       (nth i tb dt).(tperm) = EncodeLayout.compute_permutation (var_eqb := var_eqb)
                                 (compute_var_order (nth i hyps dh)) ord /\
       lookup_trie tries (nth i tb dt).(tid) = Some (nth i tb dt) /\
       exists tup, nth i hyps' (Datalog.normal_fact 0 []) =
                     Datalog.normal_fact (nth i hyps dh).(Datalog.clause_rel) tup /\
                   length tup = length (nth i hyps dh).(Datalog.clause_args)).
    { intros i Hi. destruct (Htrie i Hi) as [H1 [H2 H3]].
      destruct (interp_hyp_arity ctx hyps hyps' dh i Hfa Hi) as [tup [Hnf Hlt]].
      repeat split; try assumption. exists tup. split; assumption. }
    split.
    + rewrite Hhsig. apply (interp_hyps_hsig ctx). exact Hfa.
    + exists vals. split.
      * rewrite Hhhyps.
        apply (proj2 (generate_query_correct ord hyps tb tries vals hyps' dt dh
                        Hnd Hbareh Htbl Hlenh (eq_sym Hlenov) Hcov Hstruct)).
        exists ctx'. split; [exact Hctx' | exact Hfa'].
      * assert (Hex' : Exists (fun c => interp_clause ctx' (c) (Datalog.normal_fact R args)) concls).
        { eapply exists_interp_transport; [exact Hconcl | | exact Hex].
          intros v Hv. symmetry. apply Hagree; exact Hv. }
        apply (proj2 (concl_exists_iff ord vals ctx' concls hr.(hconcls) (Datalog.normal_fact R args)
                        Hnd Hlenov Hctx' Hconcl)) in Hex'.
        apply Exists_exists in Hex'. destruct Hex' as [jo [Hin Hjo]].
        exists jo. split; [exact Hin | exact Hjo].
Qed.

End EncodeLayoutCorrect.

(*============================================================================*)
(*  Discharge lemmas: structural facts about [EncodeLayout.compile_rule]'s      *)
(*  output that feed [hw_rule_correct].  These are the *definitional* facts      *)
(*  (the per-hypothesis trie's relation/permutation, the query shape, and the    *)
(*  conclusion index correspondence).  They need EncodeLayout's full parameter   *)
(*  context, hence their own section here -- the compiler file stays proof-free. *)
(*                                                                               *)
(*  The remaining obligations are algorithmic: that                              *)
(*  [compute_variable_ordering_ordered] is NoDup and covers exactly the          *)
(*  hypothesis variables, and that the per-rule tries are registered in the      *)
(*  node's trie table with unique ids (an invariant threaded through             *)
(*  [compile_node]).                                                             *)
(*============================================================================*)

Section CompileDischarge.

Import ResultMonadNotations.
Open Scope result_monad_scope.

(* EncodeLayout's parameter context (the subset the relevant definitions use). *)
Context {rel var fn aggregator T : Type}.
Context {var_eqb : var -> var -> bool}
        {var_eqb_spec : forall x y : var, BoolSpec (x = y) (x <> y) (var_eqb x y)}.
Context {Node : Type}.
Context {node_id : Type}
        {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.
Context {node_id_set : map.map node_id unit}.
Context {rel_dependency_map : map.map rel_id node_id_set}.
Context {fn_id_map : map.map fn fn_id}.
Context {rel_relid_map : map.map rel rel_id}.
Context {var_idx_map : map.map var nat}.

Notation lowered_fact := (@HardwareProgram.lowered_fact var).
Notation lowered_expr := (@HardwareProgram.lowered_expr var).
Notation global_context :=
  (@EncodeLayout.global_context rel fn Node node_id node_id_set rel_dependency_map fn_id_map rel_relid_map).
Notation node_context := (@EncodeLayout.node_context node_id).
Notation generate_trie :=
  (@EncodeLayout.generate_trie rel var fn var_eqb Node node_id node_id_set rel_dependency_map
                               fn_id_map rel_relid_map var_idx_map).
Notation compile_hyps :=
  (@EncodeLayout.compile_hyps rel var fn var_eqb Node node_id node_id_set rel_dependency_map
                              fn_id_map rel_relid_map var_idx_map).
Notation compile_concl :=
  (@EncodeLayout.compile_concl rel var fn var_eqb Node node_id node_id_set rel_dependency_map
                               fn_id_map rel_relid_map).
Notation compile_concls :=
  (@EncodeLayout.compile_concls rel var fn var_eqb Node node_id node_id_set rel_dependency_map
                                fn_id_map rel_relid_map).
Notation generate_query := (@EncodeLayout.generate_query var var_eqb).
Notation compute_var_order := (@EncodeLayout.compute_var_order var).
Notation compute_permutation := (@EncodeLayout.compute_permutation var var_eqb var_idx_map).
Notation get_rule_var_index := (@EncodeLayout.get_rule_var_index var var_eqb).
Notation index_of_var := (@EncodeLayout.index_of_var var var_eqb).
Notation index_of_var_aux := (@EncodeLayout.index_of_var_aux var var_eqb).

(* [generate_trie] always returns a trie indexing the hypothesis's relation by the
   permutation computed for that hypothesis -- whether it freshly allocates one or
   reuses an existing trie found by [find] (whose predicate forces both fields). *)
Lemma generate_trie_spec (hyp : lowered_fact) (ord : list var)
    (existing : list trie) (gc : global_context) (nc : node_context) (t : trie) (nc' : node_context) :
  generate_trie hyp ord existing gc nc = (t, nc') ->
  t.(trel) = hyp.(Datalog.clause_rel) /\
  t.(tperm) = compute_permutation (compute_var_order hyp) ord.
Proof.
  intros H. unfold EncodeLayout.generate_trie in H. cbv zeta in H.
  destruct (List.find _ existing) as [t0|] eqn:Hfind; inversion H; subst; clear H.
  - apply List.find_some in Hfind. destruct Hfind as [_ Hpred].
    apply andb_true_iff in Hpred. destruct Hpred as [Hrel Hperm].
    apply Nat.eqb_eq in Hrel. apply permutation_eqb_eq in Hperm.
    split; assumption.
  - split; reflexivity.
Qed.

(* The per-hypothesis trie list [compile_hyps] threads (in reverse) matches the
   hypotheses one-for-one with [generate_trie]'s relation/permutation facts. *)
Lemma compile_hyps_fold (ord : list var) (gc : global_context) (hyps : list lowered_fact) :
  forall (pool0 rev0 : list trie) (nc0 : node_context)
         (pool1 rev1 : list trie) (nc1 : node_context),
  fold_left (fun '(pool, per_hyp_rev, ncontext) hyp =>
      let (t, ncontext) := generate_trie hyp ord pool gc ncontext in
      (t :: pool, t :: per_hyp_rev, ncontext)) hyps (pool0, rev0, nc0)
    = (pool1, rev1, nc1) ->
  exists ts, rev1 = (List.rev ts ++ rev0)%list /\ List.length ts = List.length hyps /\
    Forall2 (fun t hyp => t.(trel) = hyp.(Datalog.clause_rel) /\
                          t.(tperm) = compute_permutation (compute_var_order hyp) ord) ts hyps.
Proof.
  induction hyps as [|hyp hyps IH]; intros pool0 rev0 nc0 pool1 rev1 nc1 H; simpl in H.
  - inversion H; subst. exists []. simpl. split; [reflexivity|]. split; [reflexivity|constructor].
  - destruct (generate_trie hyp ord pool0 gc nc0) as [t nc0'] eqn:Hgt.
    destruct (IH (t :: pool0) (t :: rev0) nc0' pool1 rev1 nc1 H) as [ts [Hrev [Hlen HF]]].
    exists (t :: ts). split.
    + simpl. rewrite Hrev. rewrite <- app_assoc. reflexivity.
    + split; [simpl; rewrite Hlen; reflexivity|].
      constructor; [apply (generate_trie_spec hyp ord pool0 gc nc0 t nc0' Hgt) | exact HF].
Qed.

(* [compile_hyps]'s query is exactly [generate_query] over the per-hypothesis tries,
   one per hypothesis, with the relation/permutation facts above. *)
Lemma compile_hyps_shape (hyps : list lowered_fact) (ord : list var)
    (existing : list trie) (gc : global_context) (nc : node_context)
    (q : query) (nc' : node_context) :
  compile_hyps hyps ord existing gc nc = (q, nc') ->
  exists tb : list trie,
    q = generate_query tb ord hyps /\
    List.length tb = List.length hyps /\
    Forall2 (fun t hyp => t.(trel) = hyp.(Datalog.clause_rel) /\
                          t.(tperm) = compute_permutation (compute_var_order hyp) ord) tb hyps.
Proof.
  intros H. unfold EncodeLayout.compile_hyps in H.
  match type of H with
  | context [fold_left ?F hyps ?init] =>
      destruct (fold_left F hyps init) as [[pool1 rev1] nc1] eqn:Hfold
  end.
  cbn beta iota zeta in H. injection H as Hq _; subst q.
  destruct (compile_hyps_fold ord gc hyps existing [] nc pool1 rev1 nc1 Hfold)
    as [ts [Hrev [Hlen HF]]].
  exists ts. rewrite Hrev, app_nil_r, rev_involutive.
  split; [reflexivity | split; [exact Hlen | exact HF]].
Qed.

(*----conclusion index correspondence----*)

(* [index_of_var] locates a variable: the returned index really points at it. *)
Lemma index_of_var_aux_sound (v : var) (vars : list var) :
  forall (i idx : nat),
  index_of_var_aux v vars i = Some idx ->
  exists k, idx = i + k /\ List.nth_error vars k = Some v.
Proof.
  induction vars as [|w vars IH]; intros i idx H; simpl in H; [discriminate|].
  destruct (var_eqb_spec v w) as [->|Hne].
  - injection H as <-. exists 0. split; [lia | reflexivity].
  - destruct (IH (S i) idx H) as [k [-> Hk]]. exists (S k). split; [lia | exact Hk].
Qed.

Lemma index_of_var_sound (v : var) (vars : list var) (idx : nat) :
  index_of_var v vars = Some idx -> List.nth_error vars idx = Some v.
Proof.
  unfold EncodeLayout.index_of_var. intros H.
  destruct (index_of_var_aux_sound v vars 0 idx H) as [k [-> Hk]].
  rewrite Nat.add_0_l. exact Hk.
Qed.

Lemma get_rule_var_index_sound (ord : list var) (v : var) (idx : nat) :
  get_rule_var_index ord v = Success idx -> List.nth_error ord idx = Some v.
Proof.
  unfold EncodeLayout.get_rule_var_index.
  destruct (index_of_var v ord) as [i|] eqn:Hi; [|discriminate].
  intros H. injection H as <-. apply index_of_var_sound; exact Hi.
Qed.

(* The conclusion-folding step preserves [Failure]: once it errors, it stays errored. *)
Lemma compile_concl_fold_error (ord : list var) (args : list lowered_expr) :
  forall (e : dlist.dlist),
  fold_left (fun acc arg => idxs <- acc ;;
      match arg with
      | var_expr v => idx <- get_rule_var_index ord v ;; Success (idx :: idxs)
      | fun_expr _ _ => Success (0 :: idxs)
      end) args (Failure e) = Failure e.
Proof.
  induction args as [|a args IH]; intros e; simpl; [reflexivity|].
  destruct a; apply IH.
Qed.

(* For a bare conclusion the index fold succeeds with the per-argument indices in order
   (built reversed onto the accumulator), each pointing at its variable in [ord]. *)
Lemma compile_concl_fold_spec (ord : list var) (args : list lowered_expr) :
  forall (acc0 out : list nat),
  Forall (fun e => exists v, e = var_expr v) args ->
  fold_left (fun acc arg => idxs <- acc ;;
      match arg with
      | var_expr v => idx <- get_rule_var_index ord v ;; Success (idx :: idxs)
      | fun_expr _ _ => Success (0 :: idxs)
      end) args (Success acc0) = Success out ->
  exists idxs, out = (List.rev idxs ++ acc0)%list /\
    Forall2 (fun e idx => exists v, e = var_expr v /\ List.nth_error ord idx = Some v) args idxs.
Proof.
  induction args as [|a args IH]; intros acc0 out Hbare H; simpl in H.
  - injection H as <-. exists []. split; [reflexivity | constructor].
  - inversion Hbare as [|x l [v Hv] Hbare']; subst a.
    simpl in H.
    destruct (get_rule_var_index ord v) as [idx|] eqn:Hgi.
    + simpl in H. destruct (IH (idx :: acc0) out Hbare' H) as [idxs [Hout HF]].
      exists (idx :: idxs). split.
      * rewrite Hout. simpl. rewrite <- app_assoc. reflexivity.
      * constructor;
          [exists v; split; [reflexivity | apply get_rule_var_index_sound; exact Hgi] | exact HF].
    + simpl in H. rewrite compile_concl_fold_error in H. discriminate.
Qed.

(* A compiled (bare) conclusion's join_output relation and indices correspond to the
   lowered conclusion: each output index is the ordering position of that variable.
   This is exactly [EncodeLayoutCorrect.concl_corr]. *)
Lemma compile_concl_corr (concl : lowered_fact) (gc : global_context) (ord : list var)
    (jo : join_output) :
  Forall (fun e => exists v, e = var_expr v) concl.(Datalog.clause_args) ->
  compile_concl concl gc ord = Success jo ->
  jo.(output_rel) = concl.(Datalog.clause_rel) /\
  Forall2 (fun e idx => exists v, e = var_expr v /\ List.nth_error ord idx = Some v)
          concl.(Datalog.clause_args) jo.(output_var_indices).
Proof.
  intros Hbare H. unfold EncodeLayout.compile_concl in H.
  destruct (fold_left _ concl.(Datalog.clause_args) (Success (@nil nat))) as [var_indices|] eqn:Hfold; [|discriminate].
  injection H as <-. simpl. split; [reflexivity|].
  destruct (compile_concl_fold_spec ord concl.(Datalog.clause_args) [] var_indices Hbare Hfold)
    as [idxs [Hvi HF]].
  rewrite Hvi, app_nil_r, rev_involutive. exact HF.
Qed.

(* The conclusion-list fold preserves [Failure]. *)
Lemma compile_concls_fold_error (gc : global_context) (ord : list var)
    (concls : list lowered_fact) :
  forall (e : dlist.dlist),
  fold_left (fun acc concl => jos <- acc ;; jo <- compile_concl concl gc ord ;;
                              Success (jo :: jos)) concls (Failure e) = Failure e.
Proof. induction concls as [|c concls IH]; intros e; simpl; [reflexivity | apply IH]. Qed.

Lemma compile_concls_fold_spec (gc : global_context) (ord : list var)
    (concls : list lowered_fact) :
  forall (acc0 out : list join_output),
  Forall (fun c => Forall (fun e => exists v, e = var_expr v) c.(Datalog.clause_args)) concls ->
  fold_left (fun acc concl => jos <- acc ;; jo <- compile_concl concl gc ord ;;
                              Success (jo :: jos)) concls (Success acc0) = Success out ->
  exists jos, out = (rev jos ++ acc0)%list /\ Forall2 (concl_corr ord) concls jos.
Proof.
  induction concls as [|c concls IH]; intros acc0 out Hb H; simpl in H.
  - injection H as <-. exists []. split; [reflexivity | constructor].
  - inversion Hb as [|x l Hbc Hb']; subst.
    simpl in H. destruct (compile_concl c gc ord) as [jo|] eqn:Hcc.
    + simpl in H. destruct (IH (jo :: acc0) out Hb' H) as [jos [Hout HF]].
      exists (jo :: jos). split.
      * rewrite Hout. simpl. rewrite <- app_assoc. reflexivity.
      * constructor; [exact (compile_concl_corr c gc ord jo Hbc Hcc) | exact HF].
    + simpl in H. rewrite compile_concls_fold_error in H. discriminate.
Qed.

(* [compile_concls] yields the per-conclusion correspondence [concl_corr] over the whole list. *)
Lemma compile_concls_corr (concls : list lowered_fact) (gc : global_context) (ord : list var)
    (jos : list join_output) :
  Forall (fun c => Forall (fun e => exists v, e = var_expr v) c.(Datalog.clause_args)) concls ->
  compile_concls concls gc ord = Success jos ->
  Forall2 (concl_corr ord) concls jos.
Proof.
  intros Hb H. unfold EncodeLayout.compile_concls in H.
  match type of H with
  | context [fold_left ?F concls ?init] => destruct (fold_left F concls init) as [jf|] eqn:Hfold
  end; cbn beta iota zeta in H; [|discriminate].
  injection H as <-.
  destruct (compile_concls_fold_spec gc ord concls [] jf Hb Hfold) as [js [Hjf HF]].
  rewrite Hjf, app_nil_r, rev_involutive. exact HF.
Qed.

(*----trie registration: each per-rule trie is found in the node's trie table----*)

(* With unique trie ids, [find]-by-id returns exactly the trie. *)
Lemma find_tid_unique (l : list trie) (t : trie) :
  In t l -> NoDup (map (fun x => x.(tid)) l) ->
  find (fun x => Nat.eqb x.(tid) t.(tid)) l = Some t.
Proof.
  induction l as [|x l IH]; intros Hin Hnd; simpl in *; [contradiction|].
  inversion Hnd as [|y ys Hynin Hnd' Heq]; subst.
  destruct (Nat.eqb_spec x.(tid) t.(tid)) as [He|Hne].
  - destruct Hin as [Heq | Hin]; [rewrite Heq; reflexivity|].
    exfalso. apply Hynin. rewrite He. apply in_map; exact Hin.
  - destruct Hin as [-> | Hin]; [congruence | apply IH; assumption].
Qed.

Lemma lookup_trie_some (l : list trie) (t : trie) :
  In t l -> NoDup (map (fun x => x.(tid)) l) ->
  EncodeNode.lookup_trie l t.(tid) = Some t.
Proof. unfold EncodeNode.lookup_trie. apply find_tid_unique. Qed.

(* Node-context well-formedness: ids are bounded by the fresh-id counter and duplicate-free. *)
Definition wf_nc (nc : node_context) : Prop :=
  (forall t, In t nc.(nctries) -> t.(tid) < nc.(last_trie_id)) /\
  NoDup (map (fun t => t.(tid)) nc.(nctries)).

(* [generate_trie] either reuses an existing trie (context unchanged) or allocates a fresh one. *)
Lemma generate_trie_nctries (hyp : lowered_fact) (ord : list var)
    (existing : list trie) (gc : global_context) (nc : node_context) (t : trie) (nc' : node_context) :
  generate_trie hyp ord existing gc nc = (t, nc') ->
  (nc' = nc /\ In t existing) \/
  (nc'.(nctries) = t :: nc.(nctries) /\ nc'.(last_trie_id) = S nc.(last_trie_id) /\
   t.(tid) = nc.(last_trie_id)).
Proof.
  intros H. unfold EncodeLayout.generate_trie in H. cbv zeta in H.
  destruct (List.find _ existing) as [t0|] eqn:Hfind; injection H as <- <-.
  - left. apply List.find_some in Hfind. destruct Hfind as [Hin _]. split; [reflexivity | exact Hin].
  - right. split; [reflexivity | split; reflexivity].
Qed.

Lemma generate_trie_wf (hyp : lowered_fact) (ord : list var)
    (existing : list trie) (gc : global_context) (nc : node_context) (t : trie) (nc' : node_context) :
  generate_trie hyp ord existing gc nc = (t, nc') ->
  wf_nc nc -> incl existing nc.(nctries) ->
  wf_nc nc' /\ incl nc.(nctries) nc'.(nctries) /\ In t nc'.(nctries).
Proof.
  intros H [Hlt Hnd] Hincl.
  destruct (generate_trie_nctries hyp ord existing gc nc t nc' H)
    as [[-> Hin] | [Hnct [Hlast Htid]]].
  - split; [split; assumption | split; [apply incl_refl | apply Hincl; exact Hin]].
  - assert (Hwf : wf_nc nc').
    { split.
      - intros s Hs. rewrite Hnct in Hs. rewrite Hlast.
        destruct Hs as [<- | Hs]; [rewrite Htid; lia | specialize (Hlt s Hs); lia].
      - rewrite Hnct. simpl. constructor; [|exact Hnd].
        rewrite in_map_iff. intros [s [Hseq Hsin]].
        specialize (Hlt s Hsin). rewrite Htid in Hseq. lia. }
    split; [exact Hwf | split].
    + intros s Hs. rewrite Hnct. right. exact Hs.
    + rewrite Hnct. left. reflexivity.
Qed.

(* The [compile_hyps] fold preserves [wf_nc], grows [nctries] monotonically, and keeps every
   chosen per-hypothesis trie inside [nctries] (the pool stays a subset of the node's tries). *)
Lemma compile_hyps_fold_reg (ord : list var) (gc : global_context) (hyps : list lowered_fact) :
  forall (pool0 rev0 : list trie) (nc0 : node_context)
         (pool1 rev1 : list trie) (nc1 : node_context),
  fold_left (fun '(pool, per_hyp_rev, ncontext) hyp =>
      let (t, ncontext) := generate_trie hyp ord pool gc ncontext in
      (t :: pool, t :: per_hyp_rev, ncontext)) hyps (pool0, rev0, nc0) = (pool1, rev1, nc1) ->
  wf_nc nc0 -> incl pool0 nc0.(nctries) -> (forall t, In t rev0 -> In t nc0.(nctries)) ->
  wf_nc nc1 /\ incl nc0.(nctries) nc1.(nctries) /\ incl pool1 nc1.(nctries) /\
  (forall t, In t rev1 -> In t nc1.(nctries)).
Proof.
  induction hyps as [|hyp hyps IH];
    intros pool0 rev0 nc0 pool1 rev1 nc1 H Hwf Hpool Hrev; simpl in H.
  - inversion H; subst.
    split; [exact Hwf | split; [apply incl_refl | split; [exact Hpool | exact Hrev]]].
  - destruct (generate_trie hyp ord pool0 gc nc0) as [t nc0'] eqn:Hgt.
    destruct (generate_trie_wf hyp ord pool0 gc nc0 t nc0' Hgt Hwf Hpool) as [Hwf' [Hmono Htin]].
    assert (Hpool' : incl (t :: pool0) nc0'.(nctries))
      by (apply incl_cons; [exact Htin | intros s Hs; apply Hmono; apply Hpool; exact Hs]).
    assert (Hrev' : forall s, In s (t :: rev0) -> In s nc0'.(nctries))
      by (intros s [<- | Hs]; [exact Htin | apply Hmono; apply Hrev; exact Hs]).
    destruct (IH (t :: pool0) (t :: rev0) nc0' pool1 rev1 nc1 H Hwf' Hpool' Hrev')
      as [Hwf1 [Hmono1 [Hpool1 Hrev1]]].
    split; [exact Hwf1 |
            split; [apply (incl_tran Hmono Hmono1) | split; [exact Hpool1 | exact Hrev1]]].
Qed.

(* Top-level: [compile_hyps] (started from the node's own tries) preserves [wf_nc], grows the
   trie table, and yields the per-hypothesis trie list -- all of whose tries are registered. *)
Lemma compile_hyps_reg (hyps : list lowered_fact) (ord : list var) (gc : global_context)
    (nc : node_context) (q : query) (nc' : node_context) :
  compile_hyps hyps ord nc.(nctries) gc nc = (q, nc') ->
  wf_nc nc ->
  wf_nc nc' /\ incl nc.(nctries) nc'.(nctries) /\
  (exists tb, q = generate_query tb ord hyps /\ (forall t, In t tb -> In t nc'.(nctries))).
Proof.
  intros H Hwf. unfold EncodeLayout.compile_hyps in H.
  match type of H with
  | context [fold_left ?F hyps ?init] =>
      destruct (fold_left F hyps init) as [[pool1 rev1] nc1] eqn:Hfold
  end.
  cbn beta iota zeta in H. injection H as Hq Hnc; subst q nc'.
  assert (Hrev0 : forall t, In t (@nil trie) -> In t nc.(nctries)) by (intros t []).
  destruct (compile_hyps_fold_reg ord gc hyps nc.(nctries) [] nc pool1 rev1 nc1
              Hfold Hwf (incl_refl _) Hrev0) as [Hwf1 [Hmono [_ Hrevin]]].
  split; [exact Hwf1 | split; [exact Hmono |]].
  exists (rev rev1). split; [reflexivity|].
  intros t Htb. apply Hrevin. rewrite in_rev. exact Htb.
Qed.

(* Combined: one [tb] with both the relation/permutation facts and the registration. *)
Lemma compile_hyps_full (hyps : list lowered_fact) (ord : list var) (gc : global_context)
    (nc : node_context) (q : query) (nc' : node_context) :
  compile_hyps hyps ord nc.(nctries) gc nc = (q, nc') ->
  wf_nc nc ->
  wf_nc nc' /\ incl nc.(nctries) nc'.(nctries) /\
  exists tb, q = generate_query tb ord hyps /\ List.length tb = List.length hyps /\
    Forall2 (fun t hyp => t.(trel) = hyp.(Datalog.clause_rel) /\
                          t.(tperm) = compute_permutation (compute_var_order hyp) ord) tb hyps /\
    (forall t, In t tb -> In t nc'.(nctries)).
Proof.
  intros H Hwf. unfold EncodeLayout.compile_hyps in H.
  match type of H with
  | context [fold_left ?F hyps ?init] =>
      destruct (fold_left F hyps init) as [[pool1 rev1] nc1] eqn:Hfold
  end.
  cbn beta iota zeta in H. injection H as Hq Hnc; subst nc'.
  destruct (compile_hyps_fold ord gc hyps nc.(nctries) [] nc pool1 rev1 nc1 Hfold)
    as [ts [Hrev [Hlen HFtt]]].
  assert (Hrev0 : forall t, In t (@nil trie) -> In t nc.(nctries)) by (intros t []).
  destruct (compile_hyps_fold_reg ord gc hyps nc.(nctries) [] nc pool1 rev1 nc1
              Hfold Hwf (incl_refl _) Hrev0) as [Hwf1 [Hmono [_ Hrevin]]].
  split; [exact Hwf1 | split; [exact Hmono |]].
  exists ts. split; [|split; [exact Hlen | split; [exact HFtt|]]].
  - rewrite <- Hq, Hrev, app_nil_r, rev_involutive. reflexivity.
  - intros t Ht. apply Hrevin. rewrite Hrev, app_nil_r. rewrite <- in_rev. exact Ht.
Qed.

End CompileDischarge.

(*============================================================================*)
(*  Variable-ordering correctness: [compute_variable_ordering_ordered] over     *)
(*  [create_dependency_graph hyps] returns a duplicate-free list that is         *)
(*  exactly the set of hypothesis variables (the candidates).  This discharges   *)
(*  [hw_rule_correct]'s [NoDup ord], coverage, and subset hypotheses.            *)
(*============================================================================*)

Section OrderingCorrect.

Context {var : Type}.
Context {var_eqb : var -> var -> bool}
        {var_eqb_spec : forall x y : var, BoolSpec (x = y) (x <> y) (var_eqb x y)}.
Context {var_node_set : map.map var unit} {var_node_set_ok : map.ok var_node_set}.
Context {var_edge_set : map.map var var_node_set}.

Notation ordering_context := (@EncodeLayout.ordering_context var var_node_set var_edge_set).
Notation var_graph := (@EncodeLayout.var_graph var var_node_set var_edge_set).
Notation lowered_fact := (@HardwareProgram.lowered_fact var).
Notation choose := (@EncodeLayout.choose_next_var_ordered var var_node_set var_edge_set).
Notation visit_node := (@EncodeLayout.visit_node var var_node_set var_edge_set).
Notation dedup := (@EncodeLayout.dedup var var_node_set).
Notation collect_vars_fact := (@EncodeLayout.collect_vars_fact var).
Notation collect_vars_hyps := (@EncodeLayout.collect_vars_hyps var).
Notation compute_var_order := (@EncodeLayout.compute_var_order var).

(* The generic per-candidate step shared by both max-degree folds: a candidate
   is considered only if it is still a graph node. *)
Definition mstep (ns : var_node_set) (degf : var -> nat)
    (acc : option (var * nat)) (x : var) : option (var * nat) :=
  match map.get ns x with
  | None => acc
  | Some _ =>
    match acc with
    | None => Some (x, degf x)
    | Some (_, md) => if Nat.ltb md (degf x) then Some (x, degf x) else acc
    end
  end.

(* The max-degree fold only ever returns a candidate that is a current graph node. *)
Lemma fold_mstep_acc (ns : var_node_set) (degf : var -> nat) (cs : list var) :
  forall acc0 v d,
  fold_left (mstep ns degf) cs acc0 = Some (v, d) ->
  (In v cs /\ map.get ns v <> None) \/ acc0 = Some (v, d).
Proof.
  induction cs as [|x cs IH]; intros acc0 v d H; simpl in H.
  - right. exact H.
  - apply IH in H. destruct H as [[Hin Hne] | Hacc].
    + left. split; [right; exact Hin | exact Hne].
    + unfold mstep in Hacc. destruct (map.get ns x) as [u|] eqn:Hx.
      * destruct acc0 as [[x0 md]|].
        -- destruct (Nat.ltb md (degf x)).
           ++ injection Hacc as <- <-. left. split; [left; reflexivity | rewrite Hx; discriminate].
           ++ right. exact Hacc.
        -- injection Hacc as <- <-. left. split; [left; reflexivity | rewrite Hx; discriminate].
      * right. exact Hacc.
Qed.

(* And it returns [None] only when no candidate is a current graph node. *)
Lemma fold_mstep_None (ns : var_node_set) (degf : var -> nat) (cs : list var) :
  forall acc0,
  fold_left (mstep ns degf) cs acc0 = None ->
  acc0 = None /\ (forall x, In x cs -> map.get ns x = None).
Proof.
  induction cs as [|x cs IH]; intros acc0 H; simpl in H.
  - split; [exact H | intros x []].
  - apply IH in H. destruct H as [Hstep Hrest].
    unfold mstep in Hstep. destruct (map.get ns x) as [u|] eqn:Hx.
    + destruct acc0 as [[x0 md]|]; [destruct (Nat.ltb md (degf x)); discriminate | discriminate].
    + split; [exact Hstep|]. intros y [<- | Hy]; [exact Hx | apply Hrest; exact Hy].
Qed.

(* [choose] picks a candidate that is a current graph node, ... *)
Lemma choose_Some (ctx : ordering_context) (cs : list var) (v : var) :
  choose ctx cs = Some v ->
  In v cs /\ map.get ctx.(dep_graph).(nodes) v <> None.
Proof.
  unfold EncodeLayout.choose_next_var_ordered.
  destruct (EncodeLayout.compute_max_degree_var_to_visited_set_ordered _ _ _)
    as [[v1 d1]|] eqn:H1.
  - intros H. injection H as <-.
    unfold EncodeLayout.compute_max_degree_var_to_visited_set_ordered in H1.
    apply (fold_mstep_acc ctx.(dep_graph).(nodes)
             (EncodeLayout.compute_degree_to_visited_set ctx.(dep_graph) ctx.(visited)) cs None v1 d1)
      in H1.
    destruct H1 as [[Hin Hne]|H1]; [split; assumption | discriminate].
  - destruct (EncodeLayout.compute_max_degree_var_ordered _ _) as [[v2 d2]|] eqn:H2; [|discriminate].
    intros H. injection H as <-.
    unfold EncodeLayout.compute_max_degree_var_ordered in H2.
    apply (fold_mstep_acc ctx.(dep_graph).(nodes)
             (EncodeLayout.compute_degree ctx.(dep_graph)) cs None v2 d2) in H2.
    destruct H2 as [[Hin Hne]|H2]; [split; assumption | discriminate].
Qed.

(* ... and returns [None] only when no candidate is a current graph node. *)
Lemma choose_None (ctx : ordering_context) (cs : list var) :
  choose ctx cs = None ->
  forall v, In v cs -> map.get ctx.(dep_graph).(nodes) v = None.
Proof.
  unfold EncodeLayout.choose_next_var_ordered.
  destruct (EncodeLayout.compute_max_degree_var_to_visited_set_ordered _ _ _)
    as [[v1 d1]|] eqn:H1; [discriminate|].
  destruct (EncodeLayout.compute_max_degree_var_ordered _ _) as [[v2 d2]|] eqn:H2; [discriminate|].
  intros _ v Hv.
  unfold EncodeLayout.compute_max_degree_var_ordered in H2.
  apply (fold_mstep_None ctx.(dep_graph).(nodes) (EncodeLayout.compute_degree ctx.(dep_graph)) cs None)
    in H2.
  destruct H2 as [_ H2]. apply H2; exact Hv.
Qed.

(*----dedup: membership and NoDup----*)

(* [dedup] keeps exactly the not-yet-seen members of the list. *)
Lemma dedup_in (l : list var) : forall (seen : var_node_set) (v : var),
  In v (dedup seen l) <-> (In v l /\ map.get seen v = None).
Proof.
  induction l as [|x l IH]; intros seen v; simpl.
  - split; [intros [] | intros [[] _]].
  - destruct (map.get seen x) as [u|] eqn:Hx.
    + rewrite IH. split.
      * intros [Hin Hsv]. split; [right; exact Hin | exact Hsv].
      * intros [[<-|Hin] Hsv]; [rewrite Hx in Hsv; discriminate | split; assumption].
    + simpl. rewrite IH. split.
      * intros [<- | [Hin Hsv]].
        -- split; [left; reflexivity | exact Hx].
        -- destruct (var_eqb_spec x v) as [->|Hne].
           ++ rewrite map.get_put_same in Hsv. discriminate.
           ++ rewrite (map.get_put_diff seen v tt x (not_eq_sym Hne)) in Hsv.
              split; [right; exact Hin | exact Hsv].
      * intros [[<-|Hin] Hsv].
        -- left; reflexivity.
        -- destruct (var_eqb_spec x v) as [->|Hne].
           ++ left; reflexivity.
           ++ right. split;
                [exact Hin | rewrite (map.get_put_diff seen v tt x (not_eq_sym Hne)); exact Hsv].
Qed.

Lemma dedup_NoDup (l : list var) : forall (seen : var_node_set), NoDup (dedup seen l).
Proof.
  induction l as [|x l IH]; intros seen; simpl; [constructor|].
  destruct (map.get seen x) eqn:Hx; [apply IH|].
  constructor; [|apply IH].
  rewrite dedup_in. intros [_ Hc]. rewrite map.get_put_same in Hc. discriminate.
Qed.

(*----bare hypotheses: collected vars coincide with the variable ordering's vars----*)

Lemma bare_collect_vars_fact (h : lowered_fact) :
  Forall (fun e => exists v, e = var_expr v) h.(Datalog.clause_args) ->
  collect_vars_fact h = compute_var_order h.
Proof.
  unfold EncodeLayout.collect_vars_fact, EncodeLayout.compute_var_order.
  induction h.(Datalog.clause_args) as [|a args IH]; intros Hb; simpl; [reflexivity|].
  inversion Hb as [|x l [v ->] Hb']; subst. simpl. f_equal. apply IH; exact Hb'.
Qed.

Lemma bare_collect_vars_hyps (hyps : list lowered_fact) :
  Forall (fun h => Forall (fun e => exists v, e = var_expr v) h.(Datalog.clause_args)) hyps ->
  collect_vars_hyps hyps = flat_map compute_var_order hyps.
Proof.
  unfold EncodeLayout.collect_vars_hyps.
  induction hyps as [|h hyps IH]; intros Hb; simpl; [reflexivity|].
  inversion Hb as [|x l Hbh Hb']; subst.
  rewrite (bare_collect_vars_fact h Hbh), (IH Hb'). reflexivity.
Qed.

(*----the greedy loop: NoDup + subset + full coverage----*)

Notation cvo_h := (@EncodeLayout.compute_variable_ordering_ordered_h var var_node_set var_edge_set).

(* [innode]/[node_count]: how many candidates are still graph nodes (the loop's measure). *)
Definition innode (ns : var_node_set) (v : var) : bool :=
  match map.get ns v with Some _ => true | None => false end.
Definition node_count (ns : var_node_set) (cs : list var) : nat :=
  length (filter (innode ns) cs).

Lemma cvo_h_S (ctx : ordering_context) (cs : list var) (fuel : nat) :
  cvo_h ctx cs (S fuel)
  = match choose ctx cs with Some v => cvo_h (visit_node v ctx) cs fuel | None => ctx end.
Proof. reflexivity. Qed.

Lemma visit_order (v : var) (ctx : ordering_context) :
  (visit_node v ctx).(order) = v :: ctx.(order).
Proof. reflexivity. Qed.
Lemma visit_nodes (v : var) (ctx : ordering_context) :
  (visit_node v ctx).(dep_graph).(nodes) = map.remove ctx.(dep_graph).(nodes) v.
Proof. reflexivity. Qed.

(* Two filters that disagree only at one (present, NoDup) element differ in count by one. *)
Lemma filter_diff_one (f g : var -> bool) (cs : list var) (v : var) :
  NoDup cs -> In v cs -> f v = true -> g v = false ->
  (forall w, w <> v -> g w = f w) ->
  length (filter g cs) = pred (length (filter f cs)).
Proof.
  intros Hnd Hin Hfv Hgv Hdiff.
  induction cs as [|x cs IH]; simpl in Hin; [contradiction|].
  inversion Hnd as [|x0 cs0 Hxnin Hnd' Heq]; subst.
  simpl. destruct Hin as [<- | Hin].
  - rewrite Hfv, Hgv. simpl.
    rewrite (filter_ext_in g f cs); [reflexivity|].
    intros w Hw. apply Hdiff. intros ->. apply Hxnin; exact Hw.
  - rewrite (Hdiff x ltac:(intros ->; apply Hxnin; exact Hin)).
    destruct (f x) eqn:Hfx; simpl.
    + rewrite (IH Hnd' Hin).
      assert (Hge : 1 <= length (filter f cs)).
      { destruct (filter f cs) eqn:Ef; [|simpl; lia].
        assert (Hvf : In v (filter f cs)) by (apply filter_In; split; assumption).
        rewrite Ef in Hvf. destruct Hvf. }
      lia.
    + apply (IH Hnd' Hin).
Qed.

Lemma node_count_remove (ns : var_node_set) (cs : list var) (v : var) :
  NoDup cs -> In v cs -> map.get ns v <> None ->
  node_count (map.remove ns v) cs = pred (node_count ns cs).
Proof.
  intros Hnd Hin Hne. unfold node_count.
  apply (filter_diff_one (innode ns) (innode (map.remove ns v)) cs v Hnd Hin).
  - unfold innode. destruct (map.get ns v); [reflexivity | exfalso; apply Hne; reflexivity].
  - unfold innode. rewrite map.get_remove_same. reflexivity.
  - intros w Hwv. unfold innode. rewrite (map.get_remove_diff ns w v Hwv). reflexivity.
Qed.

Lemma node_count_zero (ns : var_node_set) (cs : list var) :
  node_count ns cs = 0 -> forall v, In v cs -> map.get ns v = None.
Proof.
  unfold node_count. intros H v Hv.
  destruct (map.get ns v) as [u|] eqn:Hg; [|reflexivity].
  exfalso. assert (Hvf : In v (filter (innode ns) cs)).
  { apply filter_In. split; [exact Hv | unfold innode; rewrite Hg; reflexivity]. }
  destruct (filter (innode ns) cs); [destruct Hvf | simpl in H; discriminate].
Qed.

(* The loop, run with enough fuel, produces a duplicate-free ordering whose elements are
   exactly the candidates: NoDup, [order ⊆ cs], and [cs ⊆ order]. *)
Lemma cvo_h_spec (cs : list var) (Hcs : NoDup cs) :
  forall (fuel : nat) (ctx : ordering_context),
  NoDup ctx.(order) ->
  (forall w, In w ctx.(order) -> In w cs) ->
  (forall w, In w ctx.(order) -> map.get ctx.(dep_graph).(nodes) w = None) ->
  (forall w, In w cs -> In w ctx.(order) \/ map.get ctx.(dep_graph).(nodes) w <> None) ->
  node_count ctx.(dep_graph).(nodes) cs <= fuel ->
  NoDup (cvo_h ctx cs fuel).(order) /\
  (forall w, In w (cvo_h ctx cs fuel).(order) -> In w cs) /\
  (forall w, In w cs -> In w (cvo_h ctx cs fuel).(order)).
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros ctx Hnd Hsub Hrm Hk Hcount.
  - assert (Hz : node_count ctx.(dep_graph).(nodes) cs = 0) by lia.
    split; [exact Hnd | split; [exact Hsub|]].
    intros w Hw. destruct (Hk w Hw) as [Ho | Hne]; [exact Ho|].
    exfalso. apply Hne. apply (node_count_zero _ _ Hz w Hw).
  - rewrite cvo_h_S. destruct (choose ctx cs) as [v|] eqn:Hchoose.
    + destruct (choose_Some ctx cs v Hchoose) as [Hvcs Hvne].
      assert (Hvno : ~ In v ctx.(order)) by (intros Hvo; apply Hvne; apply Hrm; exact Hvo).
      apply IH.
      * rewrite visit_order. constructor; [exact Hvno | exact Hnd].
      * intros w. rewrite visit_order. intros [<- | Hw]; [exact Hvcs | apply Hsub; exact Hw].
      * intros w. rewrite visit_order, visit_nodes. intros [<- | Hw].
        -- rewrite map.get_remove_same. reflexivity.
        -- assert (Hwv : w <> v) by (intros ->; apply Hvno; exact Hw).
           rewrite (map.get_remove_diff _ w v Hwv). apply Hrm; exact Hw.
      * intros w Hw. rewrite visit_order, visit_nodes.
        destruct (Hk w Hw) as [Ho | Hne].
        -- left; right; exact Ho.
        -- destruct (var_eqb_spec w v) as [->|Hwv].
           ++ left; left; reflexivity.
           ++ right. rewrite (map.get_remove_diff _ w v Hwv). exact Hne.
      * rewrite visit_nodes.
        rewrite (node_count_remove ctx.(dep_graph).(nodes) cs v Hcs Hvcs Hvne). lia.
    + split; [exact Hnd | split; [exact Hsub|]].
      intros w Hw. destruct (Hk w Hw) as [Ho | Hne]; [exact Ho|].
      exfalso. apply Hne. apply (choose_None ctx cs Hchoose w Hw).
Qed.

(*----every collected variable is a node of the dependency graph (bare fragment)----*)

(* The reverse-edge [map.fold] inside [add_arg_edges] leaves the node set unchanged. *)
Lemma addarg_fold_nodes (F : var_graph -> var -> unit -> var_graph)
    (g0 : var_graph) (cv : var_node_set) :
  (forall acc u x, (F acc u x).(nodes) = acc.(nodes)) ->
  (map.fold F g0 cv).(nodes) = g0.(nodes).
Proof.
  intros HF.
  apply (map.fold_spec (fun (_ : var_node_set) (g : var_graph) => g.(nodes) = g0.(nodes)) F g0).
  - reflexivity.
  - intros k val m r _ Hr. rewrite HF. exact Hr.
Qed.

(* So adding a bare argument [var_expr v] puts exactly [v] into the node set. *)
Lemma add_arg_edges_LVar_nodes (v : var) (g : var_graph) (cv : var_node_set) :
  (EncodeLayout.add_arg_edges (var_expr v) g cv).(nodes) = map.put g.(nodes) v tt.
Proof.
  cbn [EncodeLayout.add_arg_edges].
  erewrite addarg_fold_nodes; [reflexivity | intros acc u x; reflexivity].
Qed.

Lemma add_args_edges_mono (args : list (@HardwareProgram.lowered_expr var)) :
  forall (g : var_graph) (seen : var_node_set) (w : var),
  Forall (fun e => exists u, e = var_expr u) args ->
  map.get g.(nodes) w <> None ->
  map.get (EncodeLayout.add_args_edges args g seen).(nodes) w <> None.
Proof.
  induction args as [|a args IH]; intros g seen w Hb Hg; simpl; [exact Hg|].
  inversion Hb as [|x l [u ->] Hb']; subst.
  apply (IH (EncodeLayout.add_arg_edges (var_expr u) g seen) (map.put seen u tt) w Hb').
  rewrite add_arg_edges_LVar_nodes.
  destruct (var_eqb_spec u w) as [->|Hne].
  - rewrite map.get_put_same. discriminate.
  - rewrite (map.get_put_diff g.(nodes) w tt u (not_eq_sym Hne)). exact Hg.
Qed.

Lemma add_args_edges_covers (args : list (@HardwareProgram.lowered_expr var)) :
  forall (g : var_graph) (seen : var_node_set) (w : var),
  Forall (fun e => exists u, e = var_expr u) args ->
  In (var_expr w) args ->
  map.get (EncodeLayout.add_args_edges args g seen).(nodes) w <> None.
Proof.
  induction args as [|a args IH]; intros g seen w Hb Hin; simpl in Hin; [contradiction|].
  inversion Hb as [|x l [u ->] Hb']; subst. simpl. destruct Hin as [Heq | Hin].
  - injection Heq as ->.
    apply (add_args_edges_mono args (EncodeLayout.add_arg_edges (var_expr w) g seen)
             (map.put seen w tt) w Hb').
    rewrite add_arg_edges_LVar_nodes, map.get_put_same. discriminate.
  - apply (IH (EncodeLayout.add_arg_edges (var_expr u) g seen) (map.put seen u tt) w Hb' Hin).
Qed.

(* Bare: a fact's collected variables are exactly its [var_expr] arguments. *)
Lemma bare_in_collect_args (args : list (@HardwareProgram.lowered_expr var)) (w : var) :
  Forall (fun e => exists u, e = var_expr u) args ->
  (In w (flat_map EncodeLayout.collect_vars_expr args) <-> In (var_expr w) args).
Proof.
  induction args as [|a args IH]; intros Hb; simpl; [reflexivity|].
  inversion Hb as [|x l [u ->] Hb']; subst. simpl. rewrite (IH Hb'). split.
  - intros [<- | Hin]; [left; reflexivity | right; exact Hin].
  - intros [Heq | Hin]; [injection Heq as ->; left; reflexivity | right; exact Hin].
Qed.

Lemma add_hyp_edges_mono (h : lowered_fact) (g : var_graph) (w : var) :
  Forall (fun e => exists u, e = var_expr u) h.(Datalog.clause_args) ->
  map.get g.(nodes) w <> None ->
  map.get (EncodeLayout.add_hyp_edges h g).(nodes) w <> None.
Proof. unfold EncodeLayout.add_hyp_edges. intros. apply add_args_edges_mono; assumption. Qed.

Lemma add_hyp_edges_covers (h : lowered_fact) (g : var_graph) (w : var) :
  Forall (fun e => exists u, e = var_expr u) h.(Datalog.clause_args) ->
  In w (collect_vars_fact h) ->
  map.get (EncodeLayout.add_hyp_edges h g).(nodes) w <> None.
Proof.
  unfold EncodeLayout.add_hyp_edges, EncodeLayout.collect_vars_fact. intros Hb Hin.
  apply add_args_edges_covers; [exact Hb | apply (bare_in_collect_args h.(Datalog.clause_args) w Hb); exact Hin].
Qed.

(* The whole dependency graph: every collected hypothesis variable is a node. *)
Lemma create_dep_graph_covers (hyps : list lowered_fact) :
  Forall (fun h => Forall (fun e => exists u, e = var_expr u) h.(Datalog.clause_args)) hyps ->
  forall w, In w (collect_vars_hyps hyps) ->
  map.get (EncodeLayout.create_dependency_graph hyps).(nodes) w <> None.
Proof.
  unfold EncodeLayout.create_dependency_graph, EncodeLayout.collect_vars_hyps.
  (* generalize the initial accumulator graph *)
  assert (Hgen : forall (hs : list lowered_fact) (g : var_graph) w,
            Forall (fun h => Forall (fun e => exists u, e = var_expr u) h.(Datalog.clause_args)) hs ->
            (In w (flat_map collect_vars_fact hs) \/ map.get g.(nodes) w <> None) ->
            map.get (fold_left (fun acc h => EncodeLayout.add_hyp_edges h acc) hs g).(nodes) w
              <> None).
  { intros hs. induction hs as [|h hs IH]; intros g w Hb Hor; simpl.
    - destruct Hor as [[] | Hg]; exact Hg.
    - inversion Hb as [|x l Hbh Hb']; subst.
      apply IH; [exact Hb'|].
      simpl in Hor. destruct Hor as [Hin | Hg].
      + apply in_app_or in Hin. destruct Hin as [Hh | Hrest].
        * right. apply add_hyp_edges_covers; [exact Hbh | exact Hh].
        * left. exact Hrest.
      + right. apply add_hyp_edges_mono; [exact Hbh | exact Hg]. }
  intros Hb w Hin. apply (Hgen hyps EncodeLayout.empty_var_graph w Hb). left. exact Hin.
Qed.

(*----assembly: the produced ordering is NoDup and exactly the hypothesis variables----*)

Lemma length_filter_le {A} (f : A -> bool) (l : list A) : length (filter f l) <= length l.
Proof. induction l as [|x l IH]; simpl; [lia | destruct (f x); simpl; lia]. Qed.

Notation compute_variable_ordering_ordered :=
  (@EncodeLayout.compute_variable_ordering_ordered var var_node_set var_edge_set).
Notation create_dependency_graph :=
  (@EncodeLayout.create_dependency_graph var var_node_set var_edge_set).
Notation initial_ordering_context :=
  (@EncodeLayout.initial_ordering_context var var_node_set var_edge_set).

(* MAIN ordering correctness: for bare hypotheses, the variable ordering computed over the
   dependency graph is duplicate-free and contains exactly the hypothesis variables.  This
   discharges [hw_rule_correct]'s [NoDup ord], coverage, and subset hypotheses. *)
Lemma compute_variable_ordering_ordered_correct (hyps : list lowered_fact) :
  Forall (fun h => Forall (fun e => exists u, e = var_expr u) h.(Datalog.clause_args)) hyps ->
  NoDup (compute_variable_ordering_ordered (create_dependency_graph hyps) hyps) /\
  (forall v, In v (compute_variable_ordering_ordered (create_dependency_graph hyps) hyps) ->
             In v (flat_map compute_var_order hyps)) /\
  (forall v, In v (flat_map compute_var_order hyps) ->
             In v (compute_variable_ordering_ordered (create_dependency_graph hyps) hyps)).
Proof.
  intros Hb.
  assert (Hcv : collect_vars_hyps hyps = flat_map compute_var_order hyps)
    by (apply bare_collect_vars_hyps; exact Hb).
  unfold EncodeLayout.compute_variable_ordering_ordered. cbv zeta.
  set (g := create_dependency_graph hyps).
  set (cs := EncodeLayout.hyp_var_order hyps).
  assert (HcandIn : forall v, In v cs <-> In v (collect_vars_hyps hyps)).
  { intros v. unfold cs, EncodeLayout.hyp_var_order. rewrite dedup_in, map.get_empty.
    split; [intros [H _]; exact H | intros H; split; [exact H | reflexivity]]. }
  assert (Hcs : NoDup cs) by (unfold cs, EncodeLayout.hyp_var_order; apply dedup_NoDup).
  assert (HP1 : NoDup (initial_ordering_context g).(order)) by (simpl; constructor).
  assert (HP2 : forall w, In w (initial_ordering_context g).(order) -> In w cs)
    by (simpl; intros w []).
  assert (HP3 : forall w, In w (initial_ordering_context g).(order) ->
                  map.get (initial_ordering_context g).(dep_graph).(nodes) w = None)
    by (simpl; intros w []).
  assert (HP4 : forall w, In w cs -> In w (initial_ordering_context g).(order) \/
                  map.get (initial_ordering_context g).(dep_graph).(nodes) w <> None).
  { intros w Hw. right. simpl.
    apply create_dep_graph_covers; [exact Hb | exact (proj1 (HcandIn w) Hw)]. }
  assert (HP5 : node_count (initial_ordering_context g).(dep_graph).(nodes) cs <= length cs)
    by (unfold node_count; apply length_filter_le).
  destruct (cvo_h_spec cs Hcs (length cs) (initial_ordering_context g) HP1 HP2 HP3 HP4 HP5)
    as [Hnd [Hsub Hcov]].
  split; [| split].
  - apply NoDup_rev. exact Hnd.
  - intros v Hv. rewrite <- in_rev in Hv. rewrite <- Hcv.
    exact (proj1 (HcandIn v) (Hsub v Hv)).
  - intros v Hv. rewrite <- in_rev. apply Hcov, (proj2 (HcandIn v)). rewrite <- Hcv in Hv. exact Hv.
Qed.

End OrderingCorrect.

(*============================================================================*)
(*  Trie registration at the node level: [compile_node]'s trie table has        *)
(*  duplicate-free ids (so [lookup_trie] finds each registered trie), and the    *)
(*  table grows monotonically across rules.                                      *)
(*============================================================================*)

Section RegisterNode.

Import ResultMonadNotations.
Open Scope result_monad_scope.

Context {rel var fn aggregator : Type}.
Context {var_eqb : var -> var -> bool}
        {var_eqb_spec : forall x y : var, BoolSpec (x = y) (x <> y) (var_eqb x y)}.
Context {Node : Type}.
Context {node_id : Type}
        {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.
Context {node_id_set : map.map node_id unit}.
Context {forwarding_table : map.map rel_id (list (@DistributedHardwareProgram.destination node_id))}.
Context {rel_dependency_map : map.map rel_id node_id_set}.
Context {fn_id_map : map.map fn fn_id}.
Context {rel_relid_map : map.map rel rel_id}.
Context {var_node_set : map.map var unit}.
Context {var_edge_set : map.map var var_node_set}.
Context {var_idx_map : map.map var nat}.

Notation global_context :=
  (@EncodeLayout.global_context rel fn Node node_id node_id_set rel_dependency_map fn_id_map rel_relid_map).
Notation node_context := (@EncodeLayout.node_context node_id).
Notation lowered_rule := (@HardwareProgram.lowered_rule var aggregator).
Notation lowered_program := (@HardwareProgram.lowered_program var aggregator).
Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).
Notation compile_rule :=
  (@EncodeLayout.compile_rule rel var fn aggregator var_eqb Node node_id node_id_set rel_dependency_map
     fn_id_map rel_relid_map var_node_set var_edge_set var_idx_map).
Notation compile_node :=
  (@EncodeLayout.compile_node rel var fn aggregator var_eqb Node node_id node_id_set forwarding_table
     rel_dependency_map fn_id_map rel_relid_map var_node_set var_edge_set var_idx_map).

(* [compile_rule] = [compile_hyps] (which threads the trie context) then [compile_concls]
   (which leaves the context untouched), so it preserves [wf_nc] and grows [nctries]. *)
Lemma compile_rule_reg (rule : lowered_rule) (gc : global_context) (nc : node_context)
    (hr : hardware_rule) (nc' : node_context) :
  compile_rule rule gc nc = Success (hr, nc') ->
  wf_nc nc -> wf_nc nc' /\ incl nc.(nctries) nc'.(nctries).
Proof.
  unfold EncodeLayout.compile_rule. intros H Hwf.
  destruct rule as [rconcls rhyps | rconcls rhyps | cr ag hyp_rel];
    cbv zeta in H; [| discriminate | discriminate].
  match type of H with
  | context [EncodeLayout.compile_hyps ?a ?b ?c ?d ?e] =>
      destruct (EncodeLayout.compile_hyps a b c d e) as [q nc''] eqn:Hch
  end.
  cbn beta iota zeta in H.
  match type of H with
  | context [EncodeLayout.compile_concls ?a ?b ?c] =>
      destruct (EncodeLayout.compile_concls a b c) as [concls|] eqn:Hcc
  end; cbn beta iota zeta in H; [|discriminate].
  injection H as _ <-.
  destruct (compile_hyps_reg rhyps _ gc nc q nc'' Hch Hwf) as [Hwf'' [Hmono _]].
  split; assumption.
Qed.

(* Errored accumulator stays errored across the [compile_node] fold. *)
Lemma compile_node_fold_error (gc : global_context) (prog : lowered_program) :
  forall (e : dlist.dlist),
  fold_left (fun acc rule =>
      '(rules, ncontext) <- acc ;;
      '(hr, ncontext) <- compile_rule rule gc ncontext ;;
      Success (hr :: rules, ncontext)%list) prog (Failure e) = Failure e.
Proof. induction prog as [|r prog IH]; intros e; simpl; [reflexivity | apply IH]. Qed.

(* The [compile_node] fold preserves [wf_nc] and grows [nctries]. *)
Lemma compile_node_fold_wf (gc : global_context) (prog : lowered_program) :
  forall (rules0 : list hardware_rule) (nc0 : node_context)
         (res : list hardware_rule) (nc1 : node_context),
  fold_left (fun acc rule =>
      '(rules, ncontext) <- acc ;;
      '(hr, ncontext) <- compile_rule rule gc ncontext ;;
      Success (hr :: rules, ncontext)%list) prog (Success (rules0, nc0)) = Success (res, nc1) ->
  wf_nc nc0 -> wf_nc nc1 /\ incl nc0.(nctries) nc1.(nctries).
Proof.
  induction prog as [|r prog IH]; intros rules0 nc0 res nc1 H Hwf; simpl in H.
  - injection H as _ <-. split; [exact Hwf | apply incl_refl].
  - destruct (compile_rule r gc nc0) as [[hr nc0']|] eqn:Hcr; cbn beta iota in H.
    + destruct (compile_rule_reg r gc nc0 hr nc0' Hcr Hwf) as [Hwf' Hmono].
      destruct (IH (hr :: rules0) nc0' res nc1 H Hwf') as [Hwf1 Hmono1].
      split; [exact Hwf1 | apply (incl_tran Hmono Hmono1)].
    + rewrite compile_node_fold_error in H. discriminate.
Qed.

(* MAIN registration fact: the node's trie table has duplicate-free trie ids, so [lookup_trie]
   returns exactly the trie for any registered id (see [lookup_trie_some]). *)
Lemma compile_node_wf (node : node_id) (prog : lowered_program) (gc : global_context)
    (ninfo : node_info) :
  compile_node node prog gc = Success ninfo ->
  NoDup (map (fun t => t.(tid)) ninfo.(ntries)).
Proof.
  unfold EncodeLayout.compile_node. intros H.
  match type of H with
  | context [fold_left ?F prog ?init] =>
      destruct (fold_left F prog init) as [[rules nc1]|] eqn:Hfold
  end; cbn beta iota zeta in H; [|discriminate].
  injection H as <-.
  assert (Hwf0 : wf_nc (EncodeLayout.initial_node_context node))
    by (split; [intros t [] | constructor]).
  destruct (compile_node_fold_wf gc prog [] (EncodeLayout.initial_node_context node) rules nc1
              Hfold Hwf0) as [[_ Hnd] _].
  cbn [DistributedHardwareProgram.ntries]. rewrite map_rev. apply NoDup_rev. exact Hnd.
Qed.

End RegisterNode.

(*============================================================================*)
(*  Capstone: a compiled node implements its (lowered) datalog program.         *)
(*============================================================================*)

Section NodeCorrect.

Import ResultMonadNotations.
Open Scope result_monad_scope.

Context {rel var fn aggregator T : Type}.
Context {var_eqb : var -> var -> bool}
        {var_eqb_spec : forall x y : var, BoolSpec (x = y) (x <> y) (var_eqb x y)}.
Context `{sig : signature nat aggregator T}.
Context {context : map.map var T} {context_ok : map.ok context}.
Context {var_idx_map : map.map var nat} {var_idx_map_ok : map.ok var_idx_map}.
Context {var_node_set : map.map var unit} {var_node_set_ok : map.ok var_node_set}.
Context {var_edge_set : map.map var var_node_set}.
Context {Node : Type}.
Context {node_id : Type}
        {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.
Context {node_id_set : map.map node_id unit}.
Context {forwarding_table : map.map rel_id (list (@DistributedHardwareProgram.destination node_id))}.
Context {rel_dependency_map : map.map rel_id node_id_set}.
Context {fn_id_map : map.map fn fn_id}.
Context {rel_relid_map : map.map rel rel_id}.

Notation global_context :=
  (@EncodeLayout.global_context rel fn Node node_id node_id_set rel_dependency_map fn_id_map rel_relid_map).
Notation node_context := (@EncodeLayout.node_context node_id).
Notation lowered_rule := (@HardwareProgram.lowered_rule var aggregator).
Notation lowered_program := (@HardwareProgram.lowered_program var aggregator).
Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).
Notation lowered_fact := (@HardwareProgram.lowered_fact var).
Notation compile_rule :=
  (@EncodeLayout.compile_rule rel var fn aggregator var_eqb Node node_id node_id_set rel_dependency_map
     fn_id_map rel_relid_map var_node_set var_edge_set var_idx_map).
Notation compile_node :=
  (@EncodeLayout.compile_node rel var fn aggregator var_eqb Node node_id node_id_set forwarding_table
     rel_dependency_map fn_id_map rel_relid_map var_node_set var_edge_set var_idx_map).

(* PER-RULE: a compiled rule (whose post-context tries are all in the node table [tries], which
   has unique ids) matches its lowered datalog rule -- by discharging every hypothesis of
   [hw_rule_correct] from the ordering / hypothesis / conclusion / registration lemmas. *)
Lemma compile_rule_matches (rule : lowered_rule) (gc : global_context) (nc nc' : node_context)
    (hr : hardware_rule) (tries : list trie)
    (env : list (Datalog.fact rel_id T) -> rel_id -> list T -> Prop) :
  bare_rule rule ->
  wf_nc nc ->
  compile_rule rule gc nc = Success (hr, nc') ->
  incl nc'.(nctries) tries ->
  NoDup (map (fun t => t.(tid)) tries) ->
  hw_rule_matches tries env rule hr.
Proof.
  intros Hbare Hwf H Hincl Hndt.
  destruct rule as [rconcls rhyps | rconcls rhyps | cr ag hyp_rel]; cbn in Hbare;
    [| contradiction | contradiction].
  destruct Hbare as [Hbh Hbc].
  unfold EncodeLayout.compile_rule in H. cbv zeta in H.
  set (ord := compute_variable_ordering_ordered (create_dependency_graph rhyps) rhyps) in *.
  match type of H with
  | context [EncodeLayout.compile_hyps ?a ?b ?c ?d ?e] =>
      destruct (EncodeLayout.compile_hyps a b c d e) as [q nc''] eqn:Hch
  end.
  cbn beta iota zeta in H.
  match type of H with
  | context [EncodeLayout.compile_concls ?a ?b ?c] =>
      destruct (EncodeLayout.compile_concls a b c) as [concls|] eqn:Hcc
  end; cbn beta iota zeta in H; [|discriminate].
  injection H as <- <-.
  destruct (compile_hyps_full rhyps ord gc nc q nc'' Hch Hwf)
    as [_ [_ [tb [Hq [Hlentb [HFtt Htbin]]]]]].
  pose proof (compile_concls_corr rconcls gc ord concls Hbc Hcc) as Hconcl.
  destruct (compute_variable_ordering_ordered_correct rhyps Hbh) as [Hnd [Hsub Hcov]].
  apply (hw_rule_correct rconcls rhyps
           {| hhyps := q; hconcls := concls;
              hsig := map (fun h => (h.(Datalog.clause_rel), length h.(Datalog.clause_args))) rhyps |}
           env ord tb tries {| tid := 0; trel := 0; tperm := [] |}
           {| Datalog.clause_rel := 0; Datalog.clause_args := [] |}).
  - exact Hnd.
  - exact Hbh.
  - exact Hbc.
  - exact Hlentb.
  - exact Hcov.
  - exact Hsub.
  - exact Hq.
  - reflexivity.
  - exact Hconcl.
  - intros i Hi.
    apply Forall2_nth_error_iff in HFtt. destruct HFtt as [_ Hpt].
    assert (Hitb : i < length tb) by (rewrite Hlentb; exact Hi).
    assert (Pt : nth_error tb i = Some (nth i tb {| tid := 0; trel := 0; tperm := [] |}))
      by (apply nth_error_nth'; exact Hitb).
    assert (Ph : nth_error rhyps i = Some (nth i rhyps {| Datalog.clause_rel := 0; Datalog.clause_args := [] |}))
      by (apply nth_error_nth'; exact Hi).
    specialize (Hpt i _ _ Pt Ph). destruct Hpt as [Htrel Htperm].
    split; [exact Htrel | split; [exact Htperm |]].
    apply lookup_trie_some; [|exact Hndt].
    apply Hincl. apply Htbin. apply nth_In. exact Hitb.
Qed.

(* The [compile_node] fold: every compiled rule matches its datalog rule against the node's
   final trie table (each rule's tries are a subset of the final table, by monotonicity). *)
Lemma compile_node_fold_matches (gc : global_context) (tries : list trie) (prog : lowered_program)
    (env : list (Datalog.fact rel_id T) -> rel_id -> list T -> Prop) :
  forall (rules0 : list hardware_rule) (nc0 : node_context)
         (compiled_rev : list hardware_rule) (nc_final : node_context),
  fold_left (fun acc rule =>
      '(rules, ncontext) <- acc ;;
      '(hr, ncontext) <- compile_rule rule gc ncontext ;;
      Success (hr :: rules, ncontext)%list) prog (Success (rules0, nc0))
    = Success (compiled_rev, nc_final) ->
  Forall bare_rule prog ->
  wf_nc nc0 -> incl nc_final.(nctries) tries -> NoDup (map (fun t => t.(tid)) tries) ->
  exists hrs, compiled_rev = (rev hrs ++ rules0)%list /\
              Forall2 (fun rule hr => hw_rule_matches tries env rule hr) prog hrs.
Proof.
  induction prog as [|r prog IH];
    intros rules0 nc0 compiled_rev nc_final H Hbare Hwf Hincl Hndt; simpl in H.
  - injection H as <- <-. exists []. split; [reflexivity | constructor].
  - inversion Hbare as [|x l Hbr Hbprog]; subst.
    destruct (compile_rule r gc nc0) as [[hr nc0']|] eqn:Hcr; cbn beta iota in H.
    + destruct (compile_rule_reg r gc nc0 hr nc0' Hcr Hwf) as [Hwf' _].
      destruct (compile_node_fold_wf gc prog (hr :: rules0) nc0' compiled_rev nc_final H Hwf')
        as [_ Hmonotail].
      assert (Hinc' : incl nc0'.(nctries) tries) by (apply (incl_tran Hmonotail Hincl)).
      pose proof (compile_rule_matches r gc nc0 nc0' hr tries env Hbr Hwf Hcr Hinc' Hndt) as Hm.
      destruct (IH (hr :: rules0) nc0' compiled_rev nc_final H Hbprog Hwf' Hincl Hndt)
        as [hrs [Hcomp HF]].
      exists (hr :: hrs). split.
      * simpl. rewrite Hcomp, <- app_assoc. reflexivity.
      * constructor; [exact Hm | exact HF].
    + rewrite compile_node_fold_error in H. discriminate.
Qed.

Lemma Forall2_map_lrule (tries : list trie) (prog : lowered_program) (hrs : list hardware_rule)
    (env : list (Datalog.fact rel_id T) -> rel_id -> list T -> Prop) :
  Forall2 (fun rule hr => hw_rule_matches tries env rule hr) prog hrs ->
  Forall2 (hw_rule_matches tries env) (prog) hrs.
Proof. intros HF. induction HF; simpl; constructor; assumption. Qed.

(* Per node: every compiled hardware rule matches its source rule against the node's trie table.
   This is exactly the per-node condition [EncodeDistributed.node_rules_match] needs. *)
Lemma compile_node_matches (node : node_id) (prog : lowered_program) (gc : global_context)
    (ninfo : node_info) (env : list (Datalog.fact rel_id T) -> rel_id -> list T -> Prop) :
  Forall bare_rule prog ->
  compile_node node prog gc = Success ninfo ->
  Forall2 (hw_rule_matches ninfo.(ntries) env) (prog) ninfo.(nprogram).
Proof.
  intros Hbare H.
  pose proof (compile_node_wf node prog gc ninfo H) as Hndt.
  unfold EncodeLayout.compile_node in H.
  match type of H with
  | context [fold_left ?F prog ?init] =>
      destruct (fold_left F prog init) as [[compiled_rev nc_final]|] eqn:Hfold
  end; cbn beta iota zeta in H; [|discriminate].
  injection H as <-.
  assert (Hwf0 : wf_nc (EncodeLayout.initial_node_context node))
    by (split; [intros t [] | constructor]).
  assert (Hincl : incl nc_final.(nctries) (rev nc_final.(nctries)))
    by (intros t Ht; rewrite <- in_rev; exact Ht).
  cbn [DistributedHardwareProgram.ntries] in Hndt, Hincl |- *.
  cbn [DistributedHardwareProgram.nprogram].
  destruct (compile_node_fold_matches gc (rev nc_final.(nctries)) prog env []
              (EncodeLayout.initial_node_context node) compiled_rev nc_final
              Hfold Hbare Hwf0 Hincl Hndt) as [hrs [Hcomp HF]].
  rewrite Hcomp, app_nil_r, rev_involutive.
  apply Forall2_map_lrule. exact HF.
Qed.

(* CAPSTONE (single node): a successfully-compiled node implements its lowered datalog program --
   the trie-join semantics of the node's hardware program derives exactly the facts the program
   (read as ordinary datalog over numeric ids) derives. *)
Theorem compile_node_correct (node : node_id) (prog : lowered_program) (gc : global_context)
    (ninfo : node_info) :
  Forall bare_rule prog ->
  compile_node node prog gc = Success ninfo ->
  node_implements ninfo.(ntries) ninfo.(nprogram) (prog).
Proof.
  intros Hbare H.
  apply (hw_node_correct ninfo.(ntries) (prog) ninfo.(nprogram)).
  apply (compile_node_matches node prog gc ninfo (Datalog.one_step_derives prog)); assumption.
Qed.

End NodeCorrect.

(*============================================================================*)
(*  Distributed correctness: a network whose nodes are all compiled by          *)
(*  [compile_node] implements the global datalog program, provided its          *)
(*  forwarding/topology is well-formed ([good_network]).  The per-node matching  *)
(*  is discharged from [compile_node_matches]; [good_network] (the forwarding-   *)
(*  table obligation) is the remaining side condition.                           *)
(*============================================================================*)

Section DistCorrect.

Context {rel var fn aggregator T : Type}.
Context {var_eqb : var -> var -> bool}
        {var_eqb_spec : forall x y : var, BoolSpec (x = y) (x <> y) (var_eqb x y)}.
Context `{sig : signature nat aggregator T}.
Context {context : map.map var T} {context_ok : map.ok context}.
Context {var_idx_map : map.map var nat} {var_idx_map_ok : map.ok var_idx_map}.
Context {var_node_set : map.map var unit} {var_node_set_ok : map.ok var_node_set}.
Context {var_edge_set : map.map var var_node_set}.
Context {Node : Type}.
Context {node_id : Type}
        {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.
Context {node_id_set : map.map node_id unit}.
Context {forwarding_table : map.map rel_id (list (@DistributedHardwareProgram.destination node_id))}.
Context {rel_dependency_map : map.map rel_id node_id_set}.
Context {fn_id_map : map.map fn fn_id}.
Context {rel_relid_map : map.map rel rel_id}.

Notation global_context :=
  (@EncodeLayout.global_context rel fn Node node_id node_id_set rel_dependency_map fn_id_map rel_relid_map).
Notation lowered_program := (@HardwareProgram.lowered_program var aggregator).
Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).
Notation compile_node :=
  (@EncodeLayout.compile_node rel var fn aggregator var_eqb Node node_id node_id_set forwarding_table
     rel_dependency_map fn_id_map rel_relid_map var_node_set var_edge_set var_idx_map).
Notation HwNetwork := (@EncodeDistributed.HwNetwork var aggregator T node_id).

(* The network's per-node hardware data (tries, program) and datalog layout are exactly what
   [compile_node] produces from the lowered program assigned to that node. *)
Definition compiled_network (hn : HwNetwork) (gc : global_context)
    (lprog_at : node_id -> lowered_program) : Prop :=
  forall n, exists ninfo,
    compile_node n (lprog_at n) gc = Success ninfo /\
    EncodeDistributed.hw_tries hn n = ninfo.(ntries) /\
    EncodeDistributed.hw_prog hn n = ninfo.(nprogram) /\
    (EncodeDistributed.hw_dnet hn).(layout) n = (lprog_at n).

(* Each compiled node's rules match its datalog rules -- so the whole network matches. *)
Lemma node_rules_match_of_compiled (hn : HwNetwork) (gc : global_context)
    (lprog_at : node_id -> lowered_program) :
  (forall n, Forall bare_rule (lprog_at n)) ->
  compiled_network hn gc lprog_at ->
  EncodeDistributed.node_rules_match hn.
Proof.
  intros Hbare Hcomp n.
  destruct (Hcomp n) as [ninfo [Hcn [Ht [Hp Hl]]]].
  rewrite Ht, Hp, Hl.
  apply (compile_node_matches n (lprog_at n) gc ninfo (fun _ _ _ => False)); [apply Hbare | exact Hcn].
Qed.

(* DISTRIBUTED CAPSTONE: a compiled network derives exactly the facts the global program does
   from the streaming base facts [Q], given a well-formed topology/forwarding
   ([good_network_streaming]).  The forwarding-table completeness for [generate_forwarding_table]
   (every producer/input node is a good source) is the remaining obligation. *)
Theorem compiled_dist_correct (hn : HwNetwork) (gc : global_context)
    (lprog_at : node_id -> lowered_program)
    (program : list (Datalog.rule rel_id var nat aggregator))
    (Q : Datalog.fact rel_id T -> Prop) :
  (forall n, Forall bare_rule (lprog_at n)) ->
  compiled_network hn gc lprog_at ->
  good_network_streaming (EncodeDistributed.hw_dnet hn) program Q ->
  forall f, EncodeDistributed.hw_net_prog_impl_fact hn f <-> DistributedDatalog.prog_impl_fact program Q f.
Proof.
  intros Hbare Hcomp Hgood.
  apply (EncodeDistributed.hw_dist_correct hn program Q);
    [exact (node_rules_match_of_compiled hn gc lprog_at Hbare Hcomp) | exact Hgood].
Qed.

End DistCorrect.

(*============================================================================*)
(*  Top-level [compile]: bridging its output back to per-node [compile_node].   *)
(*============================================================================*)

Section CompileTop.

Import ResultMonadNotations.
Open Scope result_monad_scope.

Context {rel var fn aggregator T : Type}.
Context {var_eqb : var -> var -> bool}
        {var_eqb_spec : forall x y : var, BoolSpec (x = y) (x <> y) (var_eqb x y)}.
Context `{sig : signature nat aggregator T}.
Context {context : map.map var T} {context_ok : map.ok context}.
Context {var_idx_map : map.map var nat} {var_idx_map_ok : map.ok var_idx_map}.
Context {var_node_set : map.map var unit} {var_node_set_ok : map.ok var_node_set}.
Context {var_edge_set : map.map var var_node_set}.
Context {Node : Type}.
Context {node_id : Type}
        {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.
Context {node_id_set : map.map node_id unit}.
Context {node_id_edge_set : map.map node_id node_id_set}.
Context {forwarding_table : map.map rel_id (list (@DistributedHardwareProgram.destination node_id))}.
Context {rel_dependency_map : map.map rel_id node_id_set}.
Context {fn_id_map : map.map fn fn_id}.
Context {rel_relid_map : map.map rel rel_id}.
Context {layout_map : map.map node_id (@HardwareProgram.program rel var fn aggregator)}
        {layout_map_ok : map.ok layout_map}.
Context {lowered_layout_map : map.map node_id (@HardwareProgram.lowered_program var aggregator)}
        {lowered_layout_map_ok : map.ok lowered_layout_map}.
Context {node_ftable_map : map.map node_id forwarding_table}.

Notation program := (@HardwareProgram.program rel var fn aggregator).
Notation lowered_program := (@HardwareProgram.lowered_program var aggregator).
Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).
Notation global_context :=
  (@EncodeLayout.global_context rel fn Node node_id node_id_set rel_dependency_map fn_id_map rel_relid_map).
Notation compile_node :=
  (@EncodeLayout.compile_node rel var fn aggregator var_eqb Node node_id node_id_set forwarding_table
     rel_dependency_map fn_id_map rel_relid_map var_node_set var_edge_set var_idx_map).
Notation compile_all_nodes :=
  (@EncodeLayout.compile_all_nodes rel var fn aggregator var_eqb Node node_id node_id_set forwarding_table
     rel_dependency_map fn_id_map rel_relid_map lowered_layout_map var_node_set var_edge_set
     var_idx_map).
Notation attach_forwarding_tables :=
  (@EncodeLayout.attach_forwarding_tables node_id forwarding_table node_ftable_map).
Notation global_rename_program :=
  (@EncodeLayout.global_rename_program rel var fn aggregator Node node_id node_id_set
     rel_dependency_map fn_id_map rel_relid_map).
Notation global_rename_rule_layout :=
  (@EncodeLayout.global_rename_rule_layout rel var fn aggregator Node node_id node_id_set
     rel_dependency_map fn_id_map rel_relid_map layout_map lowered_layout_map).
Notation compile_renamed_layout :=
  (@EncodeLayout.compile_renamed_layout rel var fn aggregator Node node_id node_id_set
     rel_dependency_map fn_id_map rel_relid_map layout_map lowered_layout_map).
Notation compile_global_context :=
  (@EncodeLayout.compile_global_context rel var fn aggregator Node node_id node_id_set
     rel_dependency_map fn_id_map rel_relid_map layout_map lowered_layout_map).
Notation fact_locations := (@EncodeLayout.fact_locations rel node_id).
Notation node_graph := (@EncodeLayout.node_graph node_id node_id_set node_id_edge_set).
Notation collect_global_names_layout :=
  (@EncodeLayout.collect_global_names_layout rel var fn aggregator Node node_id node_id_set
     rel_dependency_map fn_id_map rel_relid_map layout_map).
Notation initial_global_context :=
  (@EncodeLayout.initial_global_context rel fn Node node_id node_id_set rel_dependency_map fn_id_map
     rel_relid_map).
Notation compile :=
  (@EncodeLayout.compile rel var fn aggregator var_eqb Node node_id node_id_eqb node_id_set forwarding_table
     rel_dependency_map fn_id_map rel_relid_map layout_map lowered_layout_map var_node_set
     var_edge_set node_id_edge_set var_idx_map node_ftable_map).
Notation DNet := (@DistributedDatalog.DataflowNetwork rel_id var nat aggregator T node_id).
Notation HwNetwork := (@EncodeDistributed.HwNetwork var aggregator T node_id).

(* [attach_forwarding_tables] only rewrites the forwarding field; node id, trie table and
   hardware program are preserved. *)
Lemma attach_forwarding_tables_spec (ninfos : list node_info) (ftables : node_ftable_map)
    (ninfo' : node_info) :
  In ninfo' (attach_forwarding_tables ninfos ftables) ->
  exists ninfo, In ninfo ninfos /\
    ninfo'.(nid) = ninfo.(nid) /\ ninfo'.(ntries) = ninfo.(ntries) /\
    ninfo'.(nprogram) = ninfo.(nprogram).
Proof.
  unfold EncodeLayout.attach_forwarding_tables. intros H.
  apply in_map_iff in H. destruct H as [ninfo [Heq Hin]].
  exists ninfo. subst ninfo'. cbn. repeat split; [exact Hin | reflexivity..].
Qed.

(* Generic: folding [g] over a map (collecting [Success] results) yields, for each collected
   element, the source key/value it came from. *)
Lemma map_fold_result_in {V W : Type} {M : map.map node_id V} {Mok : map.ok M}
    (g : node_id -> V -> result W) (m0 : M) (ll : list W) :
  map.fold (fun acc node v => acc' <- acc ;; w <- g node v ;; Success (w :: acc')%list)
           (Success []) m0 = Success ll ->
  forall w, In w ll -> exists node v, map.get m0 node = Some v /\ g node v = Success w.
Proof.
  revert ll.
  apply (map.fold_spec
    (fun (m : M) (acc : result (list W)) =>
       forall ll, acc = Success ll -> forall w, In w ll ->
         exists node v, map.get m node = Some v /\ g node v = Success w)).
  - intros ll Hll w Hw. injection Hll as <-. destruct Hw.
  - intros k v m r Hgmk Hr ll Hll w Hw. cbn beta iota in Hll.
    destruct r as [rl|]; cbn beta iota in Hll; [|discriminate].
    destruct (g k v) as [w0|] eqn:Hg; cbn beta iota in Hll; [|discriminate].
    injection Hll as <-. destruct Hw as [<- | Hw].
    + exists k, v. split; [apply map.get_put_same | exact Hg].
    + destruct (Hr rl eq_refl w Hw) as [node [v' [Hget Hgnv]]].
      exists node, v'. split; [|exact Hgnv].
      rewrite (map.get_put_diff m node v k); [exact Hget|].
      intros Heq; subst node; rewrite Hget in Hgmk; discriminate.
Qed.

(* Every node_info produced by [compile_all_nodes] is the [compile_node] result for some node
   in the lowered layout. *)
Lemma compile_all_nodes_in (llayout : lowered_layout_map) (gc : global_context)
    (ninfos : list node_info) (ninfo : node_info) :
  compile_all_nodes llayout gc = Success ninfos ->
  In ninfo ninfos ->
  exists node lprog, map.get llayout node = Some lprog /\ compile_node node lprog gc = Success ninfo.
Proof.
  intros H Hin. unfold EncodeLayout.compile_all_nodes in H.
  match type of H with
  | context [map.fold ?F ?r0 llayout] => destruct (map.fold F r0 llayout) as [l|] eqn:Hfold
  end; cbn beta iota in H; [|discriminate].
  injection H as ->.
  apply (map_fold_result_in (fun node v => compile_node node v gc) llayout ninfos Hfold ninfo Hin).
Qed.

(* Generic: folding [g] over a map and accumulating [map.put]s yields, for each key in the
   result map, the source value it was renamed from. *)
Lemma map_fold_put_get {V W : Type} {MV : map.map node_id V} {MW : map.map node_id W}
    {MWok : map.ok MW} {MVok : map.ok MV}
    (g : node_id -> V -> result W) (node : node_id) (w : W) (m0 : MV) (mw : MW) :
  map.fold (fun acc nd v => acc' <- acc ;; w0 <- g nd v ;; Success (map.put acc' nd w0))
           (Success map.empty) m0 = Success mw ->
  map.get mw node = Some w ->
  exists v, map.get m0 node = Some v /\ g node v = Success w.
Proof.
  revert mw.
  apply (map.fold_spec
    (fun (m : MV) (acc : result MW) =>
       forall mw, acc = Success mw -> map.get mw node = Some w ->
         exists v, map.get m node = Some v /\ g node v = Success w)).
  - intros mw Hmw Hget. injection Hmw as <-. rewrite map.get_empty in Hget. discriminate.
  - intros k v m r Hgmk Hr mw Hmw Hget. cbn beta iota in Hmw.
    destruct r as [rmw|]; cbn beta iota in Hmw; [|discriminate].
    destruct (g k v) as [w0|] eqn:Hg; cbn beta iota in Hmw; [|discriminate].
    injection Hmw as <-.
    destruct (node_id_eqb_spec k node) as [->|Hne].
    + rewrite map.get_put_same in Hget. injection Hget as <-.
      exists v. split; [apply map.get_put_same | exact Hg].
    + rewrite (map.get_put_diff rmw node w0 k (not_eq_sym Hne)) in Hget.
      destruct (Hr rmw eq_refl Hget) as [v' [Hget' Hgv]].
      exists v'. split;
        [rewrite (map.get_put_diff m node v k (not_eq_sym Hne)); exact Hget' | exact Hgv].
Qed.

(* The lowered program assigned to a node is the global-rename of the original program there. *)
Lemma global_rename_rule_layout_spec (layout : layout_map) (gc : global_context)
    (llayout : lowered_layout_map) (node : node_id) (lprog : lowered_program) :
  global_rename_rule_layout layout gc = Success llayout ->
  map.get llayout node = Some lprog ->
  exists orig, map.get layout node = Some orig /\ global_rename_program orig gc = Success lprog.
Proof.
  intros H. unfold EncodeLayout.global_rename_rule_layout in H.
  apply (map_fold_put_get (fun nd p => global_rename_program p gc) node lprog layout llayout H).
Qed.

(* Generic: if folding [g] over a map (collecting Success results) succeeds, then [g] succeeded
   on every key/value of the map. *)
Lemma map_fold_result_success {V W : Type} {M : map.map node_id V} {Mok : map.ok M}
    (g : node_id -> V -> result W) (m0 : M) (ll : list W) :
  map.fold (fun acc nd v => acc' <- acc ;; w <- g nd v ;; Success (w :: acc')%list)
           (Success []) m0 = Success ll ->
  forall node v, map.get m0 node = Some v -> exists w, g node v = Success w.
Proof.
  revert ll.
  apply (map.fold_spec
    (fun (m : M) (acc : result (list W)) =>
       forall ll, acc = Success ll -> forall node v, map.get m node = Some v ->
         exists w, g node v = Success w)).
  - intros ll Hll node v Hget. rewrite map.get_empty in Hget. discriminate.
  - intros k v m r Hgmk Hr ll Hll node v0 Hget. cbn beta iota in Hll.
    destruct r as [rl|]; cbn beta iota in Hll; [|discriminate].
    destruct (g k v) as [w0|] eqn:Hg; cbn beta iota in Hll; [|discriminate].
    destruct (node_id_eqb_spec k node) as [->|Hne].
    + rewrite map.get_put_same in Hget. injection Hget as <-. exists w0. exact Hg.
    + rewrite (map.get_put_diff m node v k (not_eq_sym Hne)) in Hget.
      exact (Hr rl eq_refl node v0 Hget).
Qed.

(* Every node that the lowered layout assigns a program to compiles successfully. *)
Lemma compile_all_nodes_success (llayout : lowered_layout_map) (gc : global_context)
    (ninfos : list node_info) (node : node_id) (lprog : lowered_program) :
  compile_all_nodes llayout gc = Success ninfos ->
  map.get llayout node = Some lprog ->
  exists ninfo, compile_node node lprog gc = Success ninfo.
Proof.
  intros H Hget. unfold EncodeLayout.compile_all_nodes in H.
  match type of H with
  | context [map.fold ?F ?r0 llayout] => destruct (map.fold F r0 llayout) as [l|] eqn:Hfold
  end; cbn beta iota in H; [|discriminate].
  exact (map_fold_result_success (fun nd v => compile_node nd v gc) llayout l Hfold node lprog Hget).
Qed.

(* The empty program compiles to an empty node. *)
Lemma compile_node_nil (node : node_id) (gc : global_context) :
  compile_node node [] gc =
    Success {| nid := node; nprogram := []; nforwarding := map.empty; ntries := [] |}.
Proof. reflexivity. Qed.

(*============================================================================*)
(*  Distributed framework: a program distributed across nodes via a lowered     *)
(*  layout, compiled to a hardware network, computes exactly the original.       *)
(*============================================================================*)

(* The lowered program a layout assigns to a node (empty if the node is unassigned). *)
Definition lprog_of (llayout : lowered_layout_map) (n : node_id) : lowered_program :=
  match map.get llayout n with Some p => p | None => [] end.

(* The hardware network produced by compiling a layout: its datalog-level dataflow network
   [dnet] (graph / forwarding / input / output / per-node datalog program) is supplied by the
   caller; each node's trie table and hardware program come from [compile_node]. *)
Definition compiled_hn (llayout : lowered_layout_map) (gc : global_context) (dnet : DNet)
  : HwNetwork :=
  {| EncodeDistributed.hw_dnet := dnet;
     EncodeDistributed.hw_tries :=
       fun n => match compile_node n (lprog_of llayout n) gc with
                | Success ni => ni.(ntries) | Failure _ => @nil trie end;
     EncodeDistributed.hw_prog :=
       fun n => match compile_node n (lprog_of llayout n) gc with
                | Success ni => ni.(nprogram) | Failure _ => @nil hardware_rule end |}.

(* Every node's lowered program compiles successfully (assigned nodes by [compile_all_nodes],
   unassigned ones because the empty program trivially compiles). *)
Lemma compile_node_lprog_of (llayout : lowered_layout_map) (gc : global_context)
    (ninfos : list node_info) (n : node_id) :
  compile_all_nodes llayout gc = Success ninfos ->
  exists ninfo, compile_node n (lprog_of llayout n) gc = Success ninfo.
Proof.
  intros H. unfold lprog_of. destruct (map.get llayout n) as [p|] eqn:Hget.
  - exact (compile_all_nodes_success llayout gc ninfos n p H Hget).
  - eexists. apply compile_node_nil.
Qed.

(* Each node of the compiled network matches its datalog rules. *)
Lemma compiled_hn_node_rules_match (llayout : lowered_layout_map) (gc : global_context)
    (ninfos : list node_info) (dnet : DNet) :
  compile_all_nodes llayout gc = Success ninfos ->
  (forall n, Forall bare_rule (lprog_of llayout n)) ->
  dnet.(layout) = (fun n => (lprog_of llayout n)) ->
  EncodeDistributed.node_rules_match (compiled_hn llayout gc dnet).
Proof.
  intros Hcan Hbare Hlay n.
  destruct (compile_node_lprog_of llayout gc ninfos n Hcan) as [ninfo Hcn].
  unfold compiled_hn, EncodeDistributed.node_rules_match.
  cbn [EncodeDistributed.hw_tries EncodeDistributed.hw_prog EncodeDistributed.hw_dnet].
  rewrite Hlay, Hcn.
  apply (compile_node_matches n (lprog_of llayout n) gc ninfo (fun _ _ _ => False) (Hbare n) Hcn).
Qed.

(* DISTRIBUTED SOUNDNESS + COMPLETENESS: a program [program] distributed across nodes via the
   lowered layout [llayout] (so [dnet]'s datalog layout is the compiled per-node programs) and a
   well-formed *streaming* network ([good_network_streaming] over base facts [Q]) compiles to a
   hardware network that derives exactly the facts [program] derives from [Q].  [Q] is the EDB,
   injected at per-relation input nodes (see ConnectedTopology). *)
Theorem dist_compile_correct (llayout : lowered_layout_map) (gc : global_context)
    (ninfos : list node_info) (dnet : DNet)
    (program : list (Datalog.rule rel_id var nat aggregator))
    (Q : Datalog.fact rel_id T -> Prop) :
  compile_all_nodes llayout gc = Success ninfos ->
  (forall n, Forall bare_rule (lprog_of llayout n)) ->
  dnet.(layout) = (fun n => (lprog_of llayout n)) ->
  good_network_streaming dnet program Q ->
  forall f, EncodeDistributed.hw_net_prog_impl_fact (compiled_hn llayout gc dnet) f
            <-> DistributedDatalog.prog_impl_fact program Q f.
Proof.
  intros Hcan Hbare Hlay Hgood.
  apply (EncodeDistributed.hw_dist_correct (compiled_hn llayout gc dnet) program Q).
  - exact (compiled_hn_node_rules_match llayout gc ninfos dnet Hcan Hbare Hlay).
  - exact Hgood.
Qed.

(* A lowered layout [llayout] is *correctly distributed* by the dataflow network [dnet] over the
   program [program] with base facts [Q] when: every node's program is in the bare fragment,
   [dnet]'s datalog layout is exactly the compiled per-node program, and the streaming network is
   well-formed ([good_network_streaming]).  [good_network_streaming] is discharged generically by
   [ConnectedTopology.good_network_streaming_ct] (any connected topology + a checked layout). *)
Definition distributes (llayout : lowered_layout_map) (dnet : DNet)
    (program : list (Datalog.rule rel_id var nat aggregator)) (Q : Datalog.fact rel_id T -> Prop) : Prop :=
  (forall n, Forall bare_rule (lprog_of llayout n)) /\
  DistributedDatalog.layout dnet = (fun n => (lprog_of llayout n)) /\
  good_network_streaming dnet program Q.

(* CLEAN TOP-LEVEL: a program distributed across a compiled network computes exactly what the
   original program computes from the base facts [Q] -- soundness and completeness in one iff. *)
Theorem compile_implements_distributed (llayout : lowered_layout_map) (gc : global_context)
    (ninfos : list node_info) (dnet : DNet)
    (program : list (Datalog.rule rel_id var nat aggregator)) (Q : Datalog.fact rel_id T -> Prop) :
  compile_all_nodes llayout gc = Success ninfos ->
  distributes llayout dnet program Q ->
  forall f, EncodeDistributed.hw_net_prog_impl_fact (compiled_hn llayout gc dnet) f
            <-> DistributedDatalog.prog_impl_fact program Q f.
Proof.
  intros Hcan [Hbare [Hlay Hgood]].
  exact (dist_compile_correct llayout gc ninfos dnet program Q Hcan Hbare Hlay Hgood).
Qed.

(* The full [compile] pipeline invokes a successful [compile_all_nodes] over the renamed layout. *)
Lemma compile_compile_all_nodes (layout : layout_map)
    (fact_producers fact_consumers : fact_locations) (g : node_graph) (fuel : nat)
    (ninfos : list node_info) :
  compile layout fact_producers fact_consumers g fuel = Success ninfos ->
  exists llayout gc ninfos0,
    global_rename_rule_layout layout (collect_global_names_layout layout initial_global_context)
      = Success llayout /\
    compile_all_nodes llayout gc = Success ninfos0.
Proof.
  intros H. unfold EncodeLayout.compile in H. cbv zeta in H.
  match type of H with
  | context [global_rename_rule_layout ?a ?b] =>
      destruct (global_rename_rule_layout a b) as [llayout|] eqn:Hgr
  end; cbn beta iota in H; [|discriminate].
  match type of H with
  | context [EncodeLayout.global_rename_fact_locations fact_producers ?b] =>
      destruct (EncodeLayout.global_rename_fact_locations fact_producers b) as [lfp|] eqn:Hlfp
  end; cbn beta iota in H; [|discriminate].
  match type of H with
  | context [EncodeLayout.global_rename_fact_locations fact_consumers ?b] =>
      destruct (EncodeLayout.global_rename_fact_locations fact_consumers b) as [lfc|] eqn:Hlfc
  end; cbn beta iota in H; [|discriminate].
  match type of H with
  | context [compile_all_nodes llayout ?b] =>
      destruct (compile_all_nodes llayout b) as [ninfos0|] eqn:Hcan
  end; cbn beta iota in H; [|discriminate].
  exists llayout. eexists. exists ninfos0. split; [reflexivity | exact Hcan].
Qed.

(* TOP-LEVEL DISTRIBUTED CORRECTNESS: from a successful [compile], the resulting hardware network
   (its per-node tries/programs from compile, its dataflow topology/forwarding supplied as [dnet])
   derives exactly the facts the distributed program derives -- an iff (soundness + completeness).
   [llayout]/[gc] are the compiler's renamed layout and global context; the side conditions are
   bareness and [good_network] (graph / layout / forwarding-connectivity / input / output). *)
Theorem compile_dist_correct (layout : layout_map)
    (fact_producers fact_consumers : fact_locations) (g : node_graph) (fuel : nat)
    (ninfos : list node_info) (dnet : DNet)
    (program : list (Datalog.rule rel_id var nat aggregator))
    (Q : Datalog.fact rel_id T -> Prop) :
  compile layout fact_producers fact_consumers g fuel = Success ninfos ->
  exists llayout gc,
    (forall n, Forall bare_rule (lprog_of llayout n)) ->
    DistributedDatalog.layout dnet = (fun n => (lprog_of llayout n)) ->
    good_network_streaming dnet program Q ->
    forall f, EncodeDistributed.hw_net_prog_impl_fact (compiled_hn llayout gc dnet) f
              <-> DistributedDatalog.prog_impl_fact program Q f.
Proof.
  intros H.
  destruct (compile_compile_all_nodes layout fact_producers fact_consumers g fuel ninfos H)
    as [llayout [gc [ninfos0 [_ Hcan]]]].
  exists llayout, gc. intros Hbare Hlay Hgood.
  exact (dist_compile_correct llayout gc ninfos0 dnet program Q Hcan Hbare Hlay Hgood).
Qed.

(* TOP-LEVEL COMPILE CORRECTNESS: every node_info the compiler emits implements the lowered
   (global-renamed) version of the original rules assigned to that node in the input layout.
   [Forall bare_rule lprog] is the bare/SuperNice-fragment side condition. *)
Theorem compile_correct (layout : layout_map) (fact_producers fact_consumers : fact_locations)
    (g : node_graph) (fuel : nat) (ninfos : list node_info) (ninfo : node_info) :
  compile layout fact_producers fact_consumers g fuel = Success ninfos ->
  In ninfo ninfos ->
  exists node orig_prog lprog,
    map.get layout node = Some orig_prog /\
    global_rename_program orig_prog (collect_global_names_layout layout initial_global_context)
      = Success lprog /\
    (Forall bare_rule lprog ->
     node_implements ninfo.(ntries) ninfo.(nprogram) (lprog)).
Proof.
  intros H Hin. unfold EncodeLayout.compile in H. cbv zeta in H.
  match type of H with
  | context [global_rename_rule_layout ?a ?b] =>
      destruct (global_rename_rule_layout a b) as [llayout|] eqn:Hgr
  end; cbn beta iota in H; [|discriminate].
  match type of H with
  | context [EncodeLayout.global_rename_fact_locations fact_producers ?b] =>
      destruct (EncodeLayout.global_rename_fact_locations fact_producers b) as [lfp|] eqn:Hlfp
  end; cbn beta iota in H; [|discriminate].
  match type of H with
  | context [EncodeLayout.global_rename_fact_locations fact_consumers ?b] =>
      destruct (EncodeLayout.global_rename_fact_locations fact_consumers b) as [lfc|] eqn:Hlfc
  end; cbn beta iota in H; [|discriminate].
  match type of H with
  | context [compile_all_nodes llayout ?b] =>
      destruct (compile_all_nodes llayout b) as [ninfos0|] eqn:Hcan
  end; cbn beta iota in H; [|discriminate].
  injection H as <-.
  destruct (attach_forwarding_tables_spec ninfos0 _ ninfo Hin)
    as [ninfo0 [Hin0 [_ [Ht Hp]]]].
  destruct (compile_all_nodes_in llayout _ ninfos0 ninfo0 Hcan Hin0)
    as [node [lprog [Hgetll Hcn]]].
  destruct (global_rename_rule_layout_spec layout _ llayout node lprog Hgr Hgetll)
    as [orig [Hgetlay Hgrp]].
  exists node, orig, lprog. split; [exact Hgetlay | split; [exact Hgrp |]].
  intros Hbare. rewrite Ht, Hp.
  apply (compile_node_correct node lprog _ ninfo0 Hbare Hcn).
Qed.

(*===========================================================================*)
(*  A CHECKER FOR THE [distributes] SIDE CONDITIONS                          *)
(*                                                                           *)
(*  [distributes llayout dnet program] bundles three obligations:           *)
(*    1. every node's lowered program is in the bare fragment;              *)
(*    2. [dnet]'s datalog layout is exactly the compiled per-node program;  *)
(*    3. [dnet] is a well-formed dataflow network ([good_network]).         *)
(*  We discharge (1) with a decidable boolean checker, (2) by *constructing* *)
(*  [dnet] so the equation holds definitionally, and leave (3) -- which is   *)
(*  not generically decidable (it needs finite node enumeration + topology   *)
(*  connectivity) -- as the topology side condition a per-topology checker   *)
(*  (e.g. [GridLayout.check_layout]) discharges.                             *)
(*===========================================================================*)

Notation lowered_fact := (@HardwareProgram.lowered_fact var).
Notation lowered_rule := (@HardwareProgram.lowered_rule var aggregator).

(* Boolean version of [bare_fact]: every argument is a plain variable. *)
Definition bare_factb (lf : lowered_fact) : bool :=
  forallb (fun e => match e with var_expr _ => true | fun_expr _ _ => false end) lf.(Datalog.clause_args).

Definition bare_ruleb (lr : lowered_rule) : bool :=
  match lr with
  | Datalog.normal_rule concls hyps => forallb bare_factb hyps && forallb bare_factb concls
  | _ => false
  end.

Lemma bare_factb_spec (lf : lowered_fact) : bare_factb lf = true -> bare_fact lf.
Proof.
  unfold bare_factb, bare_fact. intros H. rewrite forallb_forall in H.
  apply Forall_forall. intros e He. specialize (H e He).
  destruct e as [v|f args]; [exists v; reflexivity | discriminate].
Qed.

Lemma bare_ruleb_spec (lr : lowered_rule) : bare_ruleb lr = true -> bare_rule lr.
Proof.
  destruct lr as [concls hyps | mc mh | cr ag hr0]; cbn;
    [| intros HH; discriminate | intros HH; discriminate].
  intros H. apply andb_true_iff in H. destruct H as [H1 H2].
  rewrite forallb_forall in H1, H2. split.
  - apply Forall_forall. intros lf Hlf. apply bare_factb_spec. apply H1. exact Hlf.
  - apply Forall_forall. intros lf Hlf. apply bare_factb_spec. apply H2. exact Hlf.
Qed.

(* Decidable check that every program in the lowered layout is bare. *)
Definition bare_layoutb (llayout : lowered_layout_map) : bool :=
  map.fold (fun acc _ p => acc && forallb bare_ruleb p) true llayout.

Lemma bare_layoutb_entry (llayout : lowered_layout_map) :
  bare_layoutb llayout = true ->
  forall n p, map.get llayout n = Some p -> forallb bare_ruleb p = true.
Proof.
  unfold bare_layoutb.
  apply (map.fold_spec
    (fun (m : lowered_layout_map) (b : bool) =>
       b = true -> forall n p, map.get m n = Some p -> forallb bare_ruleb p = true)).
  - intros _ n p Hget. rewrite map.get_empty in Hget. discriminate.
  - intros k v m r Hgmk IH Hb n p Hget.
    apply andb_true_iff in Hb. destruct Hb as [Hr Hv].
    destruct (node_id_eqb_spec n k) as [->|Hne].
    + rewrite map.get_put_same in Hget. injection Hget as <-. exact Hv.
    + rewrite map.get_put_diff in Hget by congruence.
      apply (IH Hr n p Hget).
Qed.

(* [bare_layoutb] soundly discharges conjunct (1) of [distributes]. *)
Lemma bare_layoutb_spec (llayout : lowered_layout_map) :
  bare_layoutb llayout = true ->
  forall n, Forall bare_rule (lprog_of llayout n).
Proof.
  intros H n. unfold lprog_of. destruct (map.get llayout n) as [p|] eqn:Hget.
  - apply Forall_forall. intros lr Hlr.
    pose proof (bare_layoutb_entry llayout H n p Hget) as Hp.
    rewrite forallb_forall in Hp. apply bare_ruleb_spec. apply Hp. exact Hlr.
  - constructor.
Qed.

(* Build the dataflow network for a lowered layout: take the topology / forwarding / input /
   output from a [base] network and *force* the datalog layout to be the compiled per-node
   program.  This makes conjunct (2) of [distributes] hold by construction. *)
Definition dnet_of_llayout (llayout : lowered_layout_map) (base : DNet) : DNet :=
  {| DistributedDatalog.graph   := base.(DistributedDatalog.graph);
     DistributedDatalog.forward := base.(DistributedDatalog.forward);
     DistributedDatalog.input   := base.(DistributedDatalog.input);
     DistributedDatalog.output  := base.(DistributedDatalog.output);
     DistributedDatalog.layout  := fun n => (lprog_of llayout n) |}.

(* CLEAN TOP-LEVEL (per-node compilation): given a successful [compile_all_nodes], a passing
   bareness check, and a well-formed network [good_network] over the layout-forced [dnet], the
   compiled hardware network derives exactly the facts the original program derives.  Conjunct
   (2) of [distributes] is discharged by construction; conjunct (1) by [bare_layoutb]. *)
Theorem compile_all_distributes_correct (llayout : lowered_layout_map) (gc : global_context)
    (ninfos : list node_info) (base : DNet)
    (program : list (Datalog.rule rel_id var nat aggregator))
    (Q : Datalog.fact rel_id T -> Prop) :
  compile_all_nodes llayout gc = Success ninfos ->
  bare_layoutb llayout = true ->
  good_network_streaming (dnet_of_llayout llayout base) program Q ->
  forall f, EncodeDistributed.hw_net_prog_impl_fact
              (compiled_hn llayout gc (dnet_of_llayout llayout base)) f
            <-> DistributedDatalog.prog_impl_fact program Q f.
Proof.
  intros Hcan Hbare Hgood.
  apply (compile_implements_distributed llayout gc ninfos
           (dnet_of_llayout llayout base) program Q Hcan).
  unfold distributes. split; [|split].
  - apply bare_layoutb_spec. exact Hbare.
  - reflexivity.
  - exact Hgood.
Qed.

(* CLEAN TOP-LEVEL (full [compile] pipeline): same statement, starting from the raw [compile]
   entry point.  [llayout]/[gc] -- the compiler's internal renamed layout and global context --
   are existentially exposed (they are produced inside [compile]); the side conditions are the
   passing bareness check and [good_network] of the layout-forced network. *)
Theorem compile_distributes_correct (layout : layout_map)
    (fact_producers fact_consumers : fact_locations) (g : node_graph) (fuel : nat)
    (ninfos : list node_info) (base : DNet)
    (program : list (Datalog.rule rel_id var nat aggregator))
    (Q : Datalog.fact rel_id T -> Prop) :
  compile layout fact_producers fact_consumers g fuel = Success ninfos ->
  exists llayout gc,
    bare_layoutb llayout = true ->
    good_network_streaming (dnet_of_llayout llayout base) program Q ->
    forall f, EncodeDistributed.hw_net_prog_impl_fact
                (compiled_hn llayout gc (dnet_of_llayout llayout base)) f
              <-> DistributedDatalog.prog_impl_fact program Q f.
Proof.
  intros H.
  destruct (compile_compile_all_nodes layout fact_producers fact_consumers g fuel ninfos H)
    as [llayout [gc [ninfos0 [_ Hcan]]]].
  exists llayout, gc. intros Hbare Hgood.
  exact (compile_all_distributes_correct llayout gc ninfos0 base program Q Hcan Hbare Hgood).
Qed.

(* The datalog layout a lowered layout induces on the network: each node runs its lowered rules
   viewed as plain datalog rules over numeric ids.  This is exactly the [layout] field that
   [dnet_of_llayout] forces, so it is what any topology's network must carry. *)
Definition forced_layout (llayout : lowered_layout_map)
    : node_id -> list (Datalog.rule rel_id var nat aggregator) :=
  fun n => (lprog_of llayout n).

(*===========================================================================*)
(*  TOP-LEVEL, TOPOLOGY-GENERIC COMPILE CORRECTNESS                          *)
(*                                                                           *)
(*  Run the compiled per-node programs on ANY [connected_topology] (over the *)
(*  compiler's node type): if the bareness check passes and the forced       *)
(*  layout passes the topology's layout checker (only real nodes, rules <->  *)
(*  program), then the distributed hardware network derives exactly the      *)
(*  facts the original program derives.  [good_network] is discharged       *)
(*  entirely by [good_network_ct] from the topology interface -- no graph    *)
(*  specifics.  A grid is just one [connected_topology] instance; so is any   *)
(*  other topology.                                                          *)
(*===========================================================================*)
Theorem compile_topology_correct
    (rule_eqb : Datalog.rule rel_id var nat aggregator ->
                Datalog.rule rel_id var nat aggregator -> bool)
    (rule_eqb_spec : forall r1 r2, BoolSpec (r1 = r2) (r1 <> r2) (rule_eqb r1 r2))
    (ct : @ConnectedTopology.connected_topology rel_id T node_id)
    (llayout : lowered_layout_map) (gc : global_context) (ninfos : list node_info)
    (program : list (Datalog.rule rel_id var nat aggregator))
    (Q : Datalog.fact rel_id T -> Prop) :
  compile_all_nodes llayout gc = Success ninfos ->
  bare_layoutb llayout = true ->
  ConnectedTopology.layout_valid_nodes ct (forced_layout llayout) ->
  ConnectedTopology.check_layout (rule_eqb := rule_eqb) ct (forced_layout llayout) program = true ->
  forall f, EncodeDistributed.hw_net_prog_impl_fact
              (compiled_hn llayout gc (ConnectedTopology.net_of_streaming ct (forced_layout llayout) Q)) f
            <-> DistributedDatalog.prog_impl_fact program Q f.
Proof.
  intros Hcan Hbare Hvalid Hcheck.
  assert (Hgood : good_network_streaming
            (dnet_of_llayout llayout (ConnectedTopology.net_of_streaming ct (fun _ => @nil _) Q)) program Q).
  { change (good_network_streaming (ConnectedTopology.net_of_streaming ct (forced_layout llayout) Q) program Q).
    exact (ConnectedTopology.good_network_streaming_ct (rule_eqb := rule_eqb) (rule_eqb_spec := rule_eqb_spec)
             ct (forced_layout llayout) program Q Hvalid Hcheck). }
  intros f.
  change (EncodeDistributed.hw_net_prog_impl_fact
            (compiled_hn llayout gc
               (dnet_of_llayout llayout (ConnectedTopology.net_of_streaming ct (fun _ => @nil _) Q))) f
          <-> DistributedDatalog.prog_impl_fact program Q f).
  exact (compile_all_distributes_correct llayout gc ninfos
           (ConnectedTopology.net_of_streaming ct (fun _ => @nil _) Q) program Q Hcan Hbare Hgood f).
Qed.

(* COMPUTABLE layout-validity check: every node the lowered layout actually assigns to (i.e. every
   key of [llayout]) is a real node of the topology.  This [bool] is what makes
   [layout_valid_nodes] dischargeable by [vm_compute] on concrete examples. *)
Definition layout_keys_validb (ct : @ConnectedTopology.connected_topology rel_id T node_id)
    (llayout : lowered_layout_map) : bool :=
  forallb (fun n => existsb (node_id_eqb n) (ConnectedTopology.ct_all_nodes ct)) (map.keys llayout).

Lemma layout_keys_validb_spec
    (ct : @ConnectedTopology.connected_topology rel_id T node_id) (llayout : lowered_layout_map) :
  layout_keys_validb ct llayout = true ->
  ConnectedTopology.layout_valid_nodes ct (forced_layout llayout).
Proof.
  intros H n r Hin.
  assert (Hget : exists p, map.get llayout n = Some p).
  { unfold forced_layout, lprog_of in Hin. destruct (map.get llayout n) as [p|] eqn:Hg.
    - exists p. reflexivity.
    - simpl in Hin. destruct Hin. }
  destruct Hget as [p Hg].
  pose proof (map.in_keys llayout n p Hg) as Hink.
  unfold layout_keys_validb in H. rewrite forallb_forall in H. specialize (H n Hink).
  rewrite existsb_exists in H. destruct H as [n' [Hn' Heq]].
  pose proof (node_id_eqb_spec n n') as Hs. rewrite Heq in Hs. inversion Hs. subst.
  exact (proj1 (ConnectedTopology.ct_all_nodes_spec ct _) Hn').
Qed.

(* TOP-LEVEL, EXAMPLE-FRIENDLY: run the compiled per-node programs on any [connected_topology] over
   the compiler's node type.  All side conditions are now COMPUTABLE (no [rule_eqb], no supplied
   reference program): bareness ([bare_layoutb]) and node-validity ([layout_keys_validb]) are bools
   discharged by [vm_compute]; the reference program is the canonical union of the per-node rules.
   The conclusion: the distributed hardware network derives exactly the facts that union derives. *)
Theorem compile_topology_canonical_correct
    (ct : @ConnectedTopology.connected_topology rel_id T node_id)
    (llayout : lowered_layout_map) (gc : global_context) (ninfos : list node_info)
    (Q : Datalog.fact rel_id T -> Prop) :
  compile_all_nodes llayout gc = Success ninfos ->
  bare_layoutb llayout = true ->
  layout_keys_validb ct llayout = true ->
  forall f, EncodeDistributed.hw_net_prog_impl_fact
              (compiled_hn llayout gc (ConnectedTopology.net_of_streaming ct (forced_layout llayout) Q)) f
            <-> DistributedDatalog.prog_impl_fact
                  (ConnectedTopology.canonical_program ct (forced_layout llayout)) Q f.
Proof.
  intros Hcan Hbare Hkeys.
  pose proof (layout_keys_validb_spec ct llayout Hkeys) as Hvalid.
  assert (Hgood : good_network_streaming
            (dnet_of_llayout llayout (ConnectedTopology.net_of_streaming ct (fun _ => @nil _) Q))
            (ConnectedTopology.canonical_program ct (forced_layout llayout)) Q).
  { change (good_network_streaming (ConnectedTopology.net_of_streaming ct (forced_layout llayout) Q)
              (ConnectedTopology.canonical_program ct (forced_layout llayout)) Q).
    apply ConnectedTopology.good_network_streaming_canonical. exact Hvalid. }
  intros f.
  change (EncodeDistributed.hw_net_prog_impl_fact
            (compiled_hn llayout gc
               (dnet_of_llayout llayout (ConnectedTopology.net_of_streaming ct (fun _ => @nil _) Q))) f
          <-> DistributedDatalog.prog_impl_fact
                (ConnectedTopology.canonical_program ct (forced_layout llayout)) Q f).
  exact (compile_all_distributes_correct llayout gc ninfos
           (ConnectedTopology.net_of_streaming ct (fun _ => @nil _) Q)
           (ConnectedTopology.canonical_program ct (forced_layout llayout)) Q Hcan Hbare Hgood f).
Qed.

(* NON-DISTRIBUTED <-> DISTRIBUTED.  This is the statement you usually want: take a plain,
   non-distributed program [P]; if a layout *distributes* [P] -- i.e. the rules spread across the
   nodes are exactly [P]'s rules (same set: [forall r, In r P <-> In r (the union)]) -- and the
   computable side conditions hold, then [P] (run non-distributed) and the compiled distributed
   hardware network derive EXACTLY the same facts.  The set-equality hypothesis is the precise
   meaning of "the layout is a distributed version of P"; it is discharged via the canonical-union
   theorem plus [prog_impl_fact_subset] (derivability depends only on the rule SET, so order /
   duplicates / which node holds a rule are all irrelevant). *)
Theorem compile_distributes_program
    (ct : @ConnectedTopology.connected_topology rel_id T node_id)
    (llayout : lowered_layout_map) (gc : global_context) (ninfos : list node_info)
    (P : list (Datalog.rule rel_id var nat aggregator)) (Q : Datalog.fact rel_id T -> Prop) :
  compile_all_nodes llayout gc = Success ninfos ->
  bare_layoutb llayout = true ->
  layout_keys_validb ct llayout = true ->
  (forall r, In r P <-> In r (ConnectedTopology.canonical_program ct (forced_layout llayout))) ->
  forall f, DistributedDatalog.prog_impl_fact P Q f
            <-> EncodeDistributed.hw_net_prog_impl_fact
                  (compiled_hn llayout gc (ConnectedTopology.net_of_streaming ct (forced_layout llayout) Q)) f.
Proof.
  intros Hcan Hbare Hkeys Hdist f.
  rewrite (compile_topology_canonical_correct ct llayout gc ninfos Q Hcan Hbare Hkeys f).
  split; intros Hp.
  - apply (DistributedDatalog.prog_impl_fact_subset P _ Q f).
    + intros x Hx. apply (proj1 (Hdist x)). exact Hx.
    + exact Hp.
  - apply (DistributedDatalog.prog_impl_fact_subset
             (ConnectedTopology.canonical_program ct (forced_layout llayout)) P Q f).
    + intros x Hx. apply (proj2 (Hdist x)). exact Hx.
    + exact Hp.
Qed.

(*===========================================================================*)
(*  ONE CHECKER, ONE CLEAN TOP-LEVEL THEOREM                                 *)
(*                                                                           *)
(*  The three obligations as named, computable predicates over the SOURCE    *)
(*  inputs, bundled into a single [compile_checker].  When it returns [true], *)
(*  the compiled distributed hardware network and the (canonical) program    *)
(*  derive exactly the same facts.  This is the statement to actually use --  *)
(*  hand it a layout, run the checker, get correctness.                      *)
(*===========================================================================*)

(* The full pipeline produced a hardware program. *)
Definition compile_succ (layout : layout_map) (fp fc : fact_locations)
    (g : node_graph) (fuel : nat) : bool :=
  match compile layout fp fc g fuel with Success _ => true | Failure _ => false end.

(* Every rule (after renaming) is in the bare fragment. *)
Definition only_bare_rules (layout : layout_map) : bool :=
  bare_layoutb (compile_renamed_layout layout).

(* The layout only places rules on real nodes of the topology. *)
Definition valid_node_layout (ct : @ConnectedTopology.connected_topology rel_id T node_id)
    (layout : layout_map) : bool :=
  layout_keys_validb ct (compile_renamed_layout layout).

(* All three at once. *)
Definition compile_checker (ct : @ConnectedTopology.connected_topology rel_id T node_id)
    (layout : layout_map) (fp fc : fact_locations) (g : node_graph) (fuel : nat) : bool :=
  compile_succ layout fp fc g fuel && only_bare_rules layout && valid_node_layout ct layout.

(* A successful [compile] runs a successful [compile_all_nodes] on the exposed renamed
   layout / global context. *)
Lemma compile_renamed_all_nodes (layout : layout_map) (fp fc : fact_locations)
    (g : node_graph) (fuel : nat) (ninfos : list node_info) :
  compile layout fp fc g fuel = Success ninfos ->
  exists ninfos0,
    compile_all_nodes (compile_renamed_layout layout) (compile_global_context layout fp fc)
      = Success ninfos0.
Proof.
  intros H. unfold EncodeLayout.compile in H. cbv zeta in H.
  unfold compile_renamed_layout, compile_global_context,
    EncodeLayout.compile_renamed_layout, EncodeLayout.compile_global_context.
  destruct (global_rename_rule_layout layout
              (collect_global_names_layout layout initial_global_context)) as [ll|] eqn:Hgr;
    cbn beta iota in H |- *; [|discriminate].
  destruct (EncodeLayout.global_rename_fact_locations fp
              (collect_global_names_layout layout initial_global_context)) as [lfp|] eqn:Hfp;
    cbn beta iota in H |- *; [|discriminate].
  destruct (EncodeLayout.global_rename_fact_locations fc
              (collect_global_names_layout layout initial_global_context)) as [lfc|] eqn:Hfc;
    cbn beta iota in H |- *; [|discriminate].
  destruct (compile_all_nodes ll
              (collect_global_dependencies ll lfp lfc
                 (collect_global_names_layout layout initial_global_context))) as [ninfos0|] eqn:Hcan;
    cbn beta iota in H; [|discriminate].
  exists ninfos0. reflexivity.
Qed.

(* THE CLEAN TOP-LEVEL THEOREM: pass the checker, get soundness + completeness.  For any base/EDB
   facts [Q] (streamed in at the topology's per-relation input nodes), the compiled distributed
   hardware network derives EXACTLY the facts the canonical program (the union of the per-node
   rules) derives from [Q].  All side conditions are the single boolean [compile_checker]. *)
Theorem compile_checked_correct (ct : @ConnectedTopology.connected_topology rel_id T node_id)
    (layout : layout_map) (fp fc : fact_locations) (g : node_graph) (fuel : nat)
    (Q : Datalog.fact rel_id T -> Prop) :
  compile_checker ct layout fp fc g fuel = true ->
  forall f, EncodeDistributed.hw_net_prog_impl_fact
              (compiled_hn (compile_renamed_layout layout) (compile_global_context layout fp fc)
                 (ConnectedTopology.net_of_streaming ct (forced_layout (compile_renamed_layout layout)) Q)) f
            <-> DistributedDatalog.prog_impl_fact
                  (ConnectedTopology.canonical_program ct
                     (forced_layout (compile_renamed_layout layout))) Q f.
Proof.
  intros Hchk.
  unfold compile_checker in Hchk. apply andb_true_iff in Hchk. destruct Hchk as [Hchk Hvalid].
  apply andb_true_iff in Hchk. destruct Hchk as [Hcomp Hbare].
  unfold compile_succ in Hcomp.
  destruct (compile layout fp fc g fuel) as [ninfos|] eqn:Hc; [|discriminate].
  destruct (compile_renamed_all_nodes layout fp fc g fuel ninfos Hc) as [ninfos0 Hcan].
  unfold only_bare_rules in Hbare. unfold valid_node_layout in Hvalid.
  exact (compile_topology_canonical_correct ct (compile_renamed_layout layout)
           (compile_global_context layout fp fc) ninfos0 Q Hcan Hbare Hvalid).
Qed.

(*============================================================================*)
(*  Phase C (soundness): the compiler's OWN generated forwarding table only     *)
(*  ever routes a relation's facts along real edges of the topology [g].        *)
(*  ([map.ok]s the surrounding section does not already carry are taken here,    *)
(*   after [compile_checked_correct], so that theorem keeps its exact form.)     *)
(*============================================================================*)

Context {forwarding_table_ok : map.ok forwarding_table}.
Context {node_ftable_map_ok : map.ok node_ftable_map}.
Context {node_id_set_ok : map.ok node_id_set}.
Context {node_id_edge_set_ok : map.ok node_id_edge_set}.

Notation ftable_edges_sound :=
  (@ForwardingCorrect.ftable_edges_sound node_id node_id_set node_id_edge_set forwarding_table node_ftable_map).
Notation generate_forwarding_table :=
  (@EncodeLayout.generate_forwarding_table rel fn Node node_id node_id_eqb node_id_set forwarding_table
     rel_dependency_map fn_id_map rel_relid_map node_id_edge_set node_ftable_map).
Notation update_forwarding_table_for_rel :=
  (@EncodeLayout.update_forwarding_table_for_rel rel fn Node node_id node_id_eqb node_id_set forwarding_table
     rel_dependency_map fn_id_map rel_relid_map node_id_edge_set node_ftable_map).

(* one relation's worth of routing keeps the table edge-sound: every producer/consumer pair is
   joined either by trie destinations (no edges) or along a [get_path], which [get_path_spec]
   certifies is a genuine edge-walk. *)
Lemma update_rel_pres_sound (g : node_graph) (rel0 : rel_id) (gcontext : global_context)
    (ninfos : list node_info) (ftables : node_ftable_map) (fuel : nat) :
  ftable_edges_sound g ftables ->
  ftable_edges_sound g (update_forwarding_table_for_rel rel0 gcontext ninfos ftables fuel g).
Proof.
  intros Hsound. unfold EncodeLayout.update_forwarding_table_for_rel.
  apply (ForwardingCorrect.map_fold_pres_sound (M := node_id_set) (Mok := node_id_set_ok) g).
  - exact Hsound.
  - intros ft producer _ Hft.
    apply (ForwardingCorrect.map_fold_pres_sound (M := node_id_set) (Mok := node_id_set_ok) g).
    + exact Hft.
    + intros ft' consumer _ Hft'.
      destruct (node_id_eqb producer consumer).
      * apply ForwardingCorrect.add_trie_pres_sound. exact Hft'.
      * destruct (ComputableGraph.get_path (node_eqb := node_id_eqb) (node_set := node_id_set)
                    (edge_set := node_id_edge_set) g producer consumer fuel) as [path|] eqn:Hpath.
        -- eapply ForwardingCorrect.add_path_pres_sound; [| exact Hft'].
           eapply ComputableGraph.get_path_spec. exact Hpath.
        -- exact Hft'.
Qed.

(* the whole table, folded over all relation ids from the empty table, is edge-sound. *)
Lemma generate_forwarding_table_sound (g : node_graph) (gcontext : global_context)
    (ninfos : list node_info) (fuel : nat) :
  ftable_edges_sound g (generate_forwarding_table gcontext ninfos g fuel).
Proof.
  unfold EncodeLayout.generate_forwarding_table.
  apply ForwardingCorrect.fold_left_pres_sound.
  - apply ForwardingCorrect.ftable_edges_sound_empty.
  - intros acc rel0 Hacc. apply update_rel_pres_sound. exact Hacc.
Qed.

(*============================================================================*)
(*  Phase C2 (completeness engine): every consecutive edge of a path that the   *)
(*  compiler actually laid down (i.e. [get_path] returned [Some]) survives into  *)
(*  the final [generate_forwarding_table].  Built from the monotonicity         *)
(*  ([add_*_mono]) and the per-path [add_path_adds] of Phase B, threaded through *)
(*  the producer/consumer/relation folds by the [*_adds]/[*_pres] combinators.   *)
(*============================================================================*)

Notation has_fwd_edge := (@ForwardingCorrect.has_fwd_edge node_id forwarding_table node_ftable_map).
Notation get_path := (@ComputableGraph.get_path node_id node_id_eqb node_id_set node_id_edge_set).
Notation get_rel_ids :=
  (@EncodeLayout.get_rel_ids rel fn Node node_id node_id_set rel_dependency_map fn_id_map rel_relid_map).
Notation add_trie_dest :=
  (@EncodeLayout.add_trie_dest_to_forwarding_table node_id node_id_eqb forwarding_table node_ftable_map).
Notation add_path :=
  (@EncodeLayout.add_path_to_forwarding_table node_id node_id_eqb forwarding_table node_ftable_map).

(* the per-(producer,consumer) cell only adds forwarding edges (any edge relation [r] survives) *)
Lemma fwd_cell_mono (g : node_graph) (rel0 : rel_id) (ninfos : list node_info) (fuel : nat)
    (producer consumer : node_id) (a b : node_id) (r : rel_id) (ft : node_ftable_map) :
  has_fwd_edge ft a r b ->
  has_fwd_edge
    (if node_id_eqb producer consumer
     then add_trie_dest consumer rel0 ft ninfos
     else match get_path g producer consumer fuel with
          | None => ft
          | Some path => add_path rel0 path ft ninfos
          end) a r b.
Proof.
  intros H. destruct (node_id_eqb producer consumer).
  - apply ForwardingCorrect.add_trie_mono. exact H.
  - destruct (get_path g producer consumer fuel) as [path|].
    + apply ForwardingCorrect.add_path_mono. exact H.
    + exact H.
Qed.

(* routing one relation only adds forwarding edges *)
Lemma update_rel_mono (g : node_graph) (rel0 : rel_id) (gcontext : global_context)
    (ninfos : list node_info) (fuel : nat) (a b : node_id) (r : rel_id) (ft : node_ftable_map) :
  has_fwd_edge ft a r b ->
  has_fwd_edge (update_forwarding_table_for_rel rel0 gcontext ninfos ft fuel g) a r b.
Proof.
  intros H. unfold EncodeLayout.update_forwarding_table_for_rel.
  apply (ForwardingCorrect.map_fold_pres (M := node_id_set) (Mok := node_id_set_ok)
           (fun ft => has_fwd_edge ft a r b)); [exact H|].
  intros ft1 producer _ H1.
  apply (ForwardingCorrect.map_fold_pres (M := node_id_set) (Mok := node_id_set_ok)
           (fun ft => has_fwd_edge ft a r b)); [exact H1|].
  intros ft2 consumer _ H2. apply fwd_cell_mono. exact H2.
Qed.

(* routing relation [rel0] lays every consecutive edge of the path it found from [prod] to [cons] *)
Lemma update_rel_adds (g : node_graph) (rel0 : rel_id) (gcontext : global_context)
    (ninfos : list node_info) (fuel : nat) (prod cons : node_id) (path : list node_id)
    (producers consumers : node_id_set) (i : nat) (a b : node_id) (ft : node_ftable_map) :
  map.get gcontext.(EncodeLayout.rel_node_producers) rel0 = Some producers ->
  map.get gcontext.(EncodeLayout.rel_node_consumers) rel0 = Some consumers ->
  map.get producers prod = Some tt ->
  map.get consumers cons = Some tt ->
  prod <> cons ->
  get_path g prod cons fuel = Some path ->
  nth_error path i = Some a -> nth_error path (S i) = Some b ->
  has_fwd_edge (update_forwarding_table_for_rel rel0 gcontext ninfos ft fuel g) a rel0 b.
Proof.
  intros Hprods Hcons Hprod Hcon Hne Hpath Hi Hib.
  unfold EncodeLayout.update_forwarding_table_for_rel. rewrite Hprods, Hcons.
  apply (ForwardingCorrect.nid_fold_adds (Mok := node_id_set_ok)
           (fun ft => has_fwd_edge ft a rel0 b) _ ft producers prod tt Hprod).
  - intros ft1 p _ H1.
    apply (ForwardingCorrect.map_fold_pres (M := node_id_set) (Mok := node_id_set_ok)
             (fun ft => has_fwd_edge ft a rel0 b)); [exact H1|].
    intros ft2 c _ H2. apply fwd_cell_mono. exact H2.
  - intros ft1.
    apply (ForwardingCorrect.nid_fold_adds (Mok := node_id_set_ok)
             (fun ft => has_fwd_edge ft a rel0 b) _ ft1 consumers cons tt Hcon).
    + intros ft2 c _ H2. apply fwd_cell_mono. exact H2.
    + intros ft2.
      destruct (node_id_eqb_spec prod cons) as [Heq|_]; [exfalso; apply Hne; exact Heq|].
      rewrite Hpath. eapply ForwardingCorrect.add_path_adds; [exact Hi | exact Hib].
Qed.

(* MAIN C2 ENGINE: the consecutive forwarding edge survives into the whole generated table. *)
Lemma generate_forwarding_table_adds (g : node_graph) (gcontext : global_context)
    (ninfos : list node_info) (fuel : nat) (rel0 : rel_id) (prod cons : node_id)
    (path : list node_id) (producers consumers : node_id_set) (i : nat) (a b : node_id) :
  In rel0 (get_rel_ids gcontext) ->
  map.get gcontext.(EncodeLayout.rel_node_producers) rel0 = Some producers ->
  map.get gcontext.(EncodeLayout.rel_node_consumers) rel0 = Some consumers ->
  map.get producers prod = Some tt ->
  map.get consumers cons = Some tt ->
  prod <> cons ->
  get_path g prod cons fuel = Some path ->
  nth_error path i = Some a -> nth_error path (S i) = Some b ->
  has_fwd_edge (generate_forwarding_table gcontext ninfos g fuel) a rel0 b.
Proof.
  intros Hrel Hprods Hcons Hprod Hcon Hne Hpath Hi Hib.
  unfold EncodeLayout.generate_forwarding_table.
  apply (ForwardingCorrect.fold_left_adds (fun ft => has_fwd_edge ft a rel0 b)
           (fun ftables rel => update_forwarding_table_for_rel rel gcontext ninfos ftables fuel g)
           (get_rel_ids gcontext) map.empty rel0 Hrel).
  - intros acc r H1. apply update_rel_mono. exact H1.
  - intros acc. eapply update_rel_adds; eauto.
Qed.

(* the forwarding function a compiled node exposes for a relation: the [DestEdge] targets
   recorded in its forwarding table.  [In n2 (fwd_list ft n r)] is exactly [has_fwd_edge]. *)
Definition fwd_list (ftables : node_ftable_map) (n : node_id) (r : rel_id) : list node_id :=
  @ForwardingCorrect.dest_edges node_id
    (@ForwardingCorrect.node_rel_dests node_id forwarding_table node_ftable_map ftables n r).

(* PACKAGED C2 RESULT: whenever the compiler found (and laid) a path from a producer of [rel0]
   to a consumer of [rel0] (i.e. [get_path] returned [Some] — a computable, checkable fact), the
   final generated forwarding table makes that consumer forwarding-reachable from the producer.
   Composes [get_path_spec] (the path is real) + [generate_forwarding_table_adds] (its edges
   survive) + [forwarding_chain_reachable] (a forwarding walk is a reachability chain). *)
Lemma generate_forwarding_reachable (g : node_graph) (gcontext : global_context)
    (ninfos : list node_info) (fuel : nat) (rel0 : rel_id) (prod cons : node_id)
    (path : list node_id) (producers consumers : node_id_set) :
  In rel0 (get_rel_ids gcontext) ->
  map.get gcontext.(EncodeLayout.rel_node_producers) rel0 = Some producers ->
  map.get gcontext.(EncodeLayout.rel_node_consumers) rel0 = Some consumers ->
  map.get producers prod = Some tt ->
  map.get consumers cons = Some tt ->
  prod <> cons ->
  get_path g prod cons fuel = Some path ->
  @DistributedDatalog.forwarding_reachable rel_id node_id
    (fwd_list (generate_forwarding_table gcontext ninfos g fuel)) rel0 prod cons.
Proof.
  intros Hrel Hprods Hcons Hprod Hcon Hne Hpath.
  destruct (@ComputableGraph.get_path_spec node_id node_id_eqb node_id_eqb_spec node_id_set
              node_id_set_ok node_id_edge_set g prod cons fuel path Hpath)
    as [_ [Hhd [Hlast _]]].
  set (FT := generate_forwarding_table gcontext ninfos g fuel).
  assert (Hchain : forall i x y, nth_error path i = Some x -> nth_error path (S i) = Some y ->
                     In y (fwd_list FT x rel0)).
  { intros i x y Hx Hy. unfold fwd_list.
    exact (generate_forwarding_table_adds g gcontext ninfos fuel rel0 prod cons path producers
             consumers i x y Hrel Hprods Hcons Hprod Hcon Hne Hpath Hx Hy). }
  destruct (@DistributedDatalog.forwarding_chain_reachable rel_id node_id
              (fwd_list FT) rel0 path prod cons Hchain Hhd Hlast) as [Heq | Hreach].
  - exfalso. apply Hne. exact Heq.
  - exact Hreach.
Qed.

(* Phase D conjunct (3), a direct reuse of Phase C [generate_forwarding_table_sound]: the
   compiled network's forwarding ([fwd_list] of the generated table) only routes along real
   graph edges, and (by [good_graph]) between real nodes. *)
Notation cg2g := (@ComputableGraph.computable_graph_to_graph node_id node_id_set node_id_edge_set).

Lemma compiled_good_forwarding_sound (g : node_graph) (gcontext : global_context)
    (ninfos : list node_info) (fuel : nat) :
  Graph.good_graph (cg2g g) ->
  @DistributedDatalog.good_forwarding_sound rel_id node_id
    (fwd_list (generate_forwarding_table gcontext ninfos g fuel))
    (Graph.nodes (cg2g g)) (Graph.edge (cg2g g)).
Proof.
  intros Hgg n1 n2 r Hin.
  assert (Hedge : @ComputableGraph.cg_edge node_id node_id_set node_id_edge_set g n1 n2)
    by exact (generate_forwarding_table_sound g gcontext ninfos fuel n1 r n2 Hin).
  destruct (Hgg n1 n2 Hedge) as [Hn1 Hn2].
  split; [exact Hn1 | split; [exact Hn2 | exact Hedge]].
Qed.

(* Phase D conjunct (4): every producer is a [good_source].  The output half is trivial (output
   lives on every node, pick the producer itself); the consumer half is discharged by the
   path-checker -- [routes_validatedb] validates, for each (producer, relation it concludes,
   consumer node that hypothesizes it), a forwarding route (the candidate path is [get_path]'s
   own output).  No relation/consumer enumeration and no gcontext: we iterate the layout's actual
   rules' [concl_rels]/[hyp_rels] and use [map.keys] to range over nodes. *)
Notation validate_route := (@DistributedDatalog.validate_route rel_id node_id node_id_eqb).

Definition route_or_self (g : node_graph) (fuel : nat) (np nc : node_id) : list node_id :=
  match get_path g np nc fuel with Some p => p | None => [] end.

Definition routes_validatedb (forward : node_id -> rel_id -> list node_id)
    (g : node_graph) (llayout : lowered_layout_map) (fuel : nat) : bool :=
  forallb (fun np =>
    forallb (fun rule_np =>
      forallb (fun R =>
        forallb (fun nc =>
          if existsb (fun rule_nc => existsb (Nat.eqb R) (Datalog.hyp_rels rule_nc)) (lprog_of llayout nc)
          then validate_route forward R np nc (route_or_self g fuel np nc)
          else true)
        (map.keys llayout))
      (Datalog.concl_rels rule_np))
    (lprog_of llayout np))
  (map.keys llayout).

Lemma routes_validatedb_good_source (g : node_graph) (llayout : lowered_layout_map) (fuel : nat)
    (net : DNet) :
  net.(DistributedDatalog.layout) = (fun n => lprog_of llayout n) ->
  (forall n R, net.(DistributedDatalog.output) n R) ->
  routes_validatedb net.(DistributedDatalog.forward) g llayout fuel = true ->
  forall n_prod R, DistributedDatalog.node_produces net.(DistributedDatalog.layout) n_prod R ->
    DistributedDatalog.good_source net n_prod R.
Proof.
  intros Hlay Hout Hchk n_prod R Hprod.
  rewrite Hlay in Hprod. destruct Hprod as [rule_np [Hin_np HR_concl]].
  destruct (map.get llayout n_prod) as [p_np|] eqn:Hgnp;
    [|exfalso; revert Hin_np; unfold lprog_of; rewrite Hgnp; intros []].
  assert (Hkey_np : In n_prod (map.keys llayout)) by exact (map.in_keys llayout n_prod p_np Hgnp).
  unfold routes_validatedb in Hchk. rewrite forallb_forall in Hchk. specialize (Hchk n_prod Hkey_np).
  rewrite forallb_forall in Hchk. specialize (Hchk rule_np Hin_np).
  rewrite forallb_forall in Hchk. specialize (Hchk R HR_concl).
  rewrite forallb_forall in Hchk.
  split.
  - intros n_cons Hcons. rewrite Hlay in Hcons. destruct Hcons as [rule_nc [Hin_nc HR_hyp]].
    destruct (map.get llayout n_cons) as [p_nc|] eqn:Hgnc;
      [|exfalso; revert Hin_nc; unfold lprog_of; rewrite Hgnc; intros []].
    assert (Hkey_nc : In n_cons (map.keys llayout)) by exact (map.in_keys llayout n_cons p_nc Hgnc).
    specialize (Hchk n_cons Hkey_nc).
    assert (Hex : existsb (fun rnc => existsb (Nat.eqb R) (Datalog.hyp_rels rnc)) (lprog_of llayout n_cons) = true).
    { apply existsb_exists. exists rule_nc. split.
      - exact Hin_nc.
      - apply existsb_exists. exists R. split; [exact HR_hyp | apply Nat.eqb_refl]. }
    rewrite Hex in Hchk.
    exact (DistributedDatalog.validate_route_sound net.(DistributedDatalog.forward) R n_prod n_cons
             (route_or_self g fuel n_prod n_cons) Hchk).
  - exists n_prod. split; [apply Hout | left; reflexivity].
Qed.

(* Phase D conjunct (5) support: the per-relation input node is also a [good_source].  Same
   path-checker, but ranging over each consumer's hypothesized relations and validating the route
   from [input_node R] to that consumer. *)
Definition input_routes_validatedb (forward : node_id -> rel_id -> list node_id)
    (g : node_graph) (llayout : lowered_layout_map) (fuel : nat) (input_node : rel_id -> node_id) : bool :=
  forallb (fun nc =>
    forallb (fun rule_nc =>
      forallb (fun R =>
        validate_route forward R (input_node R) nc (route_or_self g fuel (input_node R) nc))
      (Datalog.hyp_rels rule_nc))
    (lprog_of llayout nc))
  (map.keys llayout).

Lemma input_routes_validatedb_good_source (g : node_graph) (llayout : lowered_layout_map) (fuel : nat)
    (net : DNet) (input_node : rel_id -> node_id) :
  net.(DistributedDatalog.layout) = (fun n => lprog_of llayout n) ->
  (forall n R, net.(DistributedDatalog.output) n R) ->
  input_routes_validatedb net.(DistributedDatalog.forward) g llayout fuel input_node = true ->
  forall R, DistributedDatalog.good_source net (input_node R) R.
Proof.
  intros Hlay Hout Hchk R. split.
  - intros n_cons Hcons. rewrite Hlay in Hcons. destruct Hcons as [rule_nc [Hin_nc HR_hyp]].
    destruct (map.get llayout n_cons) as [p_nc|] eqn:Hgnc;
      [|exfalso; revert Hin_nc; unfold lprog_of; rewrite Hgnc; intros []].
    assert (Hkey_nc : In n_cons (map.keys llayout)) by exact (map.in_keys llayout n_cons p_nc Hgnc).
    unfold input_routes_validatedb in Hchk. rewrite forallb_forall in Hchk. specialize (Hchk n_cons Hkey_nc).
    rewrite forallb_forall in Hchk. specialize (Hchk rule_nc Hin_nc).
    rewrite forallb_forall in Hchk. specialize (Hchk R HR_hyp).
    exact (DistributedDatalog.validate_route_sound net.(DistributedDatalog.forward) R (input_node R) n_cons
             (route_or_self g fuel (input_node R) n_cons) Hchk).
  - exists (input_node R). split; [apply Hout | left; reflexivity].
Qed.

(* The compiled streaming network's topology/forwarding/IO half (its datalog layout is forced on
   top by [dnet_of_llayout]): the real graph, the generated forwarding table's [fwd_list], base
   facts [Q] streamed at each relation's [input_node], output available everywhere. *)
Definition compiled_base (g : node_graph) (ftables : node_ftable_map)
    (input_node : rel_id -> node_id) (Q : Datalog.fact rel_id T -> Prop) : DNet :=
  {| DistributedDatalog.graph   := cg2g g;
     DistributedDatalog.forward := fwd_list ftables;
     DistributedDatalog.input   := fun n f => Q f /\ n = input_node (Datalog.rel_of f);
     DistributedDatalog.output  := fun _ _ => True;
     DistributedDatalog.layout  := fun _ => [] |}.

(* PHASE D MAIN: the compiled network is [good_network_streaming].  Conjuncts (1) good_graph and
   (2) good_layout are checker-discharged side conditions; (3) forwarding-soundness is Phase C
   ([ftable_edges_sound]); (4) producers and (5) the input nodes are good sources by the
   path-checkers.  Feeding this into [compile_all_distributes_correct] closes the loop to
   [prog_impl] over compile's OWN forwarding table. *)
Theorem compiled_good_network_streaming
    (g : node_graph) (ftables : node_ftable_map) (fuel : nat) (input_node : rel_id -> node_id)
    (llayout : lowered_layout_map)
    (program : list (Datalog.rule rel_id var nat aggregator)) (Q : Datalog.fact rel_id T -> Prop) :
  Graph.good_graph (cg2g g) ->
  DistributedDatalog.good_layout (fun n => lprog_of llayout n) (Graph.nodes (cg2g g)) program ->
  ftable_edges_sound g ftables ->
  routes_validatedb (fwd_list ftables) g llayout fuel = true ->
  input_routes_validatedb (fwd_list ftables) g llayout fuel input_node = true ->
  DistributedDatalog.good_network_streaming
    (dnet_of_llayout llayout (compiled_base g ftables input_node Q)) program Q.
Proof.
  intros Hgg Hlay Hsound Hroutes Hinput.
  unfold DistributedDatalog.good_network_streaming, dnet_of_llayout, compiled_base; cbn.
  split; [exact Hgg|].
  split; [exact Hlay|].
  split.
  - (* (3) forwarding soundness, from Phase C *)
    intros n1 n2 r Hin.
    assert (Hedge : @ComputableGraph.cg_edge node_id node_id_set node_id_edge_set g n1 n2)
      by exact (Hsound n1 r n2 Hin).
    destruct (Hgg n1 n2 Hedge) as [Hn1 Hn2]. split; [exact Hn1 | split; [exact Hn2 | exact Hedge]].
  - split.
    + (* (4) producers are good sources *)
      apply (routes_validatedb_good_source g llayout fuel
               (dnet_of_llayout llayout (compiled_base g ftables input_node Q)));
        [reflexivity | intros; exact I | exact Hroutes].
    + split.
      * (* (5a) input facts come from Q *)
        intros n f [HQ _]. exact HQ.
      * (* (5b) each base fact enters at a good-source input node *)
        intros f HQ. exists (input_node (Datalog.rel_of f)). split.
        -- split; [exact HQ | reflexivity].
        -- apply (input_routes_validatedb_good_source g llayout fuel
                    (dnet_of_llayout llayout (compiled_base g ftables input_node Q)) input_node);
             [reflexivity | intros; exact I | exact Hinput].
Qed.

(* PHASE D CLOSE-THE-LOOP: the compiled hardware network, run over the compiler's OWN generated
   forwarding table ([generate_forwarding_table]), derives exactly the facts the program derives
   from the streamed base facts [Q].  Phase-C [generate_forwarding_table_sound] discharges the
   forwarding-soundness obligation for free; the remaining side conditions are the per-node
   compilation success, the bareness/graph/layout checks, and the two route checkers. *)
Theorem compile_streaming_forwarding_correct
    (g : node_graph) (gcontext : global_context) (ninfos : list node_info) (fuel : nat)
    (llayout : lowered_layout_map) (input_node : rel_id -> node_id)
    (program : list (Datalog.rule rel_id var nat aggregator)) (Q : Datalog.fact rel_id T -> Prop) :
  compile_all_nodes llayout gcontext = Success ninfos ->
  bare_layoutb llayout = true ->
  Graph.good_graph (cg2g g) ->
  DistributedDatalog.good_layout (fun n => lprog_of llayout n) (Graph.nodes (cg2g g)) program ->
  routes_validatedb (fwd_list (generate_forwarding_table gcontext ninfos g fuel)) g llayout fuel = true ->
  input_routes_validatedb (fwd_list (generate_forwarding_table gcontext ninfos g fuel)) g llayout fuel input_node = true ->
  forall f, EncodeDistributed.hw_net_prog_impl_fact
              (compiled_hn llayout gcontext
                 (dnet_of_llayout llayout
                    (compiled_base g (generate_forwarding_table gcontext ninfos g fuel) input_node Q))) f
            <-> DistributedDatalog.prog_impl_fact program Q f.
Proof.
  intros Hcan Hbare Hgg Hlay Hroutes Hinput.
  apply (compile_all_distributes_correct llayout gcontext ninfos
           (compiled_base g (generate_forwarding_table gcontext ninfos g fuel) input_node Q)
           program Q Hcan Hbare).
  apply (compiled_good_network_streaming g (generate_forwarding_table gcontext ninfos g fuel) fuel
           input_node llayout program Q Hgg Hlay
           (generate_forwarding_table_sound g gcontext ninfos fuel) Hroutes Hinput).
Qed.

(*============================================================================*)
(*  Bridge to the REFERENCE single-program semantics [Datalog.prog_impl]        *)
(*============================================================================*)

(* For a bare (normal) rule, [rule_impl] can only produce a normal fact (the [meta_rule_impl]
   constructor needs a [meta_rule]). *)
Lemma bare_rule_impl_normal (env : list (Datalog.fact rel_id T) -> rel_id -> list T -> Prop)
    (r : Datalog.rule rel_id var nat aggregator) (f : Datalog.fact rel_id T)
    (hyps : list (Datalog.fact rel_id T)) :
  bare_rule r -> Datalog.rule_impl env r f hyps -> exists R args, f = Datalog.normal_fact R args.
Proof.
  intros Hbare H. destruct r as [concls hyps0 | concls hyps0 | concl agg hyp];
    [|cbn in Hbare; contradiction..].
  inversion H; subst. eexists; eexists; reflexivity.
Qed.

(* [DistributedDatalog]'s env-free network derivability coincides with the reference
   [Datalog.prog_impl] on the bare/normal fragment the compiler targets: [fires] and [rule_impl]
   agree on normal facts (the only facts a bare program ever derives). *)
Lemma prog_impl_fact_iff_datalog (program : list (Datalog.rule rel_id var nat aggregator))
    (Q : Datalog.fact rel_id T -> Prop) (f : Datalog.fact rel_id T) :
  Forall bare_rule program ->
  DistributedDatalog.prog_impl_fact program Q f <-> Datalog.prog_impl program Q f.
Proof.
  intros Hbare. unfold DistributedDatalog.prog_impl_fact, Datalog.prog_impl. split.
  - apply EncodeNode.pftree_weaken. intros x l Hx.
    apply Exists_exists in Hx. destruct Hx as [r [Hin Hfires]].
    apply Exists_exists. exists r. split; [exact Hin|].
    apply (proj2 (EncodeDistributed.rule_impl_iff_fires (Datalog.one_step_derives program) r x l
                    (match Hfires with ex_intro _ R (ex_intro _ args (conj He _)) =>
                       ex_intro _ R (ex_intro _ args He) end))).
    exact Hfires.
  - apply EncodeNode.pftree_weaken. intros x l Hx.
    apply Exists_exists in Hx. destruct Hx as [r [Hin Hri]].
    apply Exists_exists. exists r. split; [exact Hin|].
    pose proof (proj1 (Forall_forall _ _) Hbare r Hin) as Hbr.
    pose proof (bare_rule_impl_normal (Datalog.one_step_derives program) r x l Hbr Hri) as Hnorm.
    exact (proj1 (EncodeDistributed.rule_impl_iff_fires (Datalog.one_step_derives program) r x l Hnorm) Hri).
Qed.

(* PHASE D, connected to the REFERENCE Datalog semantics: the compiled hardware network derives
   exactly the facts the reference single-program [Datalog.prog_impl] derives from [Q]. *)
Theorem compile_streaming_correct_datalog
    (g : node_graph) (gcontext : global_context) (ninfos : list node_info) (fuel : nat)
    (llayout : lowered_layout_map) (input_node : rel_id -> node_id)
    (program : list (Datalog.rule rel_id var nat aggregator)) (Q : Datalog.fact rel_id T -> Prop) :
  compile_all_nodes llayout gcontext = Success ninfos ->
  bare_layoutb llayout = true ->
  Forall bare_rule program ->
  Graph.good_graph (cg2g g) ->
  DistributedDatalog.good_layout (fun n => lprog_of llayout n) (Graph.nodes (cg2g g)) program ->
  routes_validatedb (fwd_list (generate_forwarding_table gcontext ninfos g fuel)) g llayout fuel = true ->
  input_routes_validatedb (fwd_list (generate_forwarding_table gcontext ninfos g fuel)) g llayout fuel input_node = true ->
  forall f, EncodeDistributed.hw_net_prog_impl_fact
              (compiled_hn llayout gcontext
                 (dnet_of_llayout llayout
                    (compiled_base g (generate_forwarding_table gcontext ninfos g fuel) input_node Q))) f
            <-> Datalog.prog_impl program Q f.
Proof.
  intros Hcan Hbare Hbareprog Hgg Hlay Hroutes Hinput f.
  rewrite (compile_streaming_forwarding_correct g gcontext ninfos fuel llayout input_node program Q
             Hcan Hbare Hgg Hlay Hroutes Hinput f).
  apply prog_impl_fact_iff_datalog. exact Hbareprog.
Qed.

End CompileTop.
