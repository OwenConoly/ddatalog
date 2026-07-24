(* Correctness of [DistributedDatalogToHardwareCompiler.compile] against the trie-join semantics of [NodeHardwareSemantics],
   for the *bare-variable* (SuperNice) fragment: every hypothesis/conclusion argument is a
   bare variable [var_expr].  (Function-application arguments in premises/conclusions are not yet
   handled by the compiler -- see DistributedDatalogToHardwareCompiler.generate_join / compile_concl -- and are out of
   scope here.)

   The chain is:

     source datalog  --(rename, DistributedDatalogToHardwareCompiler)-->  lowered_program
        |  Datalog.prog_impl_fact                     |  NodeHardwareSemantics.lprog_impl_fact (= Datalog on ids)
        |                                             |  ===  NodeHardwareSemantics.hw_prog_impl_fact
        +---------------------------------------------+      (this file: per-rule bridge)

   [NodeHardwareSemantics.hw_prog_correct] already reduces whole-node correctness to the per-rule predicate
   [hw_rule_matches].  This file works toward [hw_rule_matches] for rules the (now fixed)
   [compile_rule] produces, i.e. the *generic-join correctness*: the trie-join query
   [generate_query] admits exactly the variable bindings under which the lowered rule fires. *)

From Datalog Require Import Datalog.
From Stdlib Require Import List Bool ZArith Lia.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Datatypes.Result Eqb.
From DatalogRocq Require Import HardwareProgram DistributedDatalogToHardwareCompiler NodeHardwareSemantics ComputableGraph.
From DatalogRocq Require Import DistributedDatalog DistributedHardwareSemantics.
From DatalogRocq Require Import ForwardingCorrect RelabelCorrect.

Import ListNotations.

(* Helper: recover the [BoolSpec] form of variable equality from the new core's [Eqb] typeclass.
   Replaces the old [var_eqb_spec] section hypothesis; every [destruct (var_eqb_spec ...)] site
   below resolves [var]/[var_eqb]/[var_eqb_ok] implicitly from its section context. *)
Lemma var_eqb_spec {var : exprvarT} {var_eqb : Eqb var} {var_eqb_ok : Eqb_ok var_eqb}
  (x y : var) : BoolSpec (x = y) (x <> y) (var_eqb x y).
Proof.
  pose proof (eqb_spec x y) as H. cbv [eqb] in H.
  destruct (var_eqb x y); [apply BoolSpecT | apply BoolSpecF]; exact H.
Qed.

Lemma rel_eqb_spec {rel : relT} {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}
  (x y : rel) : BoolSpec (x = y) (x <> y) (rel_eqb x y).
Proof.
  pose proof (eqb_spec x y) as H. cbv [eqb] in H.
  destruct (rel_eqb x y); [apply BoolSpecT | apply BoolSpecF]; exact H.
Qed.

Section DistributedDatalogToHardwareCompilerCorrect.

Context {var : exprvarT} {aggregator : aggregatorT} {T : valueT}.
Context `{sig : signature nat aggregator T}.
Context {context : map.map var T} {context_ok : map.ok context}.
Context {var_eqb : Eqb var} {var_eqb_ok : Eqb_ok var_eqb}.
Context {var_idx_map : map.map var nat}.   (* used by compute_permutation *)
Context {var_idx_map_ok : map.ok var_idx_map}.

Notation lowered_fact := (@HardwareProgram.lowered_fact var).
Notation lowered_rule := (@HardwareProgram.lowered_rule var aggregator).
Notation generate_query := (@DistributedDatalogToHardwareCompiler.generate_query var var_eqb).
Notation generate_join := (@DistributedDatalogToHardwareCompiler.generate_join var var_eqb).
Notation compute_var_order := (@DistributedDatalogToHardwareCompiler.compute_var_order var).

(* the tuple of a (normal) ground fact; meta facts (never produced by the bare fragment)
   read as []. *)
Definition nfargs (f : Datalog.fact (rel := rel_id)) : list T :=
  match f with Datalog.normal_fact _ a => a | _ => [] end.

(*----Trie-generation facts (toward hooking up compile_rule)----*)

(* [permutation_eqb] reflects list equality; needed to read off [generate_trie]'s output. *)
Lemma permutation_eqb_eq (p1 p2 : list nat) :
  DistributedDatalogToHardwareCompiler.permutation_eqb p1 p2 = true -> p1 = p2.
Proof.
  unfold DistributedDatalogToHardwareCompiler.permutation_eqb. intros H.
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
   ([DistributedDatalogToHardwareCompiler.global_rename_rule]/[compile_rule]) error out on any non-[normal_rule], so a
   lowered program is normal by construction.  A lowered fact/expr likewise IS a [Datalog]
   clause/expr over numeric ids. *)

(* A [normal_rule] fires (env-free, since its conclusion is a [normal_fact]) exactly when some
   context interprets all its hypothesis clauses to [hyps'] and one conclusion clause to [f]. *)
Lemma lrule_impl_iff (concls hyps : list lowered_fact)
    (env : list (Datalog.fact (rel := rel_id)) -> rel_id -> list T -> Prop)
    (f : Datalog.fact (rel := rel_id)) (hyps' : list (Datalog.fact (rel := rel_id))) :
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
  unfold bare_fact, DistributedDatalogToHardwareCompiler.compute_var_order. intros H.
  induction lf.(Datalog.clause_args) as [|a args IH]; simpl in *.
  - reflexivity.
  - inversion H as [|x l [v Hv] H']; subst. simpl. rewrite IH; auto.
Qed.

(*----generate_query: shape lemmas (proved)----*)

(* One join per variable in the ordering. *)
Lemma generate_query_length (tb : list trie) (ord : list var) (hyps : list lowered_fact) :
  length (generate_query tb ord hyps) = length ord.
Proof. unfold DistributedDatalogToHardwareCompiler.generate_query. apply length_map. Qed.

(* The i-th join is the join for the i-th variable in the ordering (default-free form). *)
Lemma generate_query_nth_error (tb : list trie) (ord : list var)
    (hyps : list lowered_fact) (i : nat) :
  nth_error (generate_query tb ord hyps) i
  = option_map (fun v => generate_join tb v hyps) (nth_error ord i).
Proof. unfold DistributedDatalogToHardwareCompiler.generate_query. apply nth_error_map. Qed.

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
Lemma join_output_fact_spec (vals : list T) (jo : join_output) (f : Datalog.fact (rel := rel_id)) :
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
  interp_expr ctx (var_expr v : Datalog.expr (fn := nat)) x <-> map.get ctx v = Some x.
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
    (ctx : context) (jo : join_output) (f : Datalog.fact (rel := rel_id)) :
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

Notation ccount := (@DistributedDatalogToHardwareCompiler.count_occ var var_eqb).
Notation cperm_aux := (@DistributedDatalogToHardwareCompiler.compute_perm_aux var var_idx_map).
Notation cperm := (@DistributedDatalogToHardwareCompiler.compute_permutation var var_eqb var_idx_map).
Notation bbm := (@DistributedDatalogToHardwareCompiler.build_base_map var var_eqb var_idx_map).

Definition mget0 (m : var_idx_map) (v : var) : nat :=
  match map.get m v with Some n => n | None => 0 end.

Lemma var_eqb_refl (v : var) : var_eqb v v = true.
Proof. destruct (var_eqb_spec v v); congruence. Qed.

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
  - cbn [nth firstn DistributedDatalogToHardwareCompiler.count_occ]. lia.
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
Proof. unfold DistributedDatalogToHardwareCompiler.compute_permutation. apply cperm_aux_length. Qed.

Lemma compute_permutation_nth (original desired : list var) (i : nat) (d : var) :
  i < length original ->
  nth i (cperm original desired) 0 =
    mget0 (bbm desired original 0 map.empty) (nth i original d)
      + ccount (nth i original d) (firstn i original).
Proof.
  intros Hi. unfold DistributedDatalogToHardwareCompiler.compute_permutation.
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
  - unfold DistributedDatalogToHardwareCompiler.compute_permutation. simpl. constructor.
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
  unfold DistributedDatalogToHardwareCompiler.generate_join, gj_entries.
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
  In a (DistributedDatalogToHardwareCompiler.get_hyp_arg_indices (var_eqb := var_eqb) args v i) <->
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
   bookkeeping is discharged by [trie_read_NoDup] (already proved in NodeHardwareSemantics) once the
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
    (vals : list T) (hyps' : list (Datalog.fact (rel := rel_id))) (dt : trie) (dh : lowered_fact) :
  NoDup ord ->
  Forall bare_fact hyps ->
  length tb = length hyps ->
  length hyps' = length hyps ->
  length vals = length ord ->
  (forall v, In v (flat_map compute_var_order hyps) -> In v ord) ->
  (forall i, i < length hyps ->
     (nth i tb dt).(trel) = (nth i hyps dh).(Datalog.clause_rel) /\
     (nth i tb dt).(tperm) = DistributedDatalogToHardwareCompiler.compute_permutation (var_eqb := var_eqb)
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
        unfold compute_var_order, DistributedDatalogToHardwareCompiler.compute_var_order. apply in_flat_map.
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

(* The per-conclusion fact [compile_concl] establishes: the conclusion is bare and each output
   index is the ordering position of the corresponding variable. *)
Definition concl_corr (ord : list var) (c : lowered_fact) (jo : join_output) : Prop :=
  jo.(output_rel) = c.(Datalog.clause_rel) /\
  Forall2 (fun e idx => exists v, e = var_expr v /\ nth_error ord idx = Some v)
          c.(Datalog.clause_args) jo.(output_var_indices).

(* Lifting [join_output_fact_interp] over the whole conclusion list: under the induced context,
   the trie-join's conclusion outputs are exactly the lowered rule's conclusion facts. *)
Lemma concl_exists_iff (ord : list var) (vals : list T) (ctx : context)
    (concls : list lowered_fact) (jos : list join_output) (f : Datalog.fact (rel := rel_id)) :
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
    (ord : list var) (ctx ctx' : context) (f : Datalog.fact (rel := rel_id)) :
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
  unfold DistributedDatalogToHardwareCompiler.compute_var_order. apply in_flat_map.
  exists (var_expr w). split; [exact Hein | simpl; auto].
Qed.

(*----per-hypothesis relation/arity facts----*)

(* the per-clause [hsig] shape check, exactly as in [NodeHardwareSemantics.hw_rule_impl]. *)
Notation hsig_ok := (fun (sg : rel_id * nat) (fct : Datalog.fact (rel := rel_id)) =>
  match fct with
  | Datalog.normal_fact R args => R = fst sg /\ length args = snd sg
  | _ => False
  end).

(* Each hypothesis fact is the [normal_fact] with the clause's relation and arity, read off
   from [interp_clause]. *)
Lemma interp_hyp_arity (ctx : context) (rule_hyps : list lowered_fact)
    (hyps' : list (Datalog.fact (rel := rel_id))) (dh : lowered_fact) (i : nat) :
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
    (hyps' : list (Datalog.fact (rel := rel_id))) :
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
Lemma hsig_length (rule_hyps : list lowered_fact) (hyps' : list (Datalog.fact (rel := rel_id))) :
  Forall2 hsig_ok
          (map (fun h => (h.(Datalog.clause_rel), length h.(Datalog.clause_args))) rule_hyps) hyps' ->
  length hyps' = length rule_hyps.
Proof.
  intros HF. apply Forall2_length in HF. rewrite length_map in HF. symmetry; exact HF.
Qed.

Lemma hsig_arity (rule_hyps : list lowered_fact) (hyps' : list (Datalog.fact (rel := rel_id)))
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
   exactly the facts [lr] derives.  This discharges [NodeHardwareSemantics.hw_rule_matches] for compiled
   rules (bare/SuperNice fragment), combining [generate_query_correct] (hypotheses) with
   [concl_exists_iff] (conclusions). *)
Theorem hw_rule_correct
    (concls hyps : list lowered_fact) (hr : hardware_rule)
    (env : list (Datalog.fact (rel := rel_id)) -> rel_id -> list T -> Prop)
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
     (nth i tb dt).(tperm) = DistributedDatalogToHardwareCompiler.compute_permutation (var_eqb := var_eqb)
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
       (nth i tb dt).(tperm) = DistributedDatalogToHardwareCompiler.compute_permutation (var_eqb := var_eqb)
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
      { unfold DistributedDatalogToHardwareCompiler.compute_var_order in Hvco. apply in_flat_map in Hvco.
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
       (nth i tb dt).(tperm) = DistributedDatalogToHardwareCompiler.compute_permutation (var_eqb := var_eqb)
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

End DistributedDatalogToHardwareCompilerCorrect.

(*============================================================================*)
(*  Discharge lemmas: structural facts about [DistributedDatalogToHardwareCompiler.compile_rule]'s      *)
(*  output that feed [hw_rule_correct].  These are the *definitional* facts      *)
(*  (the per-hypothesis trie's relation/permutation, the query shape, and the    *)
(*  conclusion index correspondence).  They need DistributedDatalogToHardwareCompiler's full parameter   *)
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

(* DistributedDatalogToHardwareCompiler's parameter context (the subset the relevant definitions use). *)
Context {rel : relT} {var : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
Context {var_eqb : Eqb var} {var_eqb_ok : Eqb_ok var_eqb}.
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
  (@DistributedDatalogToHardwareCompiler.global_context rel node_id node_id_set rel_dependency_map rel_relid_map).
Notation node_context := (@DistributedDatalogToHardwareCompiler.node_context node_id).
Notation generate_trie :=
  (@DistributedDatalogToHardwareCompiler.generate_trie rel var var_eqb node_id node_id_set rel_dependency_map rel_relid_map var_idx_map).
Notation compile_hyps :=
  (@DistributedDatalogToHardwareCompiler.compile_hyps rel var var_eqb node_id node_id_set rel_dependency_map rel_relid_map var_idx_map).
Notation compile_concl :=
  (@DistributedDatalogToHardwareCompiler.compile_concl rel var var_eqb node_id node_id_set rel_dependency_map rel_relid_map).
Notation compile_concls :=
  (@DistributedDatalogToHardwareCompiler.compile_concls rel var var_eqb node_id node_id_set rel_dependency_map rel_relid_map).
Notation generate_query := (@DistributedDatalogToHardwareCompiler.generate_query var var_eqb).
Notation compute_var_order := (@DistributedDatalogToHardwareCompiler.compute_var_order var).
Notation compute_permutation := (@DistributedDatalogToHardwareCompiler.compute_permutation var var_eqb var_idx_map).
Notation get_rule_var_index := (@DistributedDatalogToHardwareCompiler.get_rule_var_index var var_eqb).
Notation index_of_var := (@DistributedDatalogToHardwareCompiler.index_of_var var var_eqb).
Notation index_of_var_aux := (@DistributedDatalogToHardwareCompiler.index_of_var_aux var var_eqb).

(* [generate_trie] always returns a trie indexing the hypothesis's relation by the
   permutation computed for that hypothesis -- whether it freshly allocates one or
   reuses an existing trie found by [find] (whose predicate forces both fields). *)
Lemma generate_trie_spec (hyp : lowered_fact) (ord : list var)
    (existing : list trie) (gc : global_context) (nc : node_context) (t : trie) (nc' : node_context) :
  generate_trie hyp ord existing gc nc = (t, nc') ->
  t.(trel) = hyp.(Datalog.clause_rel) /\
  t.(tperm) = compute_permutation (compute_var_order hyp) ord.
Proof.
  intros H. unfold DistributedDatalogToHardwareCompiler.generate_trie in H. cbv zeta in H.
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
  unfold DistributedDatalogToHardwareCompiler.index_of_var. intros H.
  destruct (index_of_var_aux_sound v vars 0 idx H) as [k [-> Hk]].
  rewrite Nat.add_0_l. exact Hk.
Qed.

Lemma get_rule_var_index_sound (ord : list var) (v : var) (idx : nat) :
  get_rule_var_index ord v = Success idx -> List.nth_error ord idx = Some v.
Proof.
  unfold DistributedDatalogToHardwareCompiler.get_rule_var_index.
  destruct (index_of_var v ord) as [i|] eqn:Hi; [|discriminate].
  intros H. injection H as <-. apply index_of_var_sound; exact Hi.
Qed.

(* [all_success] succeeds exactly when every element already succeeded: the input list is then
   [map Success] of the returned values.  This replaces the earlier hand-rolled [fold_left]
   spec/error helpers, now that the compiler builds its lists with [List.all_success (List.map ..)]
   instead of a reversing [fold_left]. *)
Lemma all_success_eq_map_Success {A} :
  forall (l : list (result A)) (l' : list A),
  List.all_success l = Success l' -> l = List.map Success l'.
Proof.
  induction l as [|r l IH]; intros l' H; cbn in H.
  - injection H as <-. reflexivity.
  - destruct r as [a|e]; [|discriminate].
    destruct (List.all_success l) as [ls|e] eqn:Hl; [|discriminate].
    injection H as <-. cbn. f_equal. apply IH; reflexivity.
Qed.

(* Consequently, if each element's producer [g] sends a [Success] result to a fact [P a b], then
   [all_success (map g l)] yields the pointwise [Forall2 P]. *)
Lemma all_success_map_spec {A B} (g : A -> result B) (P : A -> B -> Prop) :
  forall (l : list A) (out : list B),
  Forall (fun a => forall b, g a = Success b -> P a b) l ->
  List.all_success (List.map g l) = Success out ->
  Forall2 P l out.
Proof.
  intros l out HF Has. apply all_success_eq_map_Success in Has.
  revert out Has. induction HF as [|a l Ha HF IH]; intros out Has; cbn in Has.
  - destruct out; cbn in Has; [constructor | discriminate].
  - destruct out as [|b out]; cbn in Has; [discriminate|].
    injection Has as Hab Hrest. constructor; [apply Ha; exact Hab | apply IH; exact Hrest].
Qed.

(* A compiled (bare) conclusion's join_output relation and indices correspond to the
   lowered conclusion: each output index is the ordering position of that variable.
   This is exactly [DistributedDatalogToHardwareCompilerCorrect.concl_corr]. *)
Lemma compile_concl_corr (concl : lowered_fact) (gc : global_context) (ord : list var)
    (jo : join_output) :
  Forall (fun e => exists v, e = var_expr v) concl.(Datalog.clause_args) ->
  compile_concl concl gc ord = Success jo ->
  jo.(output_rel) = concl.(Datalog.clause_rel) /\
  Forall2 (fun e idx => exists v, e = var_expr v /\ List.nth_error ord idx = Some v)
          concl.(Datalog.clause_args) jo.(output_var_indices).
Proof.
  intros Hbare H. unfold DistributedDatalogToHardwareCompiler.compile_concl in H.
  match type of H with
  | context [List.all_success ?x] => destruct (List.all_success x) as [var_indices|e] eqn:Has
  end; cbn beta iota in H; [|discriminate].
  injection H as <-. cbn. split; [reflexivity|].
  eapply all_success_map_spec; [| exact Has].
  eapply Forall_impl; [| exact Hbare].
  intros a [v ->] b Hb. cbn in Hb.
  exists v; split; [reflexivity | apply get_rule_var_index_sound; exact Hb].
Qed.

(* [compile_concls] yields the per-conclusion correspondence [concl_corr] over the whole list. *)
Lemma compile_concls_corr (concls : list lowered_fact) (gc : global_context) (ord : list var)
    (jos : list join_output) :
  Forall (fun c => Forall (fun e => exists v, e = var_expr v) c.(Datalog.clause_args)) concls ->
  compile_concls concls gc ord = Success jos ->
  Forall2 (concl_corr ord) concls jos.
Proof.
  intros Hb H. unfold DistributedDatalogToHardwareCompiler.compile_concls in H.
  eapply all_success_map_spec; [| exact H].
  eapply Forall_impl; [| exact Hb].
  intros c Hc jo Hcc. cbn beta in Hcc.
  exact (compile_concl_corr c gc ord jo Hc Hcc).
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
  NodeHardwareSemantics.lookup_trie l t.(tid) = Some t.
Proof. unfold NodeHardwareSemantics.lookup_trie. apply find_tid_unique. Qed.

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
  intros H. unfold DistributedDatalogToHardwareCompiler.generate_trie in H. cbv zeta in H.
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
  intros H Hwf. unfold DistributedDatalogToHardwareCompiler.compile_hyps in H.
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
  intros H Hwf. unfold DistributedDatalogToHardwareCompiler.compile_hyps in H.
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

Context {var : exprvarT}.
Context {var_eqb : Eqb var} {var_eqb_ok : Eqb_ok var_eqb}.
Context {var_node_set : map.map var unit} {var_node_set_ok : map.ok var_node_set}.
Context {var_edge_set : map.map var var_node_set}.

Notation ordering_context := (@DistributedDatalogToHardwareCompiler.ordering_context var var_node_set var_edge_set).
Notation var_graph := (@DistributedDatalogToHardwareCompiler.var_graph var var_node_set var_edge_set).
Notation lowered_fact := (@HardwareProgram.lowered_fact var).
Notation choose := (@DistributedDatalogToHardwareCompiler.choose_next_var_ordered var var_node_set var_edge_set).
Notation visit_node := (@DistributedDatalogToHardwareCompiler.visit_node var var_node_set var_edge_set).
Notation dedup := (@DistributedDatalogToHardwareCompiler.dedup var var_node_set).
Notation collect_vars_fact := (@DistributedDatalogToHardwareCompiler.collect_vars_fact var).
Notation collect_vars_hyps := (@DistributedDatalogToHardwareCompiler.collect_vars_hyps var).
Notation compute_var_order := (@DistributedDatalogToHardwareCompiler.compute_var_order var).

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
  unfold DistributedDatalogToHardwareCompiler.choose_next_var_ordered.
  destruct (DistributedDatalogToHardwareCompiler.compute_max_degree_var_to_visited_set_ordered _ _ _)
    as [[v1 d1]|] eqn:H1.
  - intros H. injection H as <-.
    unfold DistributedDatalogToHardwareCompiler.compute_max_degree_var_to_visited_set_ordered in H1.
    apply (fold_mstep_acc ctx.(dep_graph).(nodes)
             (DistributedDatalogToHardwareCompiler.compute_degree_to_visited_set ctx.(dep_graph) ctx.(visited)) cs None v1 d1)
      in H1.
    destruct H1 as [[Hin Hne]|H1]; [split; assumption | discriminate].
  - destruct (DistributedDatalogToHardwareCompiler.compute_max_degree_var_ordered _ _) as [[v2 d2]|] eqn:H2; [|discriminate].
    intros H. injection H as <-.
    unfold DistributedDatalogToHardwareCompiler.compute_max_degree_var_ordered in H2.
    apply (fold_mstep_acc ctx.(dep_graph).(nodes)
             (DistributedDatalogToHardwareCompiler.compute_degree ctx.(dep_graph)) cs None v2 d2) in H2.
    destruct H2 as [[Hin Hne]|H2]; [split; assumption | discriminate].
Qed.

(* ... and returns [None] only when no candidate is a current graph node. *)
Lemma choose_None (ctx : ordering_context) (cs : list var) :
  choose ctx cs = None ->
  forall v, In v cs -> map.get ctx.(dep_graph).(nodes) v = None.
Proof.
  unfold DistributedDatalogToHardwareCompiler.choose_next_var_ordered.
  destruct (DistributedDatalogToHardwareCompiler.compute_max_degree_var_to_visited_set_ordered _ _ _)
    as [[v1 d1]|] eqn:H1; [discriminate|].
  destruct (DistributedDatalogToHardwareCompiler.compute_max_degree_var_ordered _ _) as [[v2 d2]|] eqn:H2; [discriminate|].
  intros _ v Hv.
  unfold DistributedDatalogToHardwareCompiler.compute_max_degree_var_ordered in H2.
  apply (fold_mstep_None ctx.(dep_graph).(nodes) (DistributedDatalogToHardwareCompiler.compute_degree ctx.(dep_graph)) cs None)
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
  unfold DistributedDatalogToHardwareCompiler.collect_vars_fact, DistributedDatalogToHardwareCompiler.compute_var_order.
  induction h.(Datalog.clause_args) as [|a args IH]; intros Hb; simpl; [reflexivity|].
  inversion Hb as [|x l [v ->] Hb']; subst. simpl. f_equal. apply IH; exact Hb'.
Qed.

Lemma bare_collect_vars_hyps (hyps : list lowered_fact) :
  Forall (fun h => Forall (fun e => exists v, e = var_expr v) h.(Datalog.clause_args)) hyps ->
  collect_vars_hyps hyps = flat_map compute_var_order hyps.
Proof.
  unfold DistributedDatalogToHardwareCompiler.collect_vars_hyps.
  induction hyps as [|h hyps IH]; intros Hb; simpl; [reflexivity|].
  inversion Hb as [|x l Hbh Hb']; subst.
  rewrite (bare_collect_vars_fact h Hbh), (IH Hb'). reflexivity.
Qed.

(*----the greedy loop: NoDup + subset + full coverage----*)

Notation cvo_h := (@DistributedDatalogToHardwareCompiler.compute_variable_ordering_ordered_h var var_node_set var_edge_set).

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
  (DistributedDatalogToHardwareCompiler.add_arg_edges (var_expr v) g cv).(nodes) = map.put g.(nodes) v tt.
Proof.
  cbn [DistributedDatalogToHardwareCompiler.add_arg_edges].
  erewrite addarg_fold_nodes; [reflexivity | intros acc u x; reflexivity].
Qed.

Lemma add_args_edges_mono (args : list (@HardwareProgram.lowered_expr var)) :
  forall (g : var_graph) (seen : var_node_set) (w : var),
  Forall (fun e => exists u, e = var_expr u) args ->
  map.get g.(nodes) w <> None ->
  map.get (DistributedDatalogToHardwareCompiler.add_args_edges args g seen).(nodes) w <> None.
Proof.
  induction args as [|a args IH]; intros g seen w Hb Hg; simpl; [exact Hg|].
  inversion Hb as [|x l [u ->] Hb']; subst.
  apply (IH (DistributedDatalogToHardwareCompiler.add_arg_edges (var_expr u) g seen) (map.put seen u tt) w Hb').
  rewrite add_arg_edges_LVar_nodes.
  destruct (var_eqb_spec u w) as [->|Hne].
  - rewrite map.get_put_same. discriminate.
  - rewrite (map.get_put_diff g.(nodes) w tt u (not_eq_sym Hne)). exact Hg.
Qed.

Lemma add_args_edges_covers (args : list (@HardwareProgram.lowered_expr var)) :
  forall (g : var_graph) (seen : var_node_set) (w : var),
  Forall (fun e => exists u, e = var_expr u) args ->
  In (var_expr w) args ->
  map.get (DistributedDatalogToHardwareCompiler.add_args_edges args g seen).(nodes) w <> None.
Proof.
  induction args as [|a args IH]; intros g seen w Hb Hin; simpl in Hin; [contradiction|].
  inversion Hb as [|x l [u ->] Hb']; subst. simpl. destruct Hin as [Heq | Hin].
  - injection Heq as ->.
    apply (add_args_edges_mono args (DistributedDatalogToHardwareCompiler.add_arg_edges (var_expr w) g seen)
             (map.put seen w tt) w Hb').
    rewrite add_arg_edges_LVar_nodes, map.get_put_same. discriminate.
  - apply (IH (DistributedDatalogToHardwareCompiler.add_arg_edges (var_expr u) g seen) (map.put seen u tt) w Hb' Hin).
Qed.

(* Bare: a fact's collected variables are exactly its [var_expr] arguments. *)
Lemma bare_in_collect_args (args : list (@HardwareProgram.lowered_expr var)) (w : var) :
  Forall (fun e => exists u, e = var_expr u) args ->
  (In w (flat_map DistributedDatalogToHardwareCompiler.collect_vars_expr args) <-> In (var_expr w) args).
Proof.
  induction args as [|a args IH]; intros Hb; simpl; [reflexivity|].
  inversion Hb as [|x l [u ->] Hb']; subst. simpl. rewrite (IH Hb'). split.
  - intros [<- | Hin]; [left; reflexivity | right; exact Hin].
  - intros [Heq | Hin]; [injection Heq as ->; left; reflexivity | right; exact Hin].
Qed.

Lemma add_hyp_edges_mono (h : lowered_fact) (g : var_graph) (w : var) :
  Forall (fun e => exists u, e = var_expr u) h.(Datalog.clause_args) ->
  map.get g.(nodes) w <> None ->
  map.get (DistributedDatalogToHardwareCompiler.add_hyp_edges h g).(nodes) w <> None.
Proof. unfold DistributedDatalogToHardwareCompiler.add_hyp_edges. intros. apply add_args_edges_mono; assumption. Qed.

Lemma add_hyp_edges_covers (h : lowered_fact) (g : var_graph) (w : var) :
  Forall (fun e => exists u, e = var_expr u) h.(Datalog.clause_args) ->
  In w (collect_vars_fact h) ->
  map.get (DistributedDatalogToHardwareCompiler.add_hyp_edges h g).(nodes) w <> None.
Proof.
  unfold DistributedDatalogToHardwareCompiler.add_hyp_edges, DistributedDatalogToHardwareCompiler.collect_vars_fact. intros Hb Hin.
  apply add_args_edges_covers; [exact Hb | apply (bare_in_collect_args h.(Datalog.clause_args) w Hb); exact Hin].
Qed.

(* The whole dependency graph: every collected hypothesis variable is a node. *)
Lemma create_dep_graph_covers (hyps : list lowered_fact) :
  Forall (fun h => Forall (fun e => exists u, e = var_expr u) h.(Datalog.clause_args)) hyps ->
  forall w, In w (collect_vars_hyps hyps) ->
  map.get (DistributedDatalogToHardwareCompiler.create_dependency_graph hyps).(nodes) w <> None.
Proof.
  unfold DistributedDatalogToHardwareCompiler.create_dependency_graph, DistributedDatalogToHardwareCompiler.collect_vars_hyps.
  (* generalize the initial accumulator graph *)
  assert (Hgen : forall (hs : list lowered_fact) (g : var_graph) w,
            Forall (fun h => Forall (fun e => exists u, e = var_expr u) h.(Datalog.clause_args)) hs ->
            (In w (flat_map collect_vars_fact hs) \/ map.get g.(nodes) w <> None) ->
            map.get (fold_left (fun acc h => DistributedDatalogToHardwareCompiler.add_hyp_edges h acc) hs g).(nodes) w
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
  intros Hb w Hin. apply (Hgen hyps DistributedDatalogToHardwareCompiler.empty_var_graph w Hb). left. exact Hin.
Qed.

(*----assembly: the produced ordering is NoDup and exactly the hypothesis variables----*)

Lemma length_filter_le {A} (f : A -> bool) (l : list A) : length (filter f l) <= length l.
Proof. induction l as [|x l IH]; simpl; [lia | destruct (f x); simpl; lia]. Qed.

Notation compute_variable_ordering_ordered :=
  (@DistributedDatalogToHardwareCompiler.compute_variable_ordering_ordered var var_node_set var_edge_set).
Notation create_dependency_graph :=
  (@DistributedDatalogToHardwareCompiler.create_dependency_graph var var_node_set var_edge_set).
Notation initial_ordering_context :=
  (@DistributedDatalogToHardwareCompiler.initial_ordering_context var var_node_set var_edge_set).

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
  unfold DistributedDatalogToHardwareCompiler.compute_variable_ordering_ordered. cbv zeta.
  set (g := create_dependency_graph hyps).
  set (cs := DistributedDatalogToHardwareCompiler.hyp_var_order hyps).
  assert (HcandIn : forall v, In v cs <-> In v (collect_vars_hyps hyps)).
  { intros v. unfold cs, DistributedDatalogToHardwareCompiler.hyp_var_order. rewrite dedup_in, map.get_empty.
    split; [intros [H _]; exact H | intros H; split; [exact H | reflexivity]]. }
  assert (Hcs : NoDup cs) by (unfold cs, DistributedDatalogToHardwareCompiler.hyp_var_order; apply dedup_NoDup).
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

Context {rel : relT} {var : exprvarT} {fn : fnT} {aggregator : aggregatorT}.
Context {var_eqb : Eqb var} {var_eqb_ok : Eqb_ok var_eqb}.
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
  (@DistributedDatalogToHardwareCompiler.global_context rel node_id node_id_set rel_dependency_map rel_relid_map).
Notation node_context := (@DistributedDatalogToHardwareCompiler.node_context node_id).
Notation lowered_rule := (@HardwareProgram.lowered_rule var aggregator).
Notation lowered_program := (@HardwareProgram.lowered_program var aggregator).
Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).
Notation compile_rule :=
  (@DistributedDatalogToHardwareCompiler.compile_rule rel var aggregator var_eqb node_id node_id_set rel_dependency_map rel_relid_map var_node_set var_edge_set var_idx_map).
Notation compile_node :=
  (@DistributedDatalogToHardwareCompiler.compile_node rel var aggregator var_eqb node_id node_id_set forwarding_table rel_dependency_map rel_relid_map var_node_set var_edge_set var_idx_map).

(* [compile_rule] = [compile_hyps] (which threads the trie context) then [compile_concls]
   (which leaves the context untouched), so it preserves [wf_nc] and grows [nctries]. *)
Lemma compile_rule_reg (rule : lowered_rule) (gc : global_context) (nc : node_context)
    (hr : hardware_rule) (nc' : node_context) :
  compile_rule rule gc nc = Success (hr, nc') ->
  wf_nc nc -> wf_nc nc' /\ incl nc.(nctries) nc'.(nctries).
Proof.
  unfold DistributedDatalogToHardwareCompiler.compile_rule. intros H Hwf.
  destruct rule as [rconcls rhyps | rconcls rhyps | cr ag hyp_rel];
    cbv zeta in H; [| discriminate | discriminate].
  match type of H with
  | context [DistributedDatalogToHardwareCompiler.compile_hyps ?a ?b ?c ?d ?e] =>
      destruct (DistributedDatalogToHardwareCompiler.compile_hyps a b c d e) as [q nc''] eqn:Hch
  end.
  cbn beta iota zeta in H.
  match type of H with
  | context [DistributedDatalogToHardwareCompiler.compile_concls ?a ?b ?c] =>
      destruct (DistributedDatalogToHardwareCompiler.compile_concls a b c) as [concls|] eqn:Hcc
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
  unfold DistributedDatalogToHardwareCompiler.compile_node. intros H.
  match type of H with
  | context [fold_left ?F prog ?init] =>
      destruct (fold_left F prog init) as [[rules nc1]|] eqn:Hfold
  end; cbn beta iota zeta in H; [|discriminate].
  injection H as <-.
  assert (Hwf0 : wf_nc (DistributedDatalogToHardwareCompiler.initial_node_context node))
    by (split; [intros t [] | constructor]).
  destruct (compile_node_fold_wf gc prog [] (DistributedDatalogToHardwareCompiler.initial_node_context node) rules nc1
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

Context {rel : relT} {var : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
Context {var_eqb : Eqb var} {var_eqb_ok : Eqb_ok var_eqb}.
Context `{sig : signature nat aggregator T}.
Context {context : map.map var T} {context_ok : map.ok context}.
Context {var_idx_map : map.map var nat} {var_idx_map_ok : map.ok var_idx_map}.
Context {var_node_set : map.map var unit} {var_node_set_ok : map.ok var_node_set}.
Context {var_edge_set : map.map var var_node_set}.
Context {node_id : Type}
        {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.
Context {node_id_set : map.map node_id unit}.
Context {forwarding_table : map.map rel_id (list (@DistributedHardwareProgram.destination node_id))}.
Context {rel_dependency_map : map.map rel_id node_id_set}.
Context {fn_id_map : map.map fn fn_id}.
Context {rel_relid_map : map.map rel rel_id}.

Notation global_context :=
  (@DistributedDatalogToHardwareCompiler.global_context rel node_id node_id_set rel_dependency_map rel_relid_map).
Notation node_context := (@DistributedDatalogToHardwareCompiler.node_context node_id).
Notation lowered_rule := (@HardwareProgram.lowered_rule var aggregator).
Notation lowered_program := (@HardwareProgram.lowered_program var aggregator).
Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).
Notation lowered_fact := (@HardwareProgram.lowered_fact var).
Notation compile_rule :=
  (@DistributedDatalogToHardwareCompiler.compile_rule rel var aggregator var_eqb node_id node_id_set rel_dependency_map rel_relid_map var_node_set var_edge_set var_idx_map).
Notation compile_node :=
  (@DistributedDatalogToHardwareCompiler.compile_node rel var aggregator var_eqb node_id node_id_set forwarding_table rel_dependency_map rel_relid_map var_node_set var_edge_set var_idx_map).

(* PER-RULE: a compiled rule (whose post-context tries are all in the node table [tries], which
   has unique ids) matches its lowered datalog rule -- by discharging every hypothesis of
   [hw_rule_correct] from the ordering / hypothesis / conclusion / registration lemmas. *)
Lemma compile_rule_matches (rule : lowered_rule) (gc : global_context) (nc nc' : node_context)
    (hr : hardware_rule) (tries : list trie)
    (env : list (Datalog.fact (rel := rel_id)) -> rel_id -> list T -> Prop) :
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
  unfold DistributedDatalogToHardwareCompiler.compile_rule in H. cbv zeta in H.
  set (ord := compute_variable_ordering_ordered (create_dependency_graph rhyps) rhyps) in *.
  match type of H with
  | context [DistributedDatalogToHardwareCompiler.compile_hyps ?a ?b ?c ?d ?e] =>
      destruct (DistributedDatalogToHardwareCompiler.compile_hyps a b c d e) as [q nc''] eqn:Hch
  end.
  cbn beta iota zeta in H.
  match type of H with
  | context [DistributedDatalogToHardwareCompiler.compile_concls ?a ?b ?c] =>
      destruct (DistributedDatalogToHardwareCompiler.compile_concls a b c) as [concls|] eqn:Hcc
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
    (env : list (Datalog.fact (rel := rel_id)) -> rel_id -> list T -> Prop) :
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
    (env : list (Datalog.fact (rel := rel_id)) -> rel_id -> list T -> Prop) :
  Forall2 (fun rule hr => hw_rule_matches tries env rule hr) prog hrs ->
  Forall2 (hw_rule_matches tries env) (prog) hrs.
Proof. intros HF. induction HF; simpl; constructor; assumption. Qed.

(* Per node: every compiled hardware rule matches its source rule against the node's trie table.
   This is exactly the per-node condition [ninfos_node_rules_match] needs. *)
Lemma compile_node_matches (node : node_id) (prog : lowered_program) (gc : global_context)
    (ninfo : node_info) (env : list (Datalog.fact (rel := rel_id)) -> rel_id -> list T -> Prop) :
  Forall bare_rule prog ->
  compile_node node prog gc = Success ninfo ->
  Forall2 (hw_rule_matches ninfo.(ntries) env) (prog) ninfo.(nprogram).
Proof.
  intros Hbare H.
  pose proof (compile_node_wf node prog gc ninfo H) as Hndt.
  unfold DistributedDatalogToHardwareCompiler.compile_node in H.
  match type of H with
  | context [fold_left ?F prog ?init] =>
      destruct (fold_left F prog init) as [[compiled_rev nc_final]|] eqn:Hfold
  end; cbn beta iota zeta in H; [|discriminate].
  injection H as <-.
  assert (Hwf0 : wf_nc (DistributedDatalogToHardwareCompiler.initial_node_context node))
    by (split; [intros t [] | constructor]).
  assert (Hincl : incl nc_final.(nctries) (rev nc_final.(nctries)))
    by (intros t Ht; rewrite <- in_rev; exact Ht).
  cbn [DistributedHardwareProgram.ntries] in Hndt, Hincl |- *.
  cbn [DistributedHardwareProgram.nprogram].
  destruct (compile_node_fold_matches gc (rev nc_final.(nctries)) prog env []
              (DistributedDatalogToHardwareCompiler.initial_node_context node) compiled_rev nc_final
              Hfold Hbare Hwf0 Hincl Hndt) as [hrs [Hcomp HF]].
  rewrite Hcomp, app_nil_r, rev_involutive.
  apply Forall2_map_lrule. exact HF.
Qed.

End NodeCorrect.

(*============================================================================*)
(*  Top-level [compile]: bridging its output back to per-node [compile_node].   *)
(*============================================================================*)

Section CompileTop.

Import ResultMonadNotations.
Open Scope result_monad_scope.

Context {rel : relT} {var : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
Context {var_eqb : Eqb var} {var_eqb_ok : Eqb_ok var_eqb}.
Context `{sig : signature nat aggregator T}.
Context {context : map.map var T} {context_ok : map.ok context}.
Context {var_idx_map : map.map var nat} {var_idx_map_ok : map.ok var_idx_map}.
Context {var_node_set : map.map var unit} {var_node_set_ok : map.ok var_node_set}.
Context {var_edge_set : map.map var var_node_set}.
Context {node_id : Type}
        {node_id_eqb : Eqb node_id} {node_id_eqb_spec : Eqb_ok node_id_eqb}.
Context {rule_eqb : Eqb rule} {rule_eqb_ok : Eqb_ok rule_eqb}.
Context {node_id_set : map.map node_id unit}.
Context {node_id_edge_set : map.map node_id node_id_set}.
Context {forwarding_table : map.map rel_id (list (@DistributedHardwareProgram.destination node_id))}.
Context {rel_dependency_map : map.map rel_id node_id_set}.
Context (fn_to_id : fn -> fn_id).
Context {rel_relid_map : map.map rel rel_id}.
Context {layout_map : map.map node_id (@HardwareProgram.program rel var fn aggregator)}
        {layout_map_ok : map.ok layout_map}.
Context {lowered_layout_map : map.map node_id (@HardwareProgram.lowered_program var aggregator)}
        {lowered_layout_map_ok : map.ok lowered_layout_map}.
Context {node_ftable_map : map.map node_id forwarding_table}.
Context {fact_locations_map : map.map rel (list node_id)}
        {fact_locations_map_ok : map.ok fact_locations_map}.
Context {lowered_fact_locations_map : map.map rel_id (list node_id)}
        {lowered_fact_locations_map_ok : map.ok lowered_fact_locations_map}.

Notation program := (@HardwareProgram.program rel var fn aggregator).
Notation lowered_program := (@HardwareProgram.lowered_program var aggregator).
Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).
Notation global_context :=
  (@DistributedDatalogToHardwareCompiler.global_context rel node_id node_id_set rel_dependency_map rel_relid_map).
Notation compile_node :=
  (@DistributedDatalogToHardwareCompiler.compile_node rel var aggregator var_eqb node_id node_id_set forwarding_table rel_dependency_map rel_relid_map var_node_set var_edge_set var_idx_map).
Notation compile_all_nodes :=
  (@DistributedDatalogToHardwareCompiler.compile_all_nodes rel var aggregator var_eqb node_id node_id_set forwarding_table rel_dependency_map rel_relid_map lowered_layout_map var_node_set var_edge_set var_idx_map).
Notation attach_forwarding_tables :=
  (@DistributedDatalogToHardwareCompiler.attach_forwarding_tables node_id node_id_eqb forwarding_table node_ftable_map).
Notation global_rename_program :=
  (@DistributedDatalogToHardwareCompiler.global_rename_program rel var fn aggregator node_id node_id_set rel_dependency_map rel_relid_map fn_to_id).
Notation global_rename_rule_layout :=
  (@DistributedDatalogToHardwareCompiler.global_rename_rule_layout rel var fn aggregator node_id node_id_set rel_dependency_map rel_relid_map layout_map lowered_layout_map fn_to_id).
Notation fact_locations := (@DistributedDatalogToHardwareCompiler.fact_locations rel node_id fact_locations_map).
Notation lowered_fact_locations := (@DistributedDatalogToHardwareCompiler.lowered_fact_locations node_id lowered_fact_locations_map).
Notation node_graph := (@DistributedDatalogToHardwareCompiler.node_graph node_id node_id_set node_id_edge_set).
Notation collect_global_names_layout :=
  (@DistributedDatalogToHardwareCompiler.collect_global_names_layout rel var fn aggregator node_id node_id_set rel_dependency_map rel_relid_map layout_map).
Notation initial_global_context :=
  (@DistributedDatalogToHardwareCompiler.initial_global_context rel node_id node_id_set rel_dependency_map rel_relid_map).
Notation compile :=
  (@DistributedDatalogToHardwareCompiler.compile rel var fn aggregator var_eqb node_id node_id_eqb node_id_set forwarding_table rel_dependency_map rel_relid_map layout_map lowered_layout_map fact_locations_map lowered_fact_locations_map var_node_set var_edge_set node_id_edge_set fn_to_id var_idx_map node_ftable_map).
Notation lower_inputs :=
  (@DistributedDatalogToHardwareCompiler.lower_inputs rel var fn aggregator node_id node_id_set rel_dependency_map rel_relid_map layout_map lowered_layout_map fact_locations_map lowered_fact_locations_map fn_to_id).
Notation compile_lowered :=
  (@DistributedDatalogToHardwareCompiler.compile_lowered rel var aggregator var_eqb node_id node_id_eqb node_id_set forwarding_table rel_dependency_map rel_relid_map lowered_layout_map lowered_fact_locations_map var_node_set var_edge_set node_id_edge_set var_idx_map node_ftable_map).
Notation DNet := (@DistributedDatalog.DataflowNetwork rel_id var nat aggregator T node_id).

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
  intros H Hin. unfold DistributedDatalogToHardwareCompiler.compile_all_nodes in H.
  match type of H with
  | context [map.fold ?F ?r0 llayout] => destruct (map.fold F r0 llayout) as [l|] eqn:Hfold
  end; cbn beta iota in H; [|discriminate].
  injection H as ->.
  apply (map_fold_result_in (fun node v => compile_node node v gc) llayout ninfos Hfold ninfo Hin).
Qed.

(* The lowered program assigned to a node is the global-rename of the original program there. *)
Lemma global_rename_rule_layout_spec (layout : layout_map) (gc : global_context)
    (llayout : lowered_layout_map) (node : node_id) (lprog : lowered_program) :
  global_rename_rule_layout layout gc = Success llayout ->
  map.get llayout node = Some lprog ->
  exists orig, map.get layout node = Some orig /\ global_rename_program orig gc = Success lprog.
Proof.
  intros H Hget. unfold DistributedDatalogToHardwareCompiler.global_rename_rule_layout in H.
  destruct (map.try_map_values_bw _ layout llayout H node lprog Hget) as [orig [Hgrp Hgetl]].
  exists orig. split; assumption.
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
    destruct (eqb_boolspec _ k node) as [->|Hne].
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
  intros H Hget. unfold DistributedDatalogToHardwareCompiler.compile_all_nodes in H.
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

Notation lprog_of := (@DistributedDatalogToHardwareCompiler.lprog_of var aggregator node_id lowered_layout_map).

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

(*----Reading the network back off the returned [ninfos]----*)

(* [compile_node] always stamps the result with the node it was given. *)
Lemma compile_node_nid (node : node_id) (prog : lowered_program) (gc : global_context) (ni : node_info) :
  compile_node node prog gc = Success ni -> ni.(nid) = node.
Proof.
  unfold DistributedDatalogToHardwareCompiler.compile_node.
  destruct (fold_left _ prog _) as [[compiled_rules ncontext]|] eqn:Hf; cbn beta iota; [|discriminate].
  intros H. injection H as <-. reflexivity.
Qed.

(* Forward direction of [map_fold_result_in]: each source key's result is in the collected list. *)
Lemma map_fold_result_in_fwd {V W : Type} {M : map.map node_id V} {Mok : map.ok M}
    (g : node_id -> V -> result W) (m0 : M) (ll : list W) (node : node_id) (v : V) :
  map.fold (fun acc nd v0 => acc' <- acc ;; w <- g nd v0 ;; Success (w :: acc')%list)
           (Success []) m0 = Success ll ->
  map.get m0 node = Some v ->
  exists w, g node v = Success w /\ In w ll.
Proof.
  revert ll.
  apply (map.fold_spec
    (fun (m : M) (acc : result (list W)) =>
       forall ll, acc = Success ll -> map.get m node = Some v ->
         exists w, g node v = Success w /\ In w ll)).
  - intros ll Hll Hget. rewrite map.get_empty in Hget. discriminate.
  - intros k val m r Hgmk Hr ll Hll Hget. cbn beta iota in Hll.
    destruct r as [rl|]; cbn beta iota in Hll; [|discriminate].
    destruct (g k val) as [w0|] eqn:Hgk; cbn beta iota in Hll; [|discriminate].
    injection Hll as <-.
    destruct (eqb_boolspec _ node k) as [->|Hne].
    + rewrite map.get_put_same in Hget. injection Hget as <-.
      exists w0. split; [exact Hgk | left; reflexivity].
    + rewrite (map.get_put_diff m node val k) in Hget by congruence.
      destruct (Hr rl eq_refl Hget) as [w [Hgnv Hin]].
      exists w. split; [exact Hgnv | right; exact Hin].
Qed.

(* Every node the lowered layout assigns to has its [compile_node] result in [compile_all_nodes]. *)
Lemma compile_all_nodes_in_fwd (llayout : lowered_layout_map) (gc : global_context)
    (ninfos : list node_info) (node : node_id) (lprog : lowered_program) :
  compile_all_nodes llayout gc = Success ninfos ->
  map.get llayout node = Some lprog ->
  exists ninfo, compile_node node lprog gc = Success ninfo /\ In ninfo ninfos.
Proof.
  intros H Hget. unfold DistributedDatalogToHardwareCompiler.compile_all_nodes in H.
  match type of H with
  | context [map.fold ?F ?r0 llayout] => destruct (map.fold F r0 llayout) as [l|] eqn:Hfold
  end; cbn beta iota in H; [|discriminate].
  injection H as ->.
  apply (map_fold_result_in_fwd (fun nd v => compile_node nd v gc) llayout ninfos node lprog Hfold Hget).
Qed.

(* The per-node info read off the returned [ninfos] (empty default if the node is absent). *)
Definition find_ninfo (ninfos : list node_info) (n : node_id) : node_info :=
  match List.find (fun ni => eqb ni.(nid) n) ninfos with
  | Some ni => ni
  | None => {| nid := n; nprogram := []; nforwarding := map.empty; ntries := [] |}
  end.

(* Each entry of the (all-node) attached list is either a layout node (same id/tries/program as its
   [compile_all_nodes] info) or a forwarding-only node (empty program/tries, id not in [ninfos0]). *)
Lemma attach_in_data (ninfos0 : list node_info) (ft : node_ftable_map) (x : node_info) :
  In x (attach_forwarding_tables ninfos0 ft) ->
  (exists ni0, In ni0 ninfos0 /\ x.(nid) = ni0.(nid)
     /\ x.(ntries) = ni0.(ntries) /\ x.(nprogram) = ni0.(nprogram))
  \/ (x.(nprogram) = [] /\ x.(ntries) = [] /\ (forall ni0, In ni0 ninfos0 -> ni0.(nid) <> x.(nid))).
Proof.
  unfold DistributedDatalogToHardwareCompiler.attach_forwarding_tables.
  rewrite in_app_iff. intros [Hin | Hin].
  - apply in_map_iff in Hin. destruct Hin as [ni0 [Heq Hin0]]. subst x. cbn.
    left. exists ni0. repeat split; [exact Hin0 | reflexivity..].
  - apply in_map_iff in Hin. destruct Hin as [n' [Heq Hn']]. subst x. cbn.
    right. split; [reflexivity | split; [reflexivity|]].
    apply filter_In in Hn'. destruct Hn' as [_ Hfilt]. apply Bool.negb_true_iff in Hfilt.
    intros ni0 Hin0 Hnid.
    assert (Hex : List.existsb (fun ni => eqb ni.(nid) n') ninfos0 = true).
    { apply existsb_exists. exists ni0. split; [exact Hin0|].
      rewrite Hnid. destruct (eqb_boolspec _ n' n'); congruence. }
    rewrite Hex in Hfilt. discriminate.
Qed.

(* KEY: the tries/program read off the returned [ninfos] for node [n] are exactly what [compile_node]
   produces for [n] -- i.e. pointwise equal to [compiled_hn]'s recompute.  (Forwarding is handled
   separately.)  This lets the network read off [ninfos] reuse the [compiled_hn] correctness. *)
Lemma find_ninfo_node (llayout : lowered_layout_map) (gc : global_context)
    (ninfos0 : list node_info) (ft : node_ftable_map) (n : node_id) :
  compile_all_nodes llayout gc = Success ninfos0 ->
  (find_ninfo (attach_forwarding_tables ninfos0 ft) n).(ntries)
    = match compile_node n (lprog_of llayout n) gc with Success ni => ni.(ntries) | Failure _ => [] end
  /\ (find_ninfo (attach_forwarding_tables ninfos0 ft) n).(nprogram)
    = match compile_node n (lprog_of llayout n) gc with Success ni => ni.(nprogram) | Failure _ => [] end.
Proof.
  intros Hcan. unfold find_ninfo.
  destruct (List.find (fun ni => eqb ni.(nid) n) (attach_forwarding_tables ninfos0 ft))
    as [x|] eqn:Hfind.
  - apply List.find_some in Hfind. destruct Hfind as [Hxin Hxnid].
    destruct (eqb_boolspec _ x.(nid) n) as [Hxn|]; [|discriminate].
    destruct (attach_in_data ninfos0 ft x Hxin) as [[ni0' [Hin0' [Hnid' [Htr' Hpr']]]] | [Hpr [Htr Hno]]].
    + (* layout node: x's data = ni0' = compile_node n (lprog_of llayout n) gc *)
      destruct (compile_all_nodes_in llayout gc ninfos0 ni0' Hcan Hin0')
        as [node'' [lprog'' [Hgnode'' Hcn'']]].
      assert (Hnidni0 : ni0'.(nid) = node'') by exact (compile_node_nid node'' lprog'' gc ni0' Hcn'').
      assert (Hn2 : node'' = n) by (rewrite <- Hnidni0, <- Hnid'; exact Hxn).
      rewrite Hn2 in Hgnode'', Hcn''.
      unfold lprog_of. rewrite Hgnode'', Hcn''.
      rewrite Htr', Hpr'. split; reflexivity.
    + (* forwarding-only: no layout node with id n, so lprog_of llayout n = [] *)
      assert (Hgn : map.get llayout n = None).
      { destruct (map.get llayout n) as [lprog|] eqn:Hg; [|reflexivity].
        destruct (compile_all_nodes_in_fwd llayout gc ninfos0 n lprog Hcan Hg) as [ni0 [Hcn Hin0]].
        exfalso. apply (Hno ni0 Hin0).
        rewrite (compile_node_nid n lprog gc ni0 Hcn), Hxn. reflexivity. }
      unfold lprog_of. rewrite Hgn. rewrite compile_node_nil. cbn.
      rewrite Hpr, Htr. split; reflexivity.
  - (* find = None: no entry with id n, so n is not a layout node either *)
    assert (Hgn : map.get llayout n = None).
    { destruct (map.get llayout n) as [lprog|] eqn:Hg; [|reflexivity].
      destruct (compile_all_nodes_in_fwd llayout gc ninfos0 n lprog Hcan Hg) as [ni0 [Hcn Hin0]].
      assert (Hin : In {| nid := ni0.(nid); nprogram := ni0.(nprogram);
                          nforwarding := get_node_ftable ni0.(nid) ft; ntries := ni0.(ntries) |}
                       (attach_forwarding_tables ninfos0 ft)).
      { unfold DistributedDatalogToHardwareCompiler.attach_forwarding_tables. rewrite in_app_iff.
        left. apply in_map_iff. exists ni0. split; [reflexivity | exact Hin0]. }
      pose proof (List.find_none _ _ Hfind _ Hin) as Hfn. cbn in Hfn.
      rewrite (compile_node_nid n lprog gc ni0 Hcn) in Hfn.
      destruct (eqb_boolspec _ n n); congruence. }
    cbn. unfold lprog_of. rewrite Hgn. rewrite compile_node_nil. cbn. split; reflexivity.
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

(* Boolean version of [bare_fact]: every argument is a plain variable.  PARAMETRIC over the relation
   and function types -- bareness inspects only [var_expr]/[fun_expr], never the relation/function
   identifiers -- so the SAME check applies to the source layout (over [rel]/[fn]) and the renamed
   lowered layout (over [rel_id]/[fn_id]). *)
Definition bare_factb {Rel Fn} (f : Datalog.clause (rel := Rel) (fn := Fn)) : bool :=
  forallb (fun e => match e with var_expr _ => true | fun_expr _ _ => false end) f.(Datalog.clause_args).

Definition bare_ruleb {Rel Fn} (r : Datalog.rule (rel := Rel) (fn := Fn)) : bool :=
  match r with
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

(* Decidable check that every program in a layout is bare.  PARAMETRIC over the relation/function
   types and the layout-map instance, so it applies to both the source [layout] and the lowered
   [llayout]. *)
Definition bare_layoutb {Rel Fn} {M : map.map node_id (list (Datalog.rule (rel := Rel) (fn := Fn)))}
    (lay : M) : bool :=
  map.fold (fun acc _ p => acc && forallb bare_ruleb p) true lay.

Lemma bare_layoutb_entry {Rel Fn} {M : map.map node_id (list (Datalog.rule (rel := Rel) (fn := Fn)))}
    {M_ok : map.ok M} (lay : M) :
  bare_layoutb lay = true ->
  forall n p, map.get lay n = Some p -> forallb bare_ruleb p = true.
Proof.
  unfold bare_layoutb.
  apply (map.fold_spec
    (fun (m : M) (b : bool) =>
       b = true -> forall n p, map.get m n = Some p -> forallb bare_ruleb p = true)).
  - intros _ n p Hget. rewrite map.get_empty in Hget. discriminate.
  - intros k v m r Hgmk IH Hb n p Hget.
    apply andb_true_iff in Hb. destruct Hb as [Hr Hv].
    destruct (eqb_boolspec _ n k) as [->|Hne].
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

(*============================================================================*)
(*  Phase C (soundness): the compiler's OWN generated forwarding table only     *)
(*  ever routes a relation's facts along real edges of the topology [g].        *)
(*  (The extra [map.ok]s the surrounding section does not already carry are      *)
(*   declared here, just before they are first needed.)                          *)
(*============================================================================*)

Context {forwarding_table_ok : map.ok forwarding_table}.
Context {node_ftable_map_ok : map.ok node_ftable_map}.
Context {node_id_set_ok : map.ok node_id_set}.
Context {node_id_edge_set_ok : map.ok node_id_edge_set}.

Notation ftable_edges_sound :=
  (@ForwardingCorrect.ftable_edges_sound node_id node_id_set node_id_edge_set forwarding_table node_ftable_map).
Notation generate_forwarding_table :=
  (@DistributedDatalogToHardwareCompiler.generate_forwarding_table rel node_id node_id_eqb node_id_set forwarding_table rel_dependency_map rel_relid_map node_id_edge_set node_ftable_map).
Notation update_forwarding_table_for_rel :=
  (@DistributedDatalogToHardwareCompiler.update_forwarding_table_for_rel rel node_id node_id_eqb node_id_set forwarding_table rel_dependency_map rel_relid_map node_id_edge_set node_ftable_map).

(* one relation's worth of routing keeps the table edge-sound: every producer/consumer pair is
   joined either by trie destinations (no edges) or along a [get_path], which [get_path_spec]
   certifies is a genuine edge-walk. *)
Lemma update_rel_pres_sound (g : node_graph) (rel0 : rel_id) (gcontext : global_context)
    (ninfos : list node_info) (ftables : node_ftable_map) :
  ftable_edges_sound g ftables ->
  ftable_edges_sound g (update_forwarding_table_for_rel rel0 gcontext ninfos ftables g).
Proof.
  intros Hsound. unfold DistributedDatalogToHardwareCompiler.update_forwarding_table_for_rel.
  apply (ForwardingCorrect.map_fold_pres_sound (M := node_id_set) (Mok := node_id_set_ok) g).
  - exact Hsound.
  - intros ft producer _ Hft.
    apply (ForwardingCorrect.map_fold_pres_sound (M := node_id_set) (Mok := node_id_set_ok) g).
    + exact Hft.
    + intros ft' consumer _ Hft'.
      destruct (eqb_boolspec _ producer consumer).
      * apply ForwardingCorrect.add_trie_pres_sound. exact Hft'.
      * destruct (ComputableGraph.get_path (node_eqb := node_id_eqb) (node_set := node_id_set)
                    (edge_set := node_id_edge_set) g producer consumer ) as [path|] eqn:Hpath.
        -- eapply ForwardingCorrect.add_path_pres_sound; [| exact Hft'].
           eapply ComputableGraph.get_path_spec. exact Hpath.
        -- exact Hft'.
Qed.

(* the whole table, folded over all relation ids from the empty table, is edge-sound. *)
Lemma generate_forwarding_table_sound (g : node_graph) (gcontext : global_context)
    (ninfos : list node_info) :
  ftable_edges_sound g (generate_forwarding_table gcontext ninfos g ).
Proof.
  unfold DistributedDatalogToHardwareCompiler.generate_forwarding_table.
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
  (@DistributedDatalogToHardwareCompiler.get_rel_ids rel node_id node_id_set rel_dependency_map rel_relid_map).
Notation add_trie_dest :=
  (@DistributedDatalogToHardwareCompiler.add_trie_dest_to_forwarding_table node_id node_id_eqb forwarding_table node_ftable_map).
Notation add_path :=
  (@DistributedDatalogToHardwareCompiler.add_path_to_forwarding_table node_id node_id_eqb forwarding_table node_ftable_map).

(* the per-(producer,consumer) cell only adds forwarding edges (any edge relation [r] survives) *)
Lemma fwd_cell_mono (g : node_graph) (rel0 : rel_id) (ninfos : list node_info)
    (producer consumer : node_id) (a b : node_id) (r : rel_id) (ft : node_ftable_map) :
  has_fwd_edge ft a r b ->
  has_fwd_edge
    (if node_id_eqb producer consumer
     then add_trie_dest consumer rel0 ft ninfos
     else match get_path g producer consumer with
          | None => ft
          | Some path => add_path rel0 path ft ninfos
          end) a r b.
Proof.
  intros H. destruct (node_id_eqb producer consumer).
  - apply ForwardingCorrect.add_trie_mono. exact H.
  - destruct (get_path g producer consumer ) as [path|].
    + apply ForwardingCorrect.add_path_mono. exact H.
    + exact H.
Qed.

(* routing one relation only adds forwarding edges *)
Lemma update_rel_mono (g : node_graph) (rel0 : rel_id) (gcontext : global_context)
    (ninfos : list node_info) (a b : node_id) (r : rel_id) (ft : node_ftable_map) :
  has_fwd_edge ft a r b ->
  has_fwd_edge (update_forwarding_table_for_rel rel0 gcontext ninfos ft g) a r b.
Proof.
  intros H. unfold DistributedDatalogToHardwareCompiler.update_forwarding_table_for_rel.
  apply (ForwardingCorrect.map_fold_pres (M := node_id_set) (Mok := node_id_set_ok)
           (fun ft => has_fwd_edge ft a r b)); [exact H|].
  intros ft1 producer _ H1.
  apply (ForwardingCorrect.map_fold_pres (M := node_id_set) (Mok := node_id_set_ok)
           (fun ft => has_fwd_edge ft a r b)); [exact H1|].
  intros ft2 consumer _ H2. apply fwd_cell_mono. exact H2.
Qed.

(* routing relation [rel0] lays every consecutive edge of the path it found from [prod] to [cons] *)
Lemma update_rel_adds (g : node_graph) (rel0 : rel_id) (gcontext : global_context)
    (ninfos : list node_info) (prod cons : node_id) (path : list node_id)
    (producers consumers : node_id_set) (i : nat) (a b : node_id) (ft : node_ftable_map) :
  map.get gcontext.(DistributedDatalogToHardwareCompiler.rel_node_producers) rel0 = Some producers ->
  map.get gcontext.(DistributedDatalogToHardwareCompiler.rel_node_consumers) rel0 = Some consumers ->
  map.get producers prod = Some tt ->
  map.get consumers cons = Some tt ->
  prod <> cons ->
  get_path g prod cons = Some path ->
  nth_error path i = Some a -> nth_error path (S i) = Some b ->
  has_fwd_edge (update_forwarding_table_for_rel rel0 gcontext ninfos ft g) a rel0 b.
Proof.
  intros Hprods Hcons Hprod Hcon Hne Hpath Hi Hib.
  unfold DistributedDatalogToHardwareCompiler.update_forwarding_table_for_rel. rewrite Hprods, Hcons.
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
      destruct (eqb_boolspec _ prod cons) as [Heq|_]; [exfalso; apply Hne; exact Heq|].
      rewrite Hpath. eapply ForwardingCorrect.add_path_adds; [exact Hi | exact Hib].
Qed.

(* MAIN C2 ENGINE: the consecutive forwarding edge survives into the whole generated table. *)
Lemma generate_forwarding_table_adds (g : node_graph) (gcontext : global_context)
    (ninfos : list node_info) (rel0 : rel_id) (prod cons : node_id)
    (path : list node_id) (producers consumers : node_id_set) (i : nat) (a b : node_id) :
  In rel0 (get_rel_ids gcontext) ->
  map.get gcontext.(DistributedDatalogToHardwareCompiler.rel_node_producers) rel0 = Some producers ->
  map.get gcontext.(DistributedDatalogToHardwareCompiler.rel_node_consumers) rel0 = Some consumers ->
  map.get producers prod = Some tt ->
  map.get consumers cons = Some tt ->
  prod <> cons ->
  get_path g prod cons = Some path ->
  nth_error path i = Some a -> nth_error path (S i) = Some b ->
  has_fwd_edge (generate_forwarding_table gcontext ninfos g ) a rel0 b.
Proof.
  intros Hrel Hprods Hcons Hprod Hcon Hne Hpath Hi Hib.
  unfold DistributedDatalogToHardwareCompiler.generate_forwarding_table.
  apply (ForwardingCorrect.fold_left_adds (fun ft => has_fwd_edge ft a rel0 b)
           (fun ftables rel => update_forwarding_table_for_rel rel gcontext ninfos ftables g)
           (get_rel_ids gcontext) map.empty rel0 Hrel).
  - intros acc r H1. apply update_rel_mono. exact H1.
  - intros acc. eapply update_rel_adds; eauto.
Qed.

(* the forwarding function a compiled node exposes for a relation: the [DestEdge] targets
   recorded in its forwarding table.  [In n2 (fwd_list ft n r)] is exactly [has_fwd_edge]. *)
Definition fwd_list (ftables : node_ftable_map) (n : node_id) (r : rel_id) : list node_id :=
  @ForwardingCorrect.dest_edges node_id
    (@ForwardingCorrect.node_rel_dests node_id forwarding_table node_ftable_map ftables n r).

(*----Forwarding read off the returned [ninfos]----*)

(* Every attached node carries the generated forwarding table's entry for its id. *)
Lemma attach_nforwarding (ninfos0 : list node_info) (ft : node_ftable_map) (x : node_info) :
  In x (attach_forwarding_tables ninfos0 ft) ->
  x.(nforwarding) = get_node_ftable x.(nid) ft.
Proof.
  unfold DistributedDatalogToHardwareCompiler.attach_forwarding_tables. rewrite in_app_iff.
  intros [Hin | Hin]; apply in_map_iff in Hin; destruct Hin as [a [Heq _]]; subst x; reflexivity.
Qed.

(* Every node that forwards anything (a key of the generated table) has a node_info in [ninfos]. *)
Lemma ft_key_in_attach (ninfos0 : list node_info) (ft : node_ftable_map) (n : node_id)
    (v : forwarding_table) :
  map.get ft n = Some v ->
  exists x, In x (attach_forwarding_tables ninfos0 ft) /\ x.(nid) = n.
Proof.
  intros Hget. assert (Hkey : In n (map.keys ft)) by exact (map.in_keys ft n v Hget).
  unfold DistributedDatalogToHardwareCompiler.attach_forwarding_tables.
  destruct (List.existsb (fun ni => eqb ni.(nid) n) ninfos0) eqn:Hex.
  - apply existsb_exists in Hex. destruct Hex as [ni0 [Hin0 Heqn]].
    destruct (eqb_boolspec _ ni0.(nid) n) as [Hni0n|]; [|discriminate].
    eexists. split.
    + rewrite in_app_iff. left. apply in_map_iff. exists ni0. split; [reflexivity | exact Hin0].
    + cbn. exact Hni0n.
  - eexists. split.
    + rewrite in_app_iff. right. apply in_map_iff. exists n. split; [reflexivity|].
      apply filter_In. split; [exact Hkey | apply Bool.negb_true_iff; exact Hex].
    + cbn. reflexivity.
Qed.

(* The forwarding table read off [ninfos] for node [n] is exactly the generated table's entry. *)
Lemma find_ninfo_nforwarding (ninfos0 : list node_info) (ft : node_ftable_map) (n : node_id) :
  (find_ninfo (attach_forwarding_tables ninfos0 ft) n).(nforwarding) = get_node_ftable n ft.
Proof.
  unfold find_ninfo.
  destruct (List.find (fun ni => eqb ni.(nid) n) (attach_forwarding_tables ninfos0 ft))
    as [x|] eqn:Hfind.
  - apply List.find_some in Hfind. destruct Hfind as [Hxin Hxnid].
    destruct (eqb_boolspec _ x.(nid) n) as [Hxn|]; [|discriminate].
    rewrite (attach_nforwarding ninfos0 ft x Hxin), Hxn. reflexivity.
  - assert (Hgn : map.get ft n = None).
    { destruct (map.get ft n) as [v|] eqn:Hg; [|reflexivity].
      destruct (ft_key_in_attach ninfos0 ft n v Hg) as [x [Hxin Hxn]].
      pose proof (List.find_none _ _ Hfind x Hxin) as Hfn. cbn in Hfn.
      rewrite Hxn in Hfn. destruct (eqb_boolspec _ n n); congruence. }
    cbn. unfold get_node_ftable. rewrite Hgn. reflexivity.
Qed.

(* The forwarding FUNCTION read off [ninfos]: for node [n], relation [r], the edge destinations its
   own attached forwarding table lists. *)
Definition forward_of_ninfos (ninfos : list node_info) (n : node_id) (r : rel_id) : list node_id :=
  @ForwardingCorrect.dest_edges node_id
    (match map.get (find_ninfo ninfos n).(nforwarding) r with Some ds => ds | None => [] end).

(* It coincides, pointwise, with the [fwd_list] of the generated table. *)
Lemma forward_of_ninfos_eq (ninfos0 : list node_info) (ft : node_ftable_map) (n : node_id) (r : rel_id) :
  forward_of_ninfos (attach_forwarding_tables ninfos0 ft) n r = fwd_list ft n r.
Proof.
  unfold forward_of_ninfos, fwd_list, ForwardingCorrect.node_rel_dests.
  rewrite (find_ninfo_nforwarding ninfos0 ft n). reflexivity.
Qed.

(* [forwarding_reachable] respects pointwise-equal forwarding functions (avoids funext). *)
Lemma forwarding_reachable_ext (f1 f2 : node_id -> rel_id -> list node_id) (r : rel_id) (a b : node_id) :
  (forall n r', f1 n r' = f2 n r') ->
  DistributedDatalog.forwarding_reachable f1 r a b ->
  DistributedDatalog.forwarding_reachable f2 r a b.
Proof.
  intros Hext H. induction H as [n1 n2 Hin | n1 n2 n3 Hin Hr IH].
  - apply DistributedDatalog.fwd_step. rewrite <- (Hext n1 r). exact Hin.
  - apply (DistributedDatalog.fwd_trans f2 r n1 n2 n3); [rewrite <- (Hext n1 r); exact Hin | exact IH].
Qed.

(* [good_source] depends on the forwarding function only through [forwarding_reachable], so it
   transports across two nets that agree on layout/output and have pointwise-equal forwarding. *)
Lemma good_source_forward_ext (net1 net2 : DNet) (n : node_id) (R : rel_id) :
  net1.(DistributedDatalog.layout) = net2.(DistributedDatalog.layout) ->
  net1.(DistributedDatalog.output) = net2.(DistributedDatalog.output) ->
  (forall a r, net1.(DistributedDatalog.forward) a r = net2.(DistributedDatalog.forward) a r) ->
  DistributedDatalog.good_source net1 n R -> DistributedDatalog.good_source net2 n R.
Proof.
  intros Hlay Hout Hfwd [Hcons Hexout]. split.
  - intros n_cons Hncons. rewrite <- Hlay in Hncons. destruct (Hcons n_cons Hncons) as [Heq | Hreach].
    + left; exact Heq.
    + right. exact (forwarding_reachable_ext _ _ R n n_cons Hfwd Hreach).
  - destruct Hexout as [n_out [Hout_o Hreach_o]]. exists n_out. split.
    + rewrite <- Hout. exact Hout_o.
    + destruct Hreach_o as [Heq | Hreach];
        [left; exact Heq | right; exact (forwarding_reachable_ext _ _ R n n_out Hfwd Hreach)].
Qed.

(* [good_network_streaming] transports across two nets agreeing on graph/layout/input/output with
   pointwise-equal forwarding -- the forwarding function only enters via [good_forwarding_sound] and
   [good_source].  This is the bridge that lets the [forward_of_ninfos] network inherit the
   [fwd_list] network's well-formedness (no funext). *)
Lemma good_network_streaming_forward_ext (net1 net2 : DNet)
    (program : list (Datalog.rule (rel := rel_id) (fn := nat))) (Q : Datalog.fact (rel := rel_id) -> Prop) :
  net1.(DistributedDatalog.graph) = net2.(DistributedDatalog.graph) ->
  net1.(DistributedDatalog.layout) = net2.(DistributedDatalog.layout) ->
  net1.(DistributedDatalog.input) = net2.(DistributedDatalog.input) ->
  net1.(DistributedDatalog.output) = net2.(DistributedDatalog.output) ->
  (forall a r, net1.(DistributedDatalog.forward) a r = net2.(DistributedDatalog.forward) a r) ->
  DistributedDatalog.good_network_streaming net1 program Q ->
  DistributedDatalog.good_network_streaming net2 program Q.
Proof.
  intros Hg Hl Hi Ho Hf (Hgg & Hlay & Hfwd & Hprod & Hin).
  unfold DistributedDatalog.good_network_streaming.
  split; [rewrite <- Hg; exact Hgg|].
  split; [rewrite <- Hg, <- Hl; exact Hlay|].
  split.
  - unfold DistributedDatalog.good_forwarding_sound. intros n1 n2 r Hin2.
    rewrite <- Hf in Hin2. destruct (Hfwd n1 n2 r Hin2) as (H1 & H2 & He).
    rewrite <- Hg. split; [exact H1 | split; [exact H2 | exact He]].
  - split.
    + intros n_prod R Hprodu. rewrite <- Hl in Hprodu.
      exact (good_source_forward_ext net1 net2 n_prod R Hl Ho Hf (Hprod n_prod R Hprodu)).
    + unfold DistributedDatalog.good_input_streaming. destruct Hin as [HinQ Hinj]. split.
      * intros n f. rewrite <- Hi. exact (HinQ n f).
      * intros f HQf. destruct (Hinj f HQf) as [n [Hinf Hgs]]. exists n. split.
        -- rewrite <- Hi. exact Hinf.
        -- exact (good_source_forward_ext net1 net2 n (Datalog.rel_of f) Hl Ho Hf Hgs).
Qed.

(* PACKAGED C2 RESULT: whenever the compiler found (and laid) a path from a producer of [rel0]
   to a consumer of [rel0] (i.e. [get_path] returned [Some] — a computable, checkable fact), the
   final generated forwarding table makes that consumer forwarding-reachable from the producer.
   Composes [get_path_spec] (the path is real) + [generate_forwarding_table_adds] (its edges
   survive) + [forwarding_chain_reachable] (a forwarding walk is a reachability chain). *)
Lemma generate_forwarding_reachable (g : node_graph) (gcontext : global_context)
    (ninfos : list node_info) (rel0 : rel_id) (prod cons : node_id)
    (path : list node_id) (producers consumers : node_id_set) :
  In rel0 (get_rel_ids gcontext) ->
  map.get gcontext.(DistributedDatalogToHardwareCompiler.rel_node_producers) rel0 = Some producers ->
  map.get gcontext.(DistributedDatalogToHardwareCompiler.rel_node_consumers) rel0 = Some consumers ->
  map.get producers prod = Some tt ->
  map.get consumers cons = Some tt ->
  prod <> cons ->
  get_path g prod cons = Some path ->
  @DistributedDatalog.forwarding_reachable rel_id node_id
    (fwd_list (generate_forwarding_table gcontext ninfos g )) rel0 prod cons.
Proof.
  intros Hrel Hprods Hcons Hprod Hcon Hne Hpath.
  destruct (@ComputableGraph.get_path_spec node_id node_id_eqb node_id_eqb_spec node_id_set
              node_id_set_ok node_id_edge_set g prod cons path Hpath)
    as [_ [Hhd [Hlast _]]].
  set (FT := generate_forwarding_table gcontext ninfos g ).
  assert (Hchain : forall i x y, nth_error path i = Some x -> nth_error path (S i) = Some y ->
                     In y (fwd_list FT x rel0)).
  { intros i x y Hx Hy. unfold fwd_list.
    exact (generate_forwarding_table_adds g gcontext ninfos rel0 prod cons path producers
             consumers i x y Hrel Hprods Hcons Hprod Hcon Hne Hpath Hx Hy). }
  destruct (@DistributedDatalog.forwarding_chain_reachable rel_id node_id
              (fwd_list FT) rel0 path prod cons Hchain Hhd Hlast) as [Heq | Hreach].
  - exfalso. apply Hne. exact Heq.
  - exact Hreach.
Qed.

Notation cg2g := (@ComputableGraph.computable_graph_to_graph node_id node_id_set node_id_edge_set).

(*============================================================================*)
(*  Bridge to the REFERENCE single-program semantics [Datalog.prog_impl]        *)
(*============================================================================*)

(* For a bare (normal) rule, [rule_impl] can only produce a normal fact (the [meta_rule_impl]
   constructor needs a [meta_rule]). *)
Lemma bare_rule_impl_normal (env : list (Datalog.fact (rel := rel_id)) -> rel_id -> list T -> Prop)
    (r : Datalog.rule (rel := rel_id) (fn := nat)) (f : Datalog.fact (rel := rel_id))
    (hyps : list (Datalog.fact (rel := rel_id))) :
  bare_rule r -> Datalog.rule_impl env r f hyps -> exists R args, f = Datalog.normal_fact R args.
Proof.
  intros Hbare H. destruct r as [concls hyps0 | concls hyps0 | concl agg hyp];
    [|cbn in Hbare; contradiction..].
  inversion H; subst. eexists; eexists; reflexivity.
Qed.

(*----Per-rule bridges between the hardware/datalog/network firing relations (copied from the
     retired declarative bridge; these are the only pieces of it the operational proof needs)----*)

(* A trie-join always concludes a [normal_fact] (it projects a binding through [join_output_fact]). *)
Lemma hw_rule_impl_concl_normal (tries : list trie) hr (f : Datalog.fact (rel := rel_id)) hyps' :
  hw_rule_impl tries hr f hyps' -> exists R args, f = Datalog.normal_fact R args.
Proof.
  intros [_ [vals [_ [jo [_ Hjo]]]]].
  unfold join_output_fact in Hjo.
  destruct (fold_right _ _ _) as [out|]; [|discriminate].
  injection Hjo as <-. eauto.
Qed.

(* On [normal_fact] conclusions, [rule_impl env] (any [env]) is exactly DistributedDatalog's [fires]. *)
Lemma rule_impl_iff_fires (env : list (Datalog.fact (rel := rel_id)) -> rel_id -> list T -> Prop)
      (r : Datalog.rule (rel := rel_id) (fn := nat)) (f : Datalog.fact (rel := rel_id))
      (hyps : list (Datalog.fact (rel := rel_id))) :
  (exists R args, f = Datalog.normal_fact R args) ->
  (Datalog.rule_impl env r f hyps <-> DistributedDatalog.fires r f hyps).
Proof.
  intros [R [args ->]]. split.
  - intros H. inversion H; subst. exists R, args. split; [reflexivity | assumption].
  - intros [R' [args' [Heq Hnm]]]. injection Heq as <- <-.
    apply Datalog.simple_rule_impl. assumption.
Qed.

(* [DistributedDatalog]'s env-free network derivability coincides with the reference
   [Datalog.prog_impl] on the bare/normal fragment the compiler targets: [fires] and [rule_impl]
   agree on normal facts (the only facts a bare program ever derives). *)
Lemma prog_impl_fact_iff_datalog (program : list (Datalog.rule (rel := rel_id) (fn := nat)))
    (Q : Datalog.fact (rel := rel_id) -> Prop) (f : Datalog.fact (rel := rel_id)) :
  Forall bare_rule program ->
  DistributedDatalog.prog_impl_fact program Q f <-> Datalog.prog_impl program Q f.
Proof.
  intros Hbare. unfold DistributedDatalog.prog_impl_fact, Datalog.prog_impl. split.
  - apply NodeHardwareSemantics.pftree_weaken. intros x l Hx.
    apply Exists_exists in Hx. destruct Hx as [r [Hin Hfires]].
    apply Exists_exists. exists r. split; [exact Hin|].
    apply (proj2 (rule_impl_iff_fires (Datalog.one_step_derives program) r x l
                    (match Hfires with ex_intro _ R (ex_intro _ args (conj He _)) =>
                       ex_intro _ R (ex_intro _ args He) end))).
    exact Hfires.
  - apply NodeHardwareSemantics.pftree_weaken. intros x l Hx.
    apply Exists_exists in Hx. destruct Hx as [r [Hin Hri]].
    apply Exists_exists. exists r. split; [exact Hin|].
    pose proof (proj1 (Forall_forall _ _) Hbare r Hin) as Hbr.
    pose proof (bare_rule_impl_normal (Datalog.one_step_derives program) r x l Hbr Hri) as Hnorm.
    exact (proj1 (rule_impl_iff_fires (Datalog.one_step_derives program) r x l Hnorm) Hri).
Qed.

(*============================================================================*)
(*  FULLY DECIDABLE top theorem: every side condition is a [bool] checker.      *)
(*  The reference program is the [canonical_program] (the union of every node's *)
(*  placed rules), for which [good_layout] holds structurally; [good_graph] is  *)
(*  discharged by [check_graph_valid] and bareness by [bare_layoutb].           *)
(*============================================================================*)

(* The single reference program a layout induces: every rule placed on any node. *)
Definition canonical_program (llayout : lowered_layout_map)
  : list (Datalog.rule (rel := rel_id) (fn := nat)) :=
  map.fold (fun acc _ p => acc ++ p) [] llayout.

Lemma canonical_program_in (llayout : lowered_layout_map)
    (r : Datalog.rule (rel := rel_id) (fn := nat)) :
  In r (canonical_program llayout) <->
  exists n p, map.get llayout n = Some p /\ In r p.
Proof.
  unfold canonical_program.
  apply (map.fold_spec
    (fun (m : lowered_layout_map) (acc : list (Datalog.rule (rel := rel_id) (fn := nat))) =>
       In r acc <-> exists n p, map.get m n = Some p /\ In r p)).
  - split.
    + intros [].
    + intros [n [p [Hget _]]]. rewrite map.get_empty in Hget. discriminate.
  - intros k v m acc Hgmk IH. rewrite in_app_iff. split.
    + intros [Hacc | Hv].
      * apply IH in Hacc. destruct Hacc as [n [p [Hget Hin]]].
        exists n, p. split; [|exact Hin].
        rewrite map.get_put_diff; [exact Hget|].
        intros ->. rewrite Hgmk in Hget. discriminate.
      * exists k, v. split; [apply map.get_put_same | exact Hv].
    + intros [n [p [Hget Hin]]].
      destruct (eqb_boolspec _ n k) as [->|Hne].
      * rewrite map.get_put_same in Hget. injection Hget as <-. right. exact Hin.
      * rewrite map.get_put_diff in Hget by congruence. left. apply IH. exists n, p. auto.
Qed.

(* Decidable check that every node a layout assigns rules to is a real graph node.  Now a GATE inside
   [compile_lowered]; aliased here so the existing lemmas / top theorems refer to the same function. *)
Notation layout_in_graphb :=
  (@DistributedDatalogToHardwareCompiler.layout_in_graphb var aggregator node_id node_id_set
     lowered_layout_map node_id_edge_set).

Lemma layout_in_graphb_entry (g : node_graph) (llayout : lowered_layout_map) :
  layout_in_graphb g llayout = true ->
  forall n p, map.get llayout n = Some p -> check_node_valid n (ComputableGraph.nodes g) = true.
Proof.
  unfold DistributedDatalogToHardwareCompiler.layout_in_graphb. intros H n p Hget.
  exact (map.get_forallb _ _ H n p Hget).
Qed.

(* [check_node_valid] on [g]'s node set is exactly the graph-node predicate of [cg2g g]. *)
Lemma cg2g_node (g : node_graph) (n : node_id) :
  check_node_valid n (ComputableGraph.nodes g) = true -> Graph.nodes (cg2g g) n.
Proof. intros H. exact H. Qed.

(* The canonical program is placed exactly by [llayout] over real graph nodes. *)
Lemma canonical_good_layout (g : node_graph) (llayout : lowered_layout_map) :
  layout_in_graphb g llayout = true ->
  DistributedDatalog.good_layout (fun n => lprog_of llayout n)
    (Graph.nodes (cg2g g)) (canonical_program llayout).
Proof.
  intros Hkeys. unfold DistributedDatalog.good_layout. split.
  - apply Forall_forall. intros r Hr.
    apply canonical_program_in in Hr. destruct Hr as [n [p [Hget Hin]]].
    exists n. split.
    + apply cg2g_node. apply (layout_in_graphb_entry g llayout Hkeys n p Hget).
    + unfold lprog_of. rewrite Hget. exact Hin.
  - intros n r Hin. unfold lprog_of in Hin.
    destruct (map.get llayout n) as [p|] eqn:Hget; [|destruct Hin].
    split.
    + apply cg2g_node. apply (layout_in_graphb_entry g llayout Hkeys n p Hget).
    + apply canonical_program_in. exists n, p. auto.
Qed.

(* Every rule of the canonical program is bare when the whole layout is bare. *)
Lemma canonical_bare (llayout : lowered_layout_map) :
  bare_layoutb llayout = true -> Forall bare_rule (canonical_program llayout).
Proof.
  intros Hbare. apply Forall_forall. intros r Hr.
  apply canonical_program_in in Hr. destruct Hr as [n [p [Hget Hin]]].
  pose proof (bare_layoutb_entry llayout Hbare n p Hget) as Hp.
  rewrite forallb_forall in Hp. apply bare_ruleb_spec. apply Hp. exact Hin.
Qed.

(*============================================================================*)
(*  PATH B: derive reachability from the compiler's CONSTRUCTION, not from      *)
(*  re-validating routes against the finished forwarding table.                 *)
(*                                                                              *)
(*  Instead of the route checkers ([routes_validatedb] / [input_routes_-        *)
(*  validatedb]), which re-walk the *generated table* via [validate_route], we   *)
(*  check the compiler's own search + dependency analysis:                       *)
(*    - the relation is registered ([In R (get_rel_ids gcontext)]),             *)
(*    - the (input/producer, consumer) nodes are in [gcontext]'s producer/       *)
(*      consumer maps, and                                                      *)
(*    - [get_path] FOUND a path between them in the graph,                      *)
(*  and then PROVE reachability with the Phase C2 engine                        *)
(*  ([generate_forwarding_table_adds] / [generate_forwarding_reachable]): the    *)
(*  generated table really realizes every path the compiler laid down.          *)
(*============================================================================*)

(* Membership in a [node_id_set] (a [map node_id unit]) as a [bool]. *)
Definition nid_mem (s : node_id_set) (n : node_id) : bool :=
  match map.get s n with Some _ => true | None => false end.

Lemma nid_mem_get (s : node_id_set) (n : node_id) :
  nid_mem s n = true -> map.get s n = Some tt.
Proof.
  unfold nid_mem. destruct (map.get s n) as [u|] eqn:H; [destruct u; reflexivity | discriminate].
Qed.

(* Membership of [n] in the dependency map [m] at relation [R]. *)
Definition rel_dep_has (m : rel_dependency_map) (R : rel_id) (n : node_id) : bool :=
  match map.get m R with Some s => nid_mem s n | None => false end.

Lemma rel_dep_has_get (m : rel_dependency_map) (R : rel_id) (n : node_id) :
  rel_dep_has m R n = true -> exists s, map.get m R = Some s /\ map.get s n = Some tt.
Proof.
  unfold rel_dep_has. destruct (map.get m R) as [s|] eqn:Hm; [|discriminate].
  intros Hn. exists s. split; [reflexivity | apply nid_mem_get; exact Hn].
Qed.

(* CORE PATH-B REACH: a registered relation whose producer/consumer nodes the compiler recorded,
   joined by a [get_path] the compiler found, is forwarding-reachable in the GENERATED table.
   This is the single place the Phase C2 engine ([generate_forwarding_reachable]) is invoked. *)
Lemma construction_reach (gcontext : global_context) (ninfos : list node_info)
    (g : node_graph) (R : rel_id) (np nc : node_id) :
  In R (get_rel_ids gcontext) ->
  rel_dep_has gcontext.(DistributedDatalogToHardwareCompiler.rel_node_producers) R np = true ->
  rel_dep_has gcontext.(DistributedDatalogToHardwareCompiler.rel_node_consumers) R nc = true ->
  Datalog.List.is_Some (get_path g np nc) = true ->
  np = nc \/
  @DistributedDatalog.forwarding_reachable rel_id node_id
    (fwd_list (generate_forwarding_table gcontext ninfos g )) R np nc.
Proof.
  intros HR Hprod Hcons Hpath.
  destruct (eqb_boolspec _ np nc) as [E|Hne]; [left; exact E | right].
  destruct (get_path g np nc) as [path|] eqn:Hgpath; [| cbn in Hpath; discriminate].
  destruct (rel_dep_has_get _ _ _ Hprod) as [producers [Hprodm Hprodn]].
  destruct (rel_dep_has_get _ _ _ Hcons) as [consumers [Hconsm Hconsn]].
  exact (generate_forwarding_reachable g gcontext ninfos R np nc path producers consumers
           HR Hprodm Hconsm Hprodn Hconsn Hne Hgpath).
Qed.

(* The declared input/EDB (or, with [lfc], output/sink) locations of relation [R]. *)
Definition rel_locs (lfp : lowered_fact_locations) (R : rel_id) : list node_id :=
  match map.get lfp R with
  | Some locs => locs
  | None => []
  end.

Lemma rel_locs_In (lfp : lowered_fact_locations) (R : rel_id) (n : node_id) :
  In n (rel_locs lfp R) -> exists locs, map.get lfp R = Some locs /\ In n locs.
Proof.
  unfold rel_locs.
  destruct (map.get lfp R) as [locs|] eqn:Hf; [|intros []].
  intros Hn. exists locs. split; [reflexivity | exact Hn].
Qed.

(* [edb_routable lfp Q]: the base facts [Q] form a routable EDB for the declared input/producer
   locations [lfp] -- every [Q]-fact's relation has at least one declared input node, so the fact can
   actually enter the network.  (This is the EDB side condition of the top correctness theorem.) *)
Definition edb_routable (lfp : lowered_fact_locations) (Q : Datalog.fact (rel := rel_id) -> Prop) : Prop :=
  forall f, Q f -> exists n, In n (rel_locs lfp (Datalog.rel_of f)).

(* SOURCE-LEVEL EDB routability, the form the top theorem actually takes as its side condition.  It
   mentions ONLY the user's two original objects -- the fact-producer table [fps] and the base-fact set
   [Qsrc] -- with NO renaming, NO layout, NO program.  (It is a genuine EXTRA condition, not implied by
   [compile = Success]: [compile] never receives [Qsrc], so it cannot know every injected fact has a
   declared input node.  What [compile] gates is that the declared locations route well, not that [fps]
   covers [Qsrc].)  [src_rel_locs] is the source twin of [rel_locs] -- a plain [map.get]. *)
Definition src_rel_locs (fps : fact_locations) (R : rel) : list node_id :=
  match map.get fps R with Some locs => locs | None => [] end.
Definition edb_routable_src (fps : fact_locations) (Qsrc : Datalog.fact -> Prop) : Prop :=
  forall f, Qsrc f -> exists n, In n (src_rel_locs fps (Datalog.rel_of f)).

Notation output_routesb :=
  (@DistributedDatalogToHardwareCompiler.output_routesb rel var aggregator node_id node_id_eqb node_id_set rel_dependency_map rel_relid_map lowered_layout_map lowered_fact_locations_map node_id_edge_set).
Notation input_output_routesb :=
  (@DistributedDatalogToHardwareCompiler.input_output_routesb rel node_id node_id_eqb node_id_set rel_dependency_map rel_relid_map lowered_fact_locations_map node_id_edge_set).
Notation routes_validb :=
  (@DistributedDatalogToHardwareCompiler.routes_validb rel var aggregator node_id node_id_eqb node_id_set rel_dependency_map rel_relid_map lowered_layout_map node_id_edge_set).

Lemma construction_good_source (gcontext : global_context) (ninfos : list node_info)
    (g : node_graph) (llayout : lowered_layout_map) (lfc : lowered_fact_locations)
    (net : DNet) :
  net.(DistributedDatalog.layout) = (fun n => lprog_of llayout n) ->
  net.(DistributedDatalog.forward) = fwd_list (generate_forwarding_table gcontext ninfos g ) ->
  net.(DistributedDatalog.output) = (fun n R => In n (rel_locs lfc R)) ->
  routes_validb gcontext g llayout = true ->
  output_routesb gcontext g llayout lfc = true ->
  forall n_prod R, DistributedDatalog.node_produces net.(DistributedDatalog.layout) n_prod R ->
    DistributedDatalog.good_source net n_prod R.
Proof.
  intros Hlay Hfwd Houtput Hchk Houtchk n_prod R Hprod.
  rewrite Hlay in Hprod. destruct Hprod as [rule_np [Hin_np HR_concl]].
  destruct (map.get llayout n_prod) as [p_np|] eqn:Hgnp;
    [|exfalso; revert Hin_np; unfold lprog_of; rewrite Hgnp; intros []].
  assert (Hkey_np : In n_prod (map.keys llayout)) by exact (map.in_keys llayout n_prod p_np Hgnp).
  unfold DistributedDatalogToHardwareCompiler.routes_validb in Hchk. rewrite forallb_forall in Hchk. specialize (Hchk n_prod Hkey_np).
  rewrite forallb_forall in Hchk. specialize (Hchk rule_np Hin_np).
  rewrite forallb_forall in Hchk. specialize (Hchk R HR_concl).
  apply andb_true_iff in Hchk. destruct Hchk as [Hchk Hnc].
  apply andb_true_iff in Hchk. destruct Hchk as [Hrelids Hprodmem].
  assert (HRin : In R (get_rel_ids gcontext)).
  { apply existsb_exists in Hrelids. destruct Hrelids as [R' [HR'in HR'eq]].
    apply Nat.eqb_eq in HR'eq. subst R'. exact HR'in. }
  rewrite forallb_forall in Hnc.
  split.
  - intros n_cons Hcons. rewrite Hlay in Hcons. destruct Hcons as [rule_nc [Hin_nc HR_hyp]].
    destruct (map.get llayout n_cons) as [p_nc|] eqn:Hgnc;
      [|exfalso; revert Hin_nc; unfold lprog_of; rewrite Hgnc; intros []].
    assert (Hkey_nc : In n_cons (map.keys llayout)) by exact (map.in_keys llayout n_cons p_nc Hgnc).
    specialize (Hnc n_cons Hkey_nc).
    assert (Hex : existsb (fun rnc => existsb (Nat.eqb R) (Datalog.hyp_rels rnc)) (lprog_of llayout n_cons) = true).
    { apply existsb_exists. exists rule_nc. split.
      - exact Hin_nc.
      - apply existsb_exists. exists R. split; [exact HR_hyp | apply Nat.eqb_refl]. }
    rewrite Hex in Hnc.
    apply andb_true_iff in Hnc. destruct Hnc as [Hconsmem Hpathchk].
    rewrite Hfwd.
    exact (construction_reach gcontext ninfos g R n_prod n_cons HRin Hprodmem Hconsmem Hpathchk).
  - unfold output_routesb in Houtchk. rewrite forallb_forall in Houtchk. specialize (Houtchk n_prod Hkey_np).
    rewrite forallb_forall in Houtchk. specialize (Houtchk rule_np Hin_np).
    rewrite forallb_forall in Houtchk. specialize (Houtchk R HR_concl).
    apply andb_true_iff in Houtchk. destruct Houtchk as [_ Hexout].
    apply existsb_exists in Hexout. destruct Hexout as [no [Hno_in Hno_cond]].
    apply andb_true_iff in Hno_cond. destruct Hno_cond as [Hconsmem_o Hpathchk_o].
    exists no. split.
    + rewrite Houtput. exact Hno_in.
    + rewrite Hfwd.
      exact (construction_reach gcontext ninfos g R n_prod no HRin Hprodmem Hconsmem_o Hpathchk_o).
Qed.

(*============================================================================*)
(*  PATH B, CORRECT BY CONSTRUCTION: the producer-routing condition is no        *)
(*  longer a separate checker -- it is threaded through the result monad in the  *)
(*  compiler ([generate_forwarding_table_checked]).  The compiler REFUSES to      *)
(*  emit a forwarding table unless every producer can reach every consumer, so    *)
(*  [Success] is itself the witness of routing correctness.                       *)
(*============================================================================*)

Notation generate_forwarding_table_checked :=
  (@DistributedDatalogToHardwareCompiler.generate_forwarding_table_checked rel var aggregator node_id node_id_eqb node_id_set forwarding_table rel_dependency_map rel_relid_map lowered_layout_map node_id_edge_set node_ftable_map).

(* The compiler's forwarding gate IS (convertibly) the producer construction checker. *)
(* The monadic forwarding step: on [Success] the table is the usual one AND the routing gate passed. *)
Lemma generate_forwarding_table_checked_success (gcontext : global_context)
    (ninfos : list node_info) (g : node_graph) (llayout : lowered_layout_map)
    (ft : node_ftable_map) :
  generate_forwarding_table_checked gcontext ninfos g llayout = Success ft ->
  ft = generate_forwarding_table gcontext ninfos g /\ routes_validb gcontext g llayout = true.
Proof.
  unfold DistributedDatalogToHardwareCompiler.generate_forwarding_table_checked.
  destruct (routes_validb gcontext g llayout) eqn:Hv; intros H.
  - injection H as <-. split; reflexivity.
  - discriminate H.
Qed.

(*============================================================================*)
(*  CLEAN TOP THEOREM over [compile = Success]: BOTH producer and input routing  *)
(*  are by construction (gated inside [compile]), so the ONLY side conditions    *)
(*  are a layout check and bareness.  Base facts [Q] enter at the declared        *)
(*  fact-producer locations.                                                      *)
(*============================================================================*)

Notation input_routes_validb :=
  (@DistributedDatalogToHardwareCompiler.input_routes_validb rel var aggregator node_id node_id_eqb node_id_set rel_dependency_map rel_relid_map lowered_layout_map lowered_fact_locations_map node_id_edge_set).

(* The streaming network whose base facts [Q] enter at the declared fact-producer (input) locations
   and whose OUTPUT nodes are the declared fact-consumer (sink) locations [lfc]. *)
Definition compiled_base_edb (g : node_graph) (ftables : node_ftable_map)
    (lfp lfc : lowered_fact_locations) (Q : Datalog.fact (rel := rel_id) -> Prop) : DNet :=
  {| DistributedDatalog.graph := cg2g g;
     DistributedDatalog.forward := fwd_list ftables;
     DistributedDatalog.input := fun n f => Q f /\ In n (rel_locs lfp (Datalog.rel_of f));
     DistributedDatalog.output := fun n R => In n (rel_locs lfc R);
     DistributedDatalog.layout := fun _ => [] |}.

(* Every declared input location is a good source, from the compiler's input gate [input_routes_validb]. *)
Lemma edb_input_good_source (gcontext : global_context) (ninfos : list node_info)
    (g : node_graph) (llayout : lowered_layout_map)
    (lfp lfc : lowered_fact_locations) (net : DNet) :
  net.(DistributedDatalog.layout) = (fun n => lprog_of llayout n) ->
  net.(DistributedDatalog.forward) = fwd_list (generate_forwarding_table gcontext ninfos g ) ->
  net.(DistributedDatalog.output) = (fun n R => In n (rel_locs lfc R)) ->
  input_routes_validb gcontext g llayout lfp = true ->
  input_output_routesb gcontext g lfp lfc = true ->
  forall R locs ni, map.get lfp R = Some locs -> In ni locs -> DistributedDatalog.good_source net ni R.
Proof.
  intros Hlay Hfwd Houtput Hchk Houtchk R locs ni Hlfp Hni. split.
  - intros n_cons Hcons. rewrite Hlay in Hcons. destruct Hcons as [rule_nc [Hin_nc HR_hyp]].
    destruct (map.get llayout n_cons) as [p_nc|] eqn:Hgnc;
      [|exfalso; revert Hin_nc; unfold lprog_of; rewrite Hgnc; intros []].
    assert (Hkey_nc : In n_cons (map.keys llayout)) by exact (map.in_keys llayout n_cons p_nc Hgnc).
    unfold input_routes_validb in Hchk. apply (fun H => map.get_forallb _ _ H _ _ Hlfp) in Hchk.
    cbn beta in Hchk. rewrite forallb_forall in Hchk. specialize (Hchk ni Hni).
    apply andb_true_iff in Hchk. destruct Hchk as [Hchk Hncf].
    apply andb_true_iff in Hchk. destruct Hchk as [Hrelids Hprodmem].
    assert (HRin : In R (get_rel_ids gcontext)).
    { apply existsb_exists in Hrelids. destruct Hrelids as [R' [HR'in HR'eq]].
      apply Nat.eqb_eq in HR'eq. subst R'. exact HR'in. }
    rewrite forallb_forall in Hncf. specialize (Hncf n_cons Hkey_nc). cbn beta in Hncf.
    match type of Hncf with
    | (if ?c then _ else _) = true => assert (Hcond : c = true)
    end.
    { apply existsb_exists. exists rule_nc. split.
      - exact Hin_nc.
      - apply existsb_exists. exists R. split; [exact HR_hyp | apply Nat.eqb_refl]. }
    rewrite Hcond in Hncf.
    apply andb_true_iff in Hncf. destruct Hncf as [Hconsmem Hpathchk].
    rewrite Hfwd.
    exact (construction_reach gcontext ninfos g R ni n_cons HRin Hprodmem Hconsmem Hpathchk).
  - unfold input_output_routesb in Houtchk. apply (fun H => map.get_forallb _ _ H _ _ Hlfp) in Houtchk.
    cbn beta in Houtchk. rewrite forallb_forall in Houtchk. specialize (Houtchk ni Hni).
    apply andb_true_iff in Houtchk. destruct Houtchk as [Houtchk Hexout].
    apply andb_true_iff in Houtchk. destruct Houtchk as [Hrelids Hprodmem].
    assert (HRin : In R (get_rel_ids gcontext)).
    { apply existsb_exists in Hrelids. destruct Hrelids as [R' [HR'in HR'eq]].
      apply Nat.eqb_eq in HR'eq. subst R'. exact HR'in. }
    apply existsb_exists in Hexout. destruct Hexout as [no [Hno_in Hno_cond]].
    apply andb_true_iff in Hno_cond. destruct Hno_cond as [Hconsmem_o Hpathchk_o].
    exists no. split.
    + rewrite Houtput. exact Hno_in.
    + rewrite Hfwd.
      exact (construction_reach gcontext ninfos g R ni no HRin Hprodmem Hconsmem_o Hpathchk_o).
Qed.

(* PHASE D (EDB streaming): the compiled network with input at fact-producer locations is
   [good_network_streaming].  Producers good-source via the [routes_validb] gate; input nodes via the
   compiler's [input_routes_validb] gate; [Q] is the declared EDB (each base fact's relation has a
   fact-producer location). *)
Theorem compiled_good_network_streaming_edb
    (g : node_graph) (gcontext : global_context) (ninfos : list node_info)
    (llayout : lowered_layout_map) (lfp lfc : lowered_fact_locations)
    (program : list (Datalog.rule (rel := rel_id) (fn := nat))) (Q : Datalog.fact (rel := rel_id) -> Prop) :
  Graph.good_graph (cg2g g) ->
  DistributedDatalog.good_layout (fun n => lprog_of llayout n) (Graph.nodes (cg2g g)) program ->
  routes_validb gcontext g llayout = true ->
  input_routes_validb gcontext g llayout lfp = true ->
  output_routesb gcontext g llayout lfc = true ->
  input_output_routesb gcontext g lfp lfc = true ->
  (forall f, Q f -> exists n, In n (rel_locs lfp (Datalog.rel_of f))) ->
  DistributedDatalog.good_network_streaming
    (dnet_of_llayout llayout (compiled_base_edb g (generate_forwarding_table gcontext ninfos g ) lfp lfc Q))
    program Q.
Proof.
  intros Hgg Hlay Hroutes Hinput Houtroutes Hinoutroutes HQ.
  unfold DistributedDatalog.good_network_streaming, dnet_of_llayout, compiled_base_edb; cbn.
  split; [exact Hgg|].
  split; [exact Hlay|].
  split.
  - intros n1 n2 r Hin.
    assert (Hedge : @ComputableGraph.cg_edge node_id node_id_set node_id_edge_set g n1 n2)
      by exact (generate_forwarding_table_sound g gcontext ninfos n1 r n2 Hin).
    destruct (Hgg n1 n2 Hedge) as [Hn1 Hn2]. split; [exact Hn1 | split; [exact Hn2 | exact Hedge]].
  - split.
    + apply (construction_good_source gcontext ninfos g llayout lfc
               (dnet_of_llayout llayout (compiled_base_edb g (generate_forwarding_table gcontext ninfos g ) lfp lfc Q)));
        [reflexivity | reflexivity | reflexivity | exact Hroutes | exact Houtroutes].
    + split.
      * intros n f [HQf _]. exact HQf.
      * intros f HQf. destruct (HQ f HQf) as [n Hn].
        destruct (rel_locs_In lfp (Datalog.rel_of f) n Hn) as [locs [Hlfp Hnlocs]].
        exists n. split.
        -- split; [exact HQf | exact Hn].
        -- apply (edb_input_good_source gcontext ninfos g llayout lfp lfc
                    (dnet_of_llayout llayout (compiled_base_edb g (generate_forwarding_table gcontext ninfos g ) lfp lfc Q)))
             with (locs := locs);
             [reflexivity | reflexivity | reflexivity | exact Hinput | exact Hinoutroutes | exact Hlfp | exact Hnlocs].
Qed.

(* Invert the relabel pass: [lower_inputs] returns exactly the renamed layout/fact-tables and the
   collected name context, so its [Success] equation IS the rename results.  Replaces the old
   re-derivation helpers ([compile_global_rename_success]/[compile_fps_rename_success]). *)
Lemma lower_inputs_inv (layout : layout_map) (fps fcs : fact_locations)
    (llayout : lowered_layout_map) (lfp lfc : lowered_fact_locations) (gcontext : global_context) :
  lower_inputs layout fps fcs = Success (llayout, lfp, lfc, gcontext) ->
  gcontext = collect_global_names_layout layout initial_global_context /\
  global_rename_rule_layout layout gcontext = Success llayout /\
  global_rename_fact_locations fps gcontext = Success lfp /\
  global_rename_fact_locations fcs gcontext = Success lfc.
Proof.
  intros H. unfold lower_inputs, DistributedDatalogToHardwareCompiler.lower_inputs in H. cbv zeta in H.
  destruct (global_rename_rule_layout layout (collect_global_names_layout layout initial_global_context))
    as [ll|] eqn:Hgr; cbn beta iota in H; [|discriminate].
  destruct (DistributedDatalogToHardwareCompiler.global_rename_fact_locations fps
              (collect_global_names_layout layout initial_global_context)) as [lp|] eqn:Hlp;
    cbn beta iota in H; [|discriminate].
  destruct (DistributedDatalogToHardwareCompiler.global_rename_fact_locations fcs
              (collect_global_names_layout layout initial_global_context)) as [lc|] eqn:Hlc;
    cbn beta iota in H; [|discriminate].
  inversion H; subst.
  split; [reflexivity | split; [exact Hgr | split; [exact Hlp | exact Hlc]]].
Qed.

(* [compile = Success], given the compiler's OWN lowering outputs ([lower_inputs] = the renamed
   layout/fact-tables/context), entails the per-node compilation, the forwarding gate, and the input
   gate -- stated over those ACTUAL intermediates (no re-derivation exposers). *)
Lemma compile_success_extract (layout : layout_map) (fps fcs : fact_locations)
    (g : node_graph) (ninfos : list node_info)
    (llayout : lowered_layout_map) (lfp lfc : lowered_fact_locations) (gcontext : global_context) :
  lower_inputs layout fps fcs = Success (llayout, lfp, lfc, gcontext) ->
  compile layout fps fcs g = Success ninfos ->
  exists ninfos0 ftables,
    ninfos = attach_forwarding_tables ninfos0 ftables /\
    compile_all_nodes llayout (collect_global_dependencies llayout lfp lfc gcontext)
      = Success ninfos0 /\
    generate_forwarding_table_checked (collect_global_dependencies llayout lfp lfc gcontext) ninfos0 g
      llayout = Success ftables /\
    input_routes_validb (collect_global_dependencies llayout lfp lfc gcontext) g llayout
      lfp = true /\
    output_routesb (collect_global_dependencies llayout lfp lfc gcontext) g llayout
      lfc = true /\
    input_output_routesb (collect_global_dependencies llayout lfp lfc gcontext) g
      lfp lfc = true /\
    check_graph_valid g = true /\
    layout_in_graphb g llayout = true.
Proof.
  intros Hlow H. unfold DistributedDatalogToHardwareCompiler.compile in H.
  rewrite Hlow in H. cbn beta iota in H.
  unfold DistributedDatalogToHardwareCompiler.compile_lowered in H. cbv zeta in H.
  destruct (check_graph_valid g) eqn:Hcgv; cbn beta iota in H; [|discriminate].
  destruct (DistributedDatalogToHardwareCompiler.layout_in_graphb g llayout) eqn:Hlig;
    cbn beta iota in H; [|discriminate].
  destruct (compile_all_nodes llayout (collect_global_dependencies llayout lfp lfc gcontext))
    as [ninfos0|] eqn:Hcan; cbn beta iota in H; [|discriminate].
  destruct (DistributedDatalogToHardwareCompiler.generate_forwarding_table_checked
              (collect_global_dependencies llayout lfp lfc gcontext) ninfos0 g llayout)
    as [ftables|] eqn:Hft; cbn beta iota in H; [|discriminate].
  destruct (DistributedDatalogToHardwareCompiler.input_routes_validb
              (collect_global_dependencies llayout lfp lfc gcontext) g llayout lfp) eqn:Hinp;
    cbn beta iota in H; [|discriminate].
  destruct (DistributedDatalogToHardwareCompiler.output_routesb
              (collect_global_dependencies llayout lfp lfc gcontext) g llayout lfc) eqn:Houtp;
    cbn beta iota in H; [|discriminate].
  destruct (DistributedDatalogToHardwareCompiler.input_output_routesb
              (collect_global_dependencies llayout lfp lfc gcontext) g lfp lfc) eqn:Hinoutp;
    cbn beta iota in H; [|discriminate].
  injection H as Hret.
  exists ninfos0, ftables.
  split; [exact (eq_sym Hret) | repeat split; first [reflexivity | assumption]].
Qed.

(*----The hardware network read DIRECTLY off the returned [ninfos]----*)

(* [dnet_of_ninfos ninfos base]: the dataflow network whose forwarding function is read off the
   per-node [nforwarding] of [ninfos] (via [forward_of_ninfos]); graph/input/output/layout are
   inherited from [base] (the reference graph + EDB + output sinks + datalog layout). *)
Definition dnet_of_ninfos (ninfos : list node_info) (base : DNet) : DNet :=
  {| DistributedDatalog.graph := base.(DistributedDatalog.graph);
     DistributedDatalog.forward := forward_of_ninfos ninfos;
     DistributedDatalog.input := base.(DistributedDatalog.input);
     DistributedDatalog.output := base.(DistributedDatalog.output);
     DistributedDatalog.layout := base.(DistributedDatalog.layout) |}.

(*============================================================================*)
(*  OPERATIONAL <-> DISTRIBUTED-NETWORK adequacy.  The standalone operational     *)
(*  run [DistributedHardwareSemantics.hw_run_output] over a [DistributedDatalog]   *)
(*  network's OWN forwarding/input/output, with each node's HARDWARE rules         *)
(*  matching that node's DATALOG rules, derives EXACTLY what the network derives.  *)
(*  This binds the operational semantics DIRECTLY to                               *)
(*  [DistributedDatalog.network_prog_impl_fact] -- there is no [hw_net_step].       *)
(*============================================================================*)

(* [get_facts_on_node] shape lemmas. *)
Lemma get_facts_on_node_in (l : list (@DistributedDatalog.network_prop rel_id T node_id))
      (n : node_id) (g : Datalog.fact (rel := rel_id)) :
  In (n, g) (get_facts_on_node l) -> In (FactOnNode n g) l.
Proof.
  induction l as [| p l IH]; cbn; [intros []|].
  destruct p as [n0 g0 | n0 g0].
  - intros [Heq | Hin]; [injection Heq as -> ->; left; reflexivity | right; apply IH, Hin].
  - intros Hin; right; apply IH, Hin.
Qed.

Lemma facts_on_node_map_fst (n : node_id) (l : list (Datalog.fact (rel := rel_id))) :
  Forall (fun n' => n' = n) (map fst (get_facts_on_node (map (FactOnNode n) l))).
Proof. induction l as [|a l IH]; cbn; [constructor | constructor; [reflexivity | exact IH]]. Qed.

Lemma facts_on_node_map_snd (n : node_id) (l : list (Datalog.fact (rel := rel_id))) :
  map snd (get_facts_on_node (map (FactOnNode n) l)) = l.
Proof. induction l as [|a l IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Section OperationalNetworkAdequacy.
Context (net : DNet) (prog : node_id -> hardware_program) (tries : node_id -> list trie).
Context (Hmatch : forall n, Forall2 (hw_rule_matches (tries n) (fun _ _ _ => False))
                              (net.(DistributedDatalog.layout) n) (prog n)).

Local Notation Fwd := (net.(DistributedDatalog.forward)).
Local Notation Inp := (net.(DistributedDatalog.input)).
Local Notation Outp := (net.(DistributedDatalog.output)).
Local Notation present := (DistributedHardwareSemantics.present prog tries Fwd Inp).

(* per-node firing bridge: a node's hardware rules fire iff its matching datalog rules fire *)
Lemma node_fires_iff (n : node_id) (f : Datalog.fact (rel := rel_id)) (hyps' : list (Datalog.fact (rel := rel_id))) :
  Exists (fun hr => hw_rule_impl (tries n) hr f hyps') (prog n)
  <-> Exists (fun r => DistributedDatalog.fires r f hyps') (net.(DistributedDatalog.layout) n).
Proof.
  split; intros HE.
  - pose proof HE as HEc. apply Exists_exists in HEc. destruct HEc as [hr [_ Himpl]].
    assert (Hnorm : exists R args, f = Datalog.normal_fact R args)
      by exact (hw_rule_impl_concl_normal (tries n) hr f hyps' Himpl).
    apply (proj1 (matches_step (tries n) (net.(DistributedDatalog.layout) n) (prog n)
                    (fun _ _ _ => False) f hyps' (Hmatch n))) in HE.
    apply Exists_exists in HE. destruct HE as [r [Hin Hri]]. apply Exists_exists. exists r. split; [exact Hin|].
    exact (proj1 (rule_impl_iff_fires (fun _ _ _ => False) r f hyps' Hnorm) Hri).
  - pose proof HE as HEc. apply Exists_exists in HEc. destruct HEc as [r0 [_ [R [args [He _]]]]].
    assert (Hnorm : exists R args, f = Datalog.normal_fact R args) by (exists R, args; exact He).
    apply (proj2 (matches_step (tries n) (net.(DistributedDatalog.layout) n) (prog n)
                    (fun _ _ _ => False) f hyps' (Hmatch n))).
    apply Exists_exists in HE. destruct HE as [r [Hin Hfires]]. apply Exists_exists. exists r. split; [exact Hin|].
    exact (proj2 (rule_impl_iff_fires (fun _ _ _ => False) r f hyps' Hnorm) Hfires).
Qed.

(* a single node's [node_run] re-plays as a network proof tree of [FactOnNode]s *)
Lemma node_run_to_netpft (c : DistributedHardwareSemantics.config) (n : node_id) (f : Datalog.fact (rel := rel_id)) :
  (forall h, c n h -> network_pftree net (FactOnNode n h)) ->
  node_run (tries n) (prog n) (c n) f ->
  network_pftree net (FactOnNode n f).
Proof.
  intros Hleaf. unfold node_run. revert f.
  apply (Datalog.pftree_ind
           (fun f hyps' => Exists (fun hr => hw_rule_impl (tries n) hr f hyps') (prog n))
           (c n)
           (fun f => network_pftree net (FactOnNode n f))).
  - intros f0 HQ. apply Hleaf, HQ.
  - intros f0 hyps' Hex _ HR.
    apply node_fires_iff in Hex. apply Exists_exists in Hex. destruct Hex as [r [Hin Hfires]].
    unfold network_pftree. eapply pftree_step with (l := map (FactOnNode n) hyps').
    + eapply DistributedDatalog.RuleApp;
        [ exact Hin | apply facts_on_node_map_fst | rewrite facts_on_node_map_snd; exact Hfires ].
    + apply Forall_forall. intros p Hp. apply in_map_iff in Hp.
      destruct Hp as [g [<- Hg]]. rewrite Forall_forall in HR. apply HR, Hg.
Qed.

(* SOUNDNESS of the operational run: every reachable fact is derivable by the network *)
Lemma reach_to_netpft (c : DistributedHardwareSemantics.config) :
  DistributedHardwareSemantics.dreach prog tries Fwd Inp c ->
  forall n f, c n f -> network_pftree net (FactOnNode n f).
Proof.
  intros Hr. induction Hr as [| c c' Hr IH Hstep]; intros n f Hcf.
  - destruct Hcf.
  - inversion Hstep as [a g Hi | a g Hru | a a' g Hag Hfwd]; subst c'.
    + destruct Hcf as [Hold | [-> ->]].
      * apply IH; exact Hold.
      * unfold network_pftree. eapply pftree_step with (l := []); [apply DistributedDatalog.Input; exact Hi | constructor].
    + destruct Hcf as [Hold | [-> ->]].
      * apply IH; exact Hold.
      * apply (node_run_to_netpft c a g); [intros h Hch; apply IH; exact Hch | exact Hru].
    + destruct Hcf as [Hold | [-> ->]].
      * apply IH; exact Hold.
      * unfold network_pftree. eapply pftree_step with (l := [FactOnNode a g]);
          [apply DistributedDatalog.Forward; exact Hfwd | constructor; [apply IH; exact Hag | constructor]].
Qed.

Theorem hw_run_output_to_network (f : Datalog.fact (rel := rel_id)) :
  DistributedHardwareSemantics.hw_run_output prog tries Fwd Inp Outp f -> network_prog_impl_fact net f.
Proof.
  intros [n [c [Hr [Hcf Hout]]]]. exists n.
  unfold network_pftree. eapply pftree_step with (l := [FactOnNode n f]);
    [apply DistributedDatalog.OutputStep; exact Hout
    | constructor; [apply (reach_to_netpft c Hr n f Hcf) | constructor]].
Qed.

(* COMPLETENESS of the operational run: the [RuleApp] case merges the present hypotheses
   ([present_list]) and fires a matching hardware rule ([node_fires_iff] + [dstep_run]). *)
Lemma netpft_present (x : @DistributedDatalog.network_prop rel_id T node_id) :
  network_pftree net x ->
  match x with
  | FactOnNode n f => present n f
  | Output n f => present n f /\ Outp n (Datalog.rel_of f)
  end.
Proof.
  revert x. unfold network_pftree.
  apply (Datalog.pftree_ind (fun fact_node hyps => network_step net fact_node hyps) (fun _ => False)
           (fun x => match x with
                     | FactOnNode n f => present n f
                     | Output n f => present n f /\ Outp n (Datalog.rel_of f)
                     end)).
  - intros x [].
  - intros x l Hstep _ HR.
    destruct Hstep as [n f Hi | n f r hyps Hin Hfst Hfires | n n' f Hfwd | n f Hout].
    + exists (DistributedHardwareSemantics.cadd (fun _ _ => False) n f). split.
      * eapply DistributedHardwareSemantics.dreachS;
          [apply DistributedHardwareSemantics.dreach0 | apply DistributedHardwareSemantics.dstep_input; exact Hi].
      * right; split; reflexivity.
    + assert (Hpres : Forall (fun g => present n g) (map snd (get_facts_on_node hyps))).
      { apply Forall_forall. intros g Hg. apply in_map_iff in Hg.
        destruct Hg as [[n' g'] [Heq Hin']]. cbn in Heq; subst g'.
        assert (Hn' : n' = n).
        { rewrite Forall_forall in Hfst. apply Hfst, in_map_iff.
          exists (n', g); split; [reflexivity | exact Hin']. }
        subst n'. pose proof (get_facts_on_node_in hyps n g Hin') as HinFact.
        rewrite Forall_forall in HR. exact (HR _ HinFact). }
      destruct (DistributedHardwareSemantics.present_list prog tries Fwd Inp n _ Hpres)
        as [c [Hrc Hcfacts]].
      assert (Hnr : node_run (tries n) (prog n) (c n) f).
      { unfold node_run. eapply pftree_step with (l := map snd (get_facts_on_node hyps)).
        - apply node_fires_iff. apply Exists_exists. exists r. split; [exact Hin | exact Hfires].
        - apply Forall_forall. intros g Hg. apply pftree_leaf.
          rewrite Forall_forall in Hcfacts. apply Hcfacts, Hg. }
      exists (DistributedHardwareSemantics.cadd c n f). split.
      * eapply DistributedHardwareSemantics.dreachS;
          [exact Hrc | apply DistributedHardwareSemantics.dstep_run; exact Hnr].
      * right; split; reflexivity.
    + pose proof (Forall_inv HR) as Hpres. destruct Hpres as [c [Hrc Hcnf]].
      exists (DistributedHardwareSemantics.cadd c n' f). split.
      * eapply DistributedHardwareSemantics.dreachS;
          [exact Hrc
          | apply (DistributedHardwareSemantics.dstep_forward prog tries Fwd Inp c n n' f Hcnf Hfwd)].
      * right; split; reflexivity.
    + split; [exact (Forall_inv HR) | exact Hout].
Qed.

Theorem network_to_hw_run_output (f : Datalog.fact (rel := rel_id)) :
  network_prog_impl_fact net f -> DistributedHardwareSemantics.hw_run_output prog tries Fwd Inp Outp f.
Proof.
  intros [n Hpf]. pose proof (netpft_present (Output n f) Hpf) as Hmot.
  destruct Hmot as [[c [Hrc Hcnf]] Hout].
  exists n, c. split; [exact Hrc | split; [exact Hcnf | exact Hout]].
Qed.

(* ADEQUACY: the operational run of [net]'s data equals the network's derivability. *)
Theorem hw_run_output_iff_network (f : Datalog.fact (rel := rel_id)) :
  DistributedHardwareSemantics.hw_run_output prog tries Fwd Inp Outp f <-> network_prog_impl_fact net f.
Proof. split; [apply hw_run_output_to_network | apply network_to_hw_run_output]. Qed.

End OperationalNetworkAdequacy.

(* The per-node matching for the compiled [ninfos]: per-node tries/programs read off [ninfos] are
   exactly [compile_node]'s output ([find_ninfo_node]), so [compile_node_matches] applies.  (Raw
   [Forall2] form -- the hypothesis [hw_run_output_iff_network] needs.) *)
Lemma ninfos_node_rules_match (llayout : lowered_layout_map) (gc : global_context)
    (ninfos0 : list node_info) (ft : node_ftable_map) (dnet : DNet) :
  compile_all_nodes llayout gc = Success ninfos0 ->
  (forall n, Forall bare_rule (lprog_of llayout n)) ->
  dnet.(DistributedDatalog.layout) = (fun n => lprog_of llayout n) ->
  forall n, Forall2 (hw_rule_matches ((find_ninfo (attach_forwarding_tables ninfos0 ft) n).(ntries))
                       (fun _ _ _ => False))
              (dnet.(DistributedDatalog.layout) n)
              ((find_ninfo (attach_forwarding_tables ninfos0 ft) n).(nprogram)).
Proof.
  intros Hcan Hbare Hlay n. rewrite Hlay. cbv beta.
  destruct (compile_node_lprog_of llayout gc ninfos0 n Hcan) as [ninfo Hcn].
  destruct (find_ninfo_node llayout gc ninfos0 ft n Hcan) as [Htr Hpr].
  rewrite Hcn in Htr, Hpr. cbn in Htr, Hpr. rewrite Htr, Hpr.
  apply (compile_node_matches n (lprog_of llayout n) gc ninfo (fun _ _ _ => False) (Hbare n) Hcn).
Qed.

(* Pin [run_ninfos]'s node-equality implicit to this section's [node_id_eqb] (a plain implicit Coq
   can't otherwise infer). *)
Local Notation run_ninfos := (@DistributedHardwareSemantics.run_ninfos _ _ node_id_eqb _) (only parsing).

(* DISTRIBUTED CORRECTNESS, [ninfos]-direct: the OPERATIONAL run of the compiler's returned
   [ninfos = attach_forwarding_tables ninfos0 ft] (each node's program/tries/forwarding read straight
   out of its [node_info]) derives EXACTLY the facts [program] derives from [Q].  Per-node matching
   via [ninfos_node_rules_match]; operational<->network via [hw_run_output_iff_network];
   network<->[prog_impl_fact] via [soundness]/[completeness] (good_network_streaming transported from
   the [fwd_list]-based [base], pointwise-equal forwarding [forward_of_ninfos_eq]). *)
Theorem compile_all_distributes_ninfos (llayout : lowered_layout_map) (gc : global_context)
    (ninfos0 : list node_info) (ft : node_ftable_map) (base : DNet)
    (program : list (Datalog.rule (rel := rel_id) (fn := nat)))
    (Q : Datalog.fact (rel := rel_id) -> Prop) :
  compile_all_nodes llayout gc = Success ninfos0 ->
  bare_layoutb llayout = true ->
  base.(DistributedDatalog.layout) = (fun n => lprog_of llayout n) ->
  base.(DistributedDatalog.forward) = fwd_list ft ->
  good_network_streaming base program Q ->
  forall f, run_ninfos (attach_forwarding_tables ninfos0 ft)
              (base.(DistributedDatalog.input)) (base.(DistributedDatalog.output)) f
            <-> DistributedDatalog.prog_impl_fact program Q f.
Proof.
  intros Hcan Hbare Hbaselay Hbasefwd Hgood f.
  (* good_network_streaming transports to the [ninfos]-forwarded net (forwarding is pointwise equal). *)
  assert (Hgood' : good_network_streaming (dnet_of_ninfos (attach_forwarding_tables ninfos0 ft) base) program Q).
  { apply (good_network_streaming_forward_ext base
             (dnet_of_ninfos (attach_forwarding_tables ninfos0 ft) base) program Q);
      [reflexivity | reflexivity | reflexivity | reflexivity | | exact Hgood].
    intros a r. cbn. rewrite Hbasefwd. symmetry. exact (forward_of_ninfos_eq ninfos0 ft a r). }
  unfold DistributedHardwareSemantics.run_ninfos, DistributedHardwareSemantics.node_prog, DistributedHardwareSemantics.node_tries.
  (* operational run with [forward_from_ninfos] == with [forward_of_ninfos] (pointwise equal) ... *)
  apply (iff_trans
           (DistributedHardwareSemantics.hw_run_output_forward_ext
              (fun n => (find_ninfo (attach_forwarding_tables ninfos0 ft) n).(nprogram))
              (fun n => (find_ninfo (attach_forwarding_tables ninfos0 ft) n).(ntries))
              (DistributedHardwareSemantics.forward_from_ninfos (attach_forwarding_tables ninfos0 ft))
              (forward_of_ninfos (attach_forwarding_tables ninfos0 ft))
              (base.(DistributedDatalog.input)) (base.(DistributedDatalog.output)) f
              (fun _ _ => eq_refl))).
  (* ... == network derivability of the [ninfos]-forwarded net ... *)
  apply (iff_trans
           (hw_run_output_iff_network (dnet_of_ninfos (attach_forwarding_tables ninfos0 ft) base)
              (fun n => (find_ninfo (attach_forwarding_tables ninfos0 ft) n).(nprogram))
              (fun n => (find_ninfo (attach_forwarding_tables ninfos0 ft) n).(ntries))
              (ninfos_node_rules_match llayout gc ninfos0 ft
                 (dnet_of_ninfos (attach_forwarding_tables ninfos0 ft) base) Hcan
                 (bare_layoutb_spec llayout Hbare) Hbaselay)
              f)).
  (* ... == [prog_impl_fact] of the program ([soundness] / [completeness]). *)
  split.
  - intros Hnet. destruct Hgood' as [_ [Hgl [_ [_ [HinQ _]]]]].
    exact (soundness (dnet_of_ninfos (attach_forwarding_tables ninfos0 ft) base) program Q f HinQ Hgl Hnet).
  - intros Hprog.
    exact (completeness (dnet_of_ninfos (attach_forwarding_tables ninfos0 ft) base) program Q Hgood' f Hprog).
Qed.

(* THE TOP THEOREM: with the layout's [canonical_program] as reference and base facts [Q] entering at
   the declared fact-producer locations, a SUCCESSFUL compile (plus a bareness check and a node-validity
   check on the renamed layout, and that [Q] is the declared EDB) makes the hardware network read
   DIRECTLY off the compiler's returned [ninfos] (per-node tries/programs and per-node forwarding all
   read back out of [ninfos] -- no re-derivation) derive EXACTLY the reference [Datalog.prog_impl]
   facts.  Producer AND input routing are correct by construction (gated inside [compile]); there is
   NO route checker side condition. *)
Theorem compile_distributed_correct
    (layout : layout_map) (fps fcs : fact_locations) (g : node_graph)
    (ninfos : list node_info) (llayout : lowered_layout_map) (lfp lfc : lowered_fact_locations)
    (gcontext : global_context) (Q : Datalog.fact (rel := rel_id) -> Prop) :
  lower_inputs layout fps fcs = Success (llayout, lfp, lfc, gcontext) ->
  compile layout fps fcs g = Success ninfos ->
  bare_layoutb llayout = true ->
  edb_routable lfp Q ->
  forall f, run_ninfos ninfos
              (fun n f0 => Q f0 /\ In n (rel_locs lfp (Datalog.rel_of f0)))
              (fun n R => In n (rel_locs lfc R))
              f
            <-> Datalog.prog_impl (canonical_program llayout) Q f.
Proof.
  intros Hlow Hcomp Hbare HQ f.
  destruct (compile_success_extract layout fps fcs g ninfos llayout lfp lfc gcontext Hlow Hcomp)
    as [ninfos0 [ftables [Hret [Hcan [Hft [Hinp [Houtp [Hinoutp [Hgraph Hkeys]]]]]]]]].
  destruct (generate_forwarding_table_checked_success (collect_global_dependencies llayout lfp lfc gcontext)
              ninfos0 g llayout ftables Hft) as [Hfteq Hroutes].
  (* the returned [ninfos] IS [attach_forwarding_tables ninfos0 ftables]; [ftables] IS the generated
     table.  The operational run of [ninfos] over the compiled EDB equals [prog_impl_fact] of the
     canonical program ([compile_all_distributes_ninfos]), which is the reference [Datalog.prog_impl]
     on the bare fragment ([prog_impl_fact_iff_datalog]). *)
  rewrite Hret. rewrite Hfteq.
  apply (iff_trans
           (compile_all_distributes_ninfos llayout
              (collect_global_dependencies llayout lfp lfc gcontext) ninfos0
              (generate_forwarding_table (collect_global_dependencies llayout lfp lfc gcontext) ninfos0 g )
              (dnet_of_llayout llayout
                 (compiled_base_edb g (generate_forwarding_table (collect_global_dependencies llayout lfp lfc gcontext) ninfos0 g )
                    lfp lfc Q))
              (canonical_program llayout) Q Hcan Hbare
              eq_refl eq_refl
              (compiled_good_network_streaming_edb g (collect_global_dependencies llayout lfp lfc gcontext) ninfos0
                 llayout lfp lfc
                 (canonical_program llayout) Q
                 (proj1 (check_graph_correct g) Hgraph)
                 (canonical_good_layout g llayout Hkeys)
                 Hroutes
                 Hinp Houtp Hinoutp HQ)
              f)).
  apply prog_impl_fact_iff_datalog. apply canonical_bare. exact Hbare.
Qed.

(*========================================================================================*)
(*  ORIGINAL-NAME top theorem: the iff stated over the source [rel]/[fn], via the relabel  *)
(*  bridge [RelabelCorrect.prog_impl_relabel].  The compiler lowers [rel] -> [rel_id]; the   *)
(*  bridge transports derivability back to the original names.                             *)
(*========================================================================================*)

(* The source-side function signature (the numeric/lowered side uses [sig]; bare programs never
   invoke [interp_fun], so this is only needed to TYPE [Datalog.prog_impl] over the source [fn]). *)
Context {sig_src : signature fn aggregator T}.

(* The relation/function relabelings the compiler's global context [gc] induces (lookups in its
   [rel_map]/[fn_map]), and [Sdom gc] = the relations [gc] actually collected (the [rel_map] domain).
   [prog_impl_relabel] is applied with [rho := rho_gc gc], [iota := fn_to_id], [S := Sdom gc]. *)
(* Out-of-domain relations rename to the FRESH [last_rel_id] -- which, by [RelInv], is strictly above
   every collected id, so it collides with no real relation (and no producer/input node).  This is what
   lets the routing side condition [edb_routable] absorb the "inputs are in scope" condition: an
   out-of-scope input fact renames to a relation nothing routes, so it simply can't enter the network. *)
Definition rho_gc (gc : global_context) (r : rel) : rel_id :=
  match map.get gc.(DistributedDatalogToHardwareCompiler.rel_map) r with
  | Some id => id
  | None => gc.(DistributedDatalogToHardwareCompiler.last_rel_id)
  end.
Definition Sdom (gc : global_context) (r : rel) : Prop :=
  exists id, map.get gc.(DistributedDatalogToHardwareCompiler.rel_map) r = Some id.

(* A fact is IN SCOPE for a compiled program when its relation was collected from the layout (i.e. the
   program actually mentions it).  Facts over relations no rule uses can't be named, routed, or queried
   by the compiled network, so the query and the streamed EDB must stay within scope. *)
Definition fact_in_domain (gc : global_context) (f : Datalog.fact) : Prop :=
  Sdom gc (Datalog.rel_of f).

Definition facts_in_domain (gc : global_context) (Q : Datalog.fact -> Prop) : Prop :=
  forall h, Q h -> fact_in_domain gc h.

(*========================================================================================*)
(*  B2: the collected relation map is INJECTIVE on its domain -- a PROVEN property of        *)
(*  [collect_global_names_layout], not an assumption.  Discharges the injectivity hypothesis  *)
(*  of [compile_distributed_correct_source].                                                  *)
(*========================================================================================*)

Context {rel_relid_map_ok : map.ok rel_relid_map}.
Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.

Local Notation rmap := DistributedDatalogToHardwareCompiler.rel_map.
Local Notation rlast := DistributedDatalogToHardwareCompiler.last_rel_id.

(* invariant maintained by [collect_global_names_*]: the relation map is injective AND every assigned
   id is below the next-id counter (so a fresh [last_rel_id] collides with nothing). *)
Definition RelInv (gc : global_context) : Prop :=
  (forall r1 r2 i, map.get gc.(rmap) r1 = Some i -> map.get gc.(rmap) r2 = Some i -> r1 = r2)
  /\ (forall r i, map.get gc.(rmap) r = Some i -> i < gc.(rlast)).

Lemma RelInv_initial : RelInv initial_global_context.
Proof.
  split; cbn; intros; [rewrite map.get_empty in *; discriminate
                      | rewrite map.get_empty in *; discriminate].
Qed.

(* the only relation-side update preserves the invariant (fresh id, bounded). *)
Lemma update_with_rel_RelInv (r : rel) (gc : global_context) :
  RelInv gc -> RelInv (update_global_context_with_rel r gc).
Proof.
  intros [Hinj Hbnd]. unfold DistributedDatalogToHardwareCompiler.update_global_context_with_rel.
  destruct (map.get gc.(rmap) r) eqn:Hget; [split; assumption|].
  unfold RelInv; cbn [DistributedDatalogToHardwareCompiler.rel_map DistributedDatalogToHardwareCompiler.last_rel_id]; split.
  - intros r1 r2 i H1 H2.
    destruct (rel_eqb_spec r1 r) as [-> | Hne1]; destruct (rel_eqb_spec r2 r) as [-> | Hne2].
    + reflexivity.
    + rewrite map.get_put_same in H1. rewrite map.get_put_diff in H2 by assumption.
      injection H1 as <-. apply Hbnd in H2. exfalso; lia.
    + rewrite map.get_put_diff in H1 by assumption. rewrite map.get_put_same in H2.
      injection H2 as <-. apply Hbnd in H1. exfalso; lia.
    + rewrite map.get_put_diff in H1 by assumption.
      rewrite map.get_put_diff in H2 by assumption. exact (Hinj r1 r2 i H1 H2).
  - intros r1 i H.
    destruct (rel_eqb_spec r1 r) as [-> | Hne1].
    + rewrite map.get_put_same in H. injection H as <-. lia.
    + rewrite map.get_put_diff in H by assumption. apply Hbnd in H. lia.
Qed.

(* [RelInv] only reads the relation side, so it transfers along rel-side equalities. *)
Lemma RelInv_rel_eq (gc gc' : global_context) :
  gc'.(rmap) = gc.(rmap) -> gc'.(rlast) = gc.(rlast) -> RelInv gc -> RelInv gc'.
Proof. intros Hm Hl HR. unfold RelInv in HR |- *. rewrite Hm, Hl. exact HR. Qed.

(* generic: a [fold_left] of rel-side-preserving steps is rel-side-preserving. *)
Lemma fold_left_rel_eq {A} (gstep : global_context -> A -> global_context) (l : list A) :
  (forall gc a, In a l -> (gstep gc a).(rmap) = gc.(rmap) /\ (gstep gc a).(rlast) = gc.(rlast)) ->
  forall gc, (fold_left gstep l gc).(rmap) = gc.(rmap) /\ (fold_left gstep l gc).(rlast) = gc.(rlast).
Proof.
  induction l as [| a l IH]; intros Hstep gc; cbn; [split; reflexivity|].
  destruct (Hstep gc a (or_introl eq_refl)) as [Hm Hl].
  destruct (IH (fun gc' a' Hin => Hstep gc' a' (or_intror Hin)) (gstep gc a)) as [Hm' Hl'].
  rewrite Hm', Hl', Hm, Hl. split; reflexivity.
Qed.

(* generic [fold_left] of [RelInv]-preservers preserves [RelInv]. *)
Lemma fold_left_RelInv {A} (gstep : global_context -> A -> global_context) (l : list A) :
  (forall gc a, In a l -> RelInv gc -> RelInv (gstep gc a)) ->
  forall gc, RelInv gc -> RelInv (fold_left gstep l gc).
Proof.
  induction l as [| a l IH]; intros Hstep gc HR; cbn; [exact HR|].
  apply (IH (fun gc' a' Hin => Hstep gc' a' (or_intror Hin))).
  exact (Hstep gc a (or_introl eq_refl) HR).
Qed.

Lemma collect_fact_RelInv (f : clause) (gc : global_context) :
  RelInv gc -> RelInv (collect_global_names_fact f gc).
Proof.
  intros HR. unfold DistributedDatalogToHardwareCompiler.collect_global_names_fact.
  apply update_with_rel_RelInv. exact HR.
Qed.

Lemma collect_rule_RelInv (r : rule) (gc : global_context) :
  RelInv gc -> RelInv (collect_global_names_rule r gc).
Proof.
  intros HR. destruct r as [concls hyps | mcs mhs | cr agg hr];
    cbn [DistributedDatalogToHardwareCompiler.collect_global_names_rule]; [| exact HR | exact HR].
  apply (fold_left_RelInv (fun acc f => collect_global_names_fact f acc) concls
           (fun gc' a _ HR' => collect_fact_RelInv a gc' HR')).
  apply (fold_left_RelInv (fun acc f => collect_global_names_fact f acc) hyps
           (fun gc' a _ HR' => collect_fact_RelInv a gc' HR')).
  exact HR.
Qed.

Lemma collect_program_RelInv (p : program) (gc : global_context) :
  RelInv gc -> RelInv (collect_global_names_program p gc).
Proof.
  intros HR. unfold DistributedDatalogToHardwareCompiler.collect_global_names_program.
  apply (fold_left_RelInv (fun acc r => collect_global_names_rule r acc) p
           (fun gc' a _ HR' => collect_rule_RelInv a gc' HR')).
  exact HR.
Qed.

Lemma collect_layout_RelInv (layout : layout_map) (gc : global_context) :
  RelInv gc -> RelInv (collect_global_names_layout layout gc).
Proof.
  intros HR. unfold DistributedDatalogToHardwareCompiler.collect_global_names_layout.
  apply (map.fold_spec (fun (m : layout_map) (acc : global_context) => RelInv acc)); [exact HR|].
  intros k v m acc Hget IH. apply collect_program_RelInv. exact IH.
Qed.

Lemma collect_global_names_RelInv (layout : layout_map) :
  RelInv (collect_global_names_layout layout initial_global_context).
Proof. apply collect_layout_RelInv. exact RelInv_initial. Qed.

(* B2 RESULT (core): the relation map collected from a layout is injective on its domain. *)
Lemma rho_gc_injective_collect (layout : layout_map) (r1 r2 : rel) :
  Sdom (collect_global_names_layout layout initial_global_context) r1 ->
  Sdom (collect_global_names_layout layout initial_global_context) r2 ->
  rho_gc (collect_global_names_layout layout initial_global_context) r1
    = rho_gc (collect_global_names_layout layout initial_global_context) r2 ->
  r1 = r2.
Proof.
  intros [i1 H1] [i2 H2] Heq. unfold rho_gc in Heq. rewrite H1, H2 in Heq. cbn in Heq. subst i2.
  exact (proj1 (collect_global_names_RelInv layout) r1 r2 i1 H1 H2).
Qed.

(*========================================================================================*)
(*  B3: [global_rename_*] IS the clean [relabel_*] on the bare fragment (names present).    *)
(*  Discharges the relabel-equality hypothesis -- "the renaming pass preserves meaning".     *)
(*========================================================================================*)

(*----[all_success (map ..)] helpers----*)
(* The renamers build their lists with [List.all_success (List.map g ..)], so the correspondences
   below carry NO [rev].  [all_success_eq_map_Success] (proved earlier) is the underlying fact. *)

(* forward: pointwise [Success (h x)] lifts to the whole list. *)
Lemma all_success_map_pointwise {A B} (g : A -> result B) (h : A -> B) (xs : list A) :
  (forall x, In x xs -> g x = Success (h x)) ->
  List.all_success (List.map g xs) = Success (List.map h xs).
Proof.
  induction xs as [|x xs IH]; intros Hg; cbn; [reflexivity|].
  rewrite (Hg x (or_introl eq_refl)); cbn.
  rewrite (IH (fun x' Hin => Hg x' (or_intror Hin))); reflexivity.
Qed.

(* reverse: a [Success] result means every element succeeded, with any property of the whole
   result holding of each per-element success. *)
Lemma all_success_map_inv_forall {A B} (g : A -> result B) (P : B -> Prop) :
  forall (xs : list A) (res : list B),
    List.all_success (List.map g xs) = Success res -> Forall P res ->
    Forall (fun x => exists y, g x = Success y /\ P y) xs.
Proof.
  induction xs as [|x xs IH]; intros res Hall Hres; cbn in Hall.
  - constructor.
  - destruct (g x) as [y|msg] eqn:Hgx; cbn in Hall; [|discriminate].
    destruct (List.all_success (List.map g xs)) as [res'|msg] eqn:Hrest; cbn in Hall; [|discriminate].
    injection Hall as <-. inversion Hres as [|? ? Hy Hres']; subst.
    constructor; [exists y; split; [exact Hgx | exact Hy] | exact (IH res' eq_refl Hres')].
Qed.

(* forward, property-preserving: if [g] sends [P]-inputs to [Q]-outputs on [Success]. *)
Lemma all_success_map_forall_pres {A B} (g : A -> result B) (P : A -> Prop) (Q : B -> Prop) :
  (forall x y, P x -> g x = Success y -> Q y) ->
  forall (xs : list A) (res : list B),
    Forall P xs -> List.all_success (List.map g xs) = Success res -> Forall Q res.
Proof.
  intros Hg. induction xs as [|x xs IH]; intros res Hxs Hall; cbn in Hall.
  - injection Hall as <-. constructor.
  - inversion Hxs as [|? ? HPx HPxs]; subst.
    destruct (g x) as [y|e] eqn:Hgx; cbn in Hall; [|discriminate].
    destruct (List.all_success (List.map g xs)) as [res'|e] eqn:Hrest; cbn in Hall; [|discriminate].
    injection Hall as <-. constructor; [exact (Hg x y HPx Hgx) | exact (IH res' HPxs eq_refl)].
Qed.

Lemma global_rename_rel_eq (gc : global_context) (R : rel) :
  Sdom gc R -> global_rename_rel R gc = Success (rho_gc gc R).
Proof.
  intros [id Hid]. unfold DistributedDatalogToHardwareCompiler.global_rename_rel, rho_gc.
  rewrite Hid. reflexivity.
Qed.

Lemma global_rename_expr_bare (gc : global_context) (e : Datalog.expr) :
  RelabelCorrect.bare_expr e ->
  global_rename_expr fn_to_id e gc = Success (RelabelCorrect.relabel_expr fn_to_id e).
Proof. intros [v ->]. reflexivity. Qed.

Lemma global_rename_fact_eq (gc : global_context) (f : clause) :
  RelabelCorrect.bare_clause f -> Sdom gc f.(Datalog.clause_rel) ->
  global_rename_fact fn_to_id f gc = Success (RelabelCorrect.relabel_clause (rho_gc gc) fn_to_id f).
Proof.
  intros Hbare HS. unfold DistributedDatalogToHardwareCompiler.global_rename_fact.
  rewrite (global_rename_rel_eq gc f.(Datalog.clause_rel) HS).
  erewrite all_success_map_pointwise; [reflexivity|].
  intros x Hin. apply global_rename_expr_bare.
  exact (proj1 (Forall_forall _ _) Hbare x Hin).
Qed.

Lemma global_rename_rule_eq (gc : global_context) (r : rule) :
  RelabelCorrect.bare_rule r -> RelabelCorrect.Srule (Sdom gc) r ->
  global_rename_rule fn_to_id r gc = Success (RelabelCorrect.relabel_rule (rho_gc gc) (fn_to_id) r).
Proof.
  intros Hbare HS. destruct r as [concls hyps | mcs mhs | cr agg hr];
    cbn [RelabelCorrect.bare_rule] in Hbare; [| contradiction | contradiction].
  destruct Hbare as [Hbc Hbh]. cbn [RelabelCorrect.Srule] in HS. destruct HS as [HSc HSh].
  unfold DistributedDatalogToHardwareCompiler.global_rename_rule.
  rewrite (all_success_map_pointwise (fun f => global_rename_fact fn_to_id f gc)
             (fun f => RelabelCorrect.relabel_clause (rho_gc gc) (fn_to_id) f) hyps
             (fun f Hin => global_rename_fact_eq gc f
                (proj1 (Forall_forall _ _) Hbh f Hin) (proj1 (Forall_forall _ _) HSh f Hin))).
  rewrite (all_success_map_pointwise (fun f => global_rename_fact fn_to_id f gc)
             (fun f => RelabelCorrect.relabel_clause (rho_gc gc) (fn_to_id) f) concls
             (fun f Hin => global_rename_fact_eq gc f
                (proj1 (Forall_forall _ _) Hbc f Hin) (proj1 (Forall_forall _ _) HSc f Hin))).
  reflexivity.
Qed.

Lemma global_rename_program_eq (gc : global_context) (p : program) :
  RelabelCorrect.bare_program p -> RelabelCorrect.Sprogram (Sdom gc) p ->
  global_rename_program p gc = Success (RelabelCorrect.relabel_program (rho_gc gc) (fn_to_id) p).
Proof.
  intros Hbare HS. unfold DistributedDatalogToHardwareCompiler.global_rename_program.
  rewrite (all_success_map_pointwise (fun r => global_rename_rule fn_to_id r gc)
             (fun r => RelabelCorrect.relabel_rule (rho_gc gc) (fn_to_id) r) p
             (fun r Hin => global_rename_rule_eq gc r
                (proj1 (Forall_forall _ _) Hbare r Hin) (proj1 (Forall_forall _ _) HS r Hin))).
  reflexivity.
Qed.

(*========================================================================================*)
(*  B3 (reverse): bareness REFLECTS back through the rename.  Renaming maps [var_expr] to    *)
(*  [var_expr] and [fun_expr] to [fun_expr], so if the RENAMED rule is bare, the SOURCE rule  *)
(*  was already bare.  Hence [bare_layoutb] on the renamed layout already proves the source    *)
(*  program bare -- the explicit [bare_program (source_program ...)] hypothesis is redundant.   *)
(*========================================================================================*)

(* renaming a [fun_expr] yields a [fun_expr], so a renamed [var_expr] came from a [var_expr]. *)
Lemma grn_expr_reflect (gc : global_context) (e : Datalog.expr) (le : lowered_expr) :
  global_rename_expr fn_to_id e gc = Success le -> (exists v, le = var_expr v) -> (exists v, e = var_expr v).
Proof.
  destruct e as [v | f0 args]; intros Hren Hle; [exists v; reflexivity|].
  exfalso. cbn in Hren.
  match type of Hren with context[List.all_success ?x] =>
    destruct (List.all_success x) as [rargs | msg]; [| discriminate] end.
  injection Hren as <-. destruct Hle as [v Hv]. discriminate.
Qed.

Lemma grn_fact_reflect (gc : global_context) (f : clause) (lf : lowered_fact) :
  global_rename_fact fn_to_id f gc = Success lf -> bare_fact lf -> RelabelCorrect.bare_clause f.
Proof.
  unfold DistributedDatalogToHardwareCompiler.global_rename_fact. intros Hren Hbare.
  destruct (global_rename_rel f.(Datalog.clause_rel) gc) as [rid | msg]; [| discriminate].
  match type of Hren with context[List.all_success ?x] =>
    destruct (List.all_success x) as [rargs | msg] eqn:Hall; [| discriminate] end.
  injection Hren as <-. unfold bare_fact in Hbare. cbn in Hbare.
  pose proof (all_success_map_inv_forall (fun arg => global_rename_expr fn_to_id arg gc)
              (fun le => exists v, le = var_expr v) f.(Datalog.clause_args) rargs Hall Hbare) as Hargs.
  unfold RelabelCorrect.bare_clause. apply Forall_forall. intros e He.
  rewrite Forall_forall in Hargs. destruct (Hargs e He) as [le [Hgle Hvle]].
  exact (grn_expr_reflect gc e le Hgle Hvle).
Qed.

Lemma grn_rule_reflect (gc : global_context) (r : rule) (lr : lowered_rule) :
  global_rename_rule fn_to_id r gc = Success lr -> bare_rule lr -> RelabelCorrect.bare_rule r.
Proof.
  intros Hren Hbare. destruct r as [concls hyps | mcs mhs | cr agg hr];
    cbn [DistributedDatalogToHardwareCompiler.global_rename_rule] in Hren;
    [| discriminate | discriminate].
  match type of Hren with context[List.all_success (List.map ?ff hyps)] =>
    destruct (List.all_success (List.map ff hyps)) as [lhyps | msg] eqn:Hfh; [| discriminate] end.
  match type of Hren with context[List.all_success (List.map ?ff concls)] =>
    destruct (List.all_success (List.map ff concls)) as [lconcls | msg] eqn:Hfc; [| discriminate] end.
  injection Hren as <-. cbn [bare_rule] in Hbare. destruct Hbare as [Hbh Hbc].
  pose proof (all_success_map_inv_forall (fun f => global_rename_fact fn_to_id f gc) bare_fact hyps lhyps Hfh Hbh) as Hhyps.
  pose proof (all_success_map_inv_forall (fun f => global_rename_fact fn_to_id f gc) bare_fact concls lconcls Hfc Hbc) as Hconcls.
  cbn [RelabelCorrect.bare_rule]. split.
  - apply Forall_forall. intros f Hf. rewrite Forall_forall in Hconcls.
    destruct (Hconcls f Hf) as [lf [Hglf Hblf]]. exact (grn_fact_reflect gc f lf Hglf Hblf).
  - apply Forall_forall. intros f Hf. rewrite Forall_forall in Hhyps.
    destruct (Hhyps f Hf) as [lf [Hglf Hblf]]. exact (grn_fact_reflect gc f lf Hglf Hblf).
Qed.

Lemma grn_program_reflect (gc : global_context) (p : program) (lp : lowered_program) :
  global_rename_program p gc = Success lp -> Forall bare_rule lp -> RelabelCorrect.bare_program p.
Proof.
  unfold DistributedDatalogToHardwareCompiler.global_rename_program. intros Hren Hbare.
  match type of Hren with context[List.all_success ?x] =>
    destruct (List.all_success x) as [lrs | msg] eqn:Hall; [| discriminate] end.
  injection Hren as <-.
  pose proof (all_success_map_inv_forall (fun r => global_rename_rule fn_to_id r gc) bare_rule p lrs Hall Hbare) as Hp.
  unfold RelabelCorrect.bare_program. apply Forall_forall. intros r Hr.
  rewrite Forall_forall in Hp. destruct (Hp r Hr) as [lr [Hglr Hblr]]. exact (grn_rule_reflect gc r lr Hglr Hblr).
Qed.

(* A bare program has no meta conclusions, so [prog_impl] is invariant under reordering/duplication
   of rules -- it depends only on the rule SET. *)
Lemma bare_meta_concl_rels_nil (p : list (Datalog.rule (rel := rel_id) (fn := nat))) :
  RelabelCorrect.bare_program p -> flat_map Datalog.meta_concl_rels p = [].
Proof.
  intros H. induction p as [| r p IH]; cbn; [reflexivity|].
  inversion H as [| r0 p0 Hr Hp]; subst.
  destruct r as [cs hs | | ]; cbn [RelabelCorrect.bare_rule] in Hr; [| contradiction | contradiction].
  cbn [Datalog.meta_concl_rels]. apply IH. exact Hp.
Qed.

Lemma prog_impl_set_iff (p1 p2 : list (Datalog.rule (rel := rel_id) (fn := nat)))
    (Q : Datalog.fact (rel := rel_id) -> Prop) (f : Datalog.fact (rel := rel_id)) :
  RelabelCorrect.bare_program p1 -> RelabelCorrect.bare_program p2 ->
  incl p1 p2 -> incl p2 p1 ->
  (Datalog.prog_impl p1 Q f <-> Datalog.prog_impl p2 Q f).
Proof.
  intros Hb1 Hb2 H12 H21. split; intros H.
  - apply (Datalog.prog_impl_subset p1 p2 Q f H12); [| exact H].
    intros r _. right. rewrite (bare_meta_concl_rels_nil p1 Hb1). intros x [].
  - apply (Datalog.prog_impl_subset p2 p1 Q f H21); [| exact H].
    intros r _. right. rewrite (bare_meta_concl_rels_nil p2 Hb2). intros x [].
Qed.

(* The source reference program (the canonical union of the ORIGINAL layout's per-node programs, over
   [rel]/[fn]) and the layout-distributes-a-program checker now live in the compiler file; alias them. *)
Notation source_program :=
  (@DistributedDatalogToHardwareCompiler.source_program rel var fn aggregator node_id layout_map).
Notation layout_distributes_program :=
  (@DistributedDatalogToHardwareCompiler.layout_distributes_program rel var fn aggregator node_id layout_map).
Notation layout_distributes_programb :=
  (@DistributedDatalogToHardwareCompiler.layout_distributes_programb rel var fn aggregator node_id layout_map).

Lemma source_program_in (layout : layout_map) (r : rule) :
  In r (source_program layout) <-> exists n p, map.get layout n = Some p /\ In r p.
Proof.
  unfold DistributedDatalogToHardwareCompiler.source_program.
  apply (map.fold_spec
    (fun (m : layout_map) (acc : list (rule)) =>
       In r acc <-> exists n p, map.get m n = Some p /\ In r p)).
  - split; [intros [] | intros [n [p [Hget _]]]; rewrite map.get_empty in Hget; discriminate].
  - intros k v m acc Hgmk IH. rewrite in_app_iff. split.
    + intros [Hacc | Hv].
      * apply IH in Hacc. destruct Hacc as [n [p [Hget Hin]]].
        exists n, p. split; [|exact Hin]. rewrite map.get_put_diff; [exact Hget|].
        intros ->. rewrite Hgmk in Hget. discriminate.
      * exists k, v. split; [apply map.get_put_same | exact Hv].
    + intros [n [p [Hget Hin]]].
      destruct (eqb_boolspec _ n k) as [->|Hne].
      * rewrite map.get_put_same in Hget. injection Hget as <-. right. exact Hin.
      * rewrite map.get_put_diff in Hget by congruence. left. apply IH. exists n, p. auto.
Qed.


Lemma global_rename_rule_layout_spec_bwd (layout : layout_map) (gc : global_context)
    (llayout : lowered_layout_map) (node : node_id) (orig : program) :
  global_rename_rule_layout layout gc = Success llayout ->
  map.get layout node = Some orig ->
  exists lp, global_rename_program orig gc = Success lp /\ map.get llayout node = Some lp.
Proof.
  intros H Hget. unfold DistributedDatalogToHardwareCompiler.global_rename_rule_layout in H.
  exact (map.try_map_values_fw _ layout llayout H node orig Hget).
Qed.

(* [bare_layoutb] on the renamed layout already proves the SOURCE program bare -- so the explicit
   [bare_program (source_program ...)] hypothesis is redundant given the layoutb check. *)
Lemma source_bare_of_layoutb (layout : layout_map) (gc : global_context) (llayout : lowered_layout_map) :
  global_rename_rule_layout layout gc = Success llayout ->
  bare_layoutb llayout = true ->
  RelabelCorrect.bare_program (source_program layout).
Proof.
  intros Hgr Hbl. unfold RelabelCorrect.bare_program. apply Forall_forall. intros r Hr.
  apply source_program_in in Hr. destruct Hr as [n [orig [Hgetlayout Hrin]]].
  destruct (global_rename_rule_layout_spec_bwd layout gc llayout n orig Hgr Hgetlayout) as [lp [Hgrp Hgetll]].
  pose proof (bare_layoutb_entry llayout Hbl n lp Hgetll) as Hlp.
  assert (Hlpbare : Forall bare_rule lp).
  { apply Forall_forall. intros lr Hlr. apply bare_ruleb_spec.
    rewrite forallb_forall in Hlp. apply Hlp. exact Hlr. }
  exact (proj1 (Forall_forall _ _) (grn_program_reflect gc orig lp Hgrp Hlpbare) r Hrin).
Qed.

(* each node's source program inherits bareness / scopedness from the canonical source program. *)
Lemma layout_program_bare (layout : layout_map) (n : node_id) (orig : program) :
  RelabelCorrect.bare_program (source_program layout) -> map.get layout n = Some orig ->
  RelabelCorrect.bare_program orig.
Proof.
  intros Hb Hget. unfold RelabelCorrect.bare_program in *. apply Forall_forall. intros r Hr.
  rewrite Forall_forall in Hb. apply Hb. apply source_program_in. exists n, orig. split; assumption.
Qed.

Lemma layout_program_scoped (layout : layout_map) (gc : global_context) (n : node_id) (orig : program) :
  RelabelCorrect.Sprogram (Sdom gc) (source_program layout) -> map.get layout n = Some orig ->
  RelabelCorrect.Sprogram (Sdom gc) orig.
Proof.
  intros HS Hget. unfold RelabelCorrect.Sprogram in *. apply Forall_forall. intros r Hr.
  rewrite Forall_forall in HS. apply HS. apply source_program_in. exists n, orig. split; assumption.
Qed.

(* B3c: the compiled canonical (numeric) program is exactly the RELABEL of the source program,
   AS A RULE SET (so [prog_impl_set_iff] can swap them). *)
Lemma canonical_renamed_eq_relabel_source (layout : layout_map)
    (llayout : lowered_layout_map) (r : Datalog.rule (rel := rel_id) (fn := nat)) :
  global_rename_rule_layout layout (collect_global_names_layout layout initial_global_context) = Success llayout ->
  RelabelCorrect.bare_program (source_program layout) ->
  RelabelCorrect.Sprogram (Sdom (collect_global_names_layout layout initial_global_context)) (source_program layout) ->
  (In r (canonical_program llayout) <->
   In r (RelabelCorrect.relabel_program
           (rho_gc (collect_global_names_layout layout initial_global_context))
           (fn_to_id) (source_program layout))).
Proof.
  intros Hgr Hbare HS.
  set (gc0 := collect_global_names_layout layout initial_global_context) in *.
  split.
  - intros Hin. apply canonical_program_in in Hin. destruct Hin as [n [lp [Hgetll Hinlp]]].
    destruct (global_rename_rule_layout_spec layout gc0 llayout n lp Hgr Hgetll)
      as [orig [Hgetlayout Hgrp]].
    rewrite (global_rename_program_eq gc0 orig (layout_program_bare layout n orig Hbare Hgetlayout)
               (layout_program_scoped layout gc0 n orig HS Hgetlayout)) in Hgrp.
    injection Hgrp as Hlp. subst lp.
    unfold RelabelCorrect.relabel_program in Hinlp. apply in_map_iff in Hinlp.
    destruct Hinlp as [r0 [Hr0eq Hr0in]]. subst r.
    unfold RelabelCorrect.relabel_program. apply in_map_iff. exists r0. split; [reflexivity|].
    apply source_program_in. exists n, orig. split; assumption.
  - intros Hin. unfold RelabelCorrect.relabel_program in Hin. apply in_map_iff in Hin.
    destruct Hin as [r0 [Hr0eq Hr0in]]. apply source_program_in in Hr0in.
    destruct Hr0in as [n [orig [Hgetlayout Hr0inorig]]].
    destruct (global_rename_rule_layout_spec_bwd layout gc0 llayout n orig Hgr Hgetlayout)
      as [lp [Hgrp Hgetll]].
    rewrite (global_rename_program_eq gc0 orig (layout_program_bare layout n orig Hbare Hgetlayout)
               (layout_program_scoped layout gc0 n orig HS Hgetlayout)) in Hgrp.
    injection Hgrp as Hlp. subst lp.
    apply canonical_program_in.
    exists n, (RelabelCorrect.relabel_program (rho_gc gc0) (fn_to_id) orig). split; [exact Hgetll|].
    subst r. unfold RelabelCorrect.relabel_program. apply in_map_iff. exists r0. split; [reflexivity | exact Hr0inorig].
Qed.

(* the file's [bare_rule] (hyps/concls) and [RelabelCorrect.bare_rule] (concls/hyps) agree up to the
   conjunction order. *)
Lemma corr_bare_iff_relabel (r : Datalog.rule (rel := rel_id) (fn := nat)) :
  bare_rule r -> RelabelCorrect.bare_rule r.
Proof.
  destruct r as [cs hs | | ]; cbn [bare_rule RelabelCorrect.bare_rule]; [| contradiction | contradiction].
  intros [Hhs Hcs]. split; [exact Hcs | exact Hhs].
Qed.

Lemma canonical_renamed_bare (llayout : lowered_layout_map) :
  bare_layoutb llayout = true ->
  RelabelCorrect.bare_program (canonical_program llayout).
Proof.
  intros Hbl. unfold RelabelCorrect.bare_program. apply Forall_forall. intros r Hr.
  apply corr_bare_iff_relabel.
  exact (proj1 (Forall_forall _ _) (canonical_bare llayout Hbl) r Hr).
Qed.

(*----Discharging source [Sprogram]: every relation in the layout is collected by the rename pass,
  so [Sprogram (Sdom gc0) (source_program layout)] is automatic (not a side condition).----*)

(* generic monotone / covering folds for a [global_context] predicate [Q]. *)
Lemma fold_left_Q_mono {A} (gstep : global_context -> A -> global_context) (Q : global_context -> Prop)
    (l : list A) :
  (forall gc a, Q gc -> Q (gstep gc a)) -> forall gc, Q gc -> Q (fold_left gstep l gc).
Proof.
  intros Hmono. induction l as [| a l IH]; intros gc HQ; cbn; [exact HQ|].
  apply IH. apply Hmono. exact HQ.
Qed.

Lemma fold_left_Q_covers {A} (gstep : global_context -> A -> global_context) (Q : global_context -> Prop)
    (l : list A) (a0 : A) :
  (forall gc a, Q gc -> Q (gstep gc a)) -> (forall gc, Q (gstep gc a0)) ->
  In a0 l -> forall gc, Q (fold_left gstep l gc).
Proof.
  intros Hmono Hadd. induction l as [| a l IH]; [intros [] |]. intros [Heq | Hin] gc; cbn.
  - subst a. apply (fold_left_Q_mono gstep Q l Hmono). apply Hadd.
  - apply IH. exact Hin.
Qed.

Lemma update_with_rel_Sdom (r : rel) (gc : global_context) (R : rel) :
  Sdom gc R -> Sdom (update_global_context_with_rel r gc) R.
Proof.
  unfold Sdom, DistributedDatalogToHardwareCompiler.update_global_context_with_rel.
  destruct (map.get gc.(rmap) r) eqn:Hget; [exact (fun H => H)|].
  cbn [DistributedDatalogToHardwareCompiler.rel_map]. intros [i Hi].
  destruct (rel_eqb_spec R r) as [->|Hne].
  - exists gc.(rlast). apply map.get_put_same.
  - exists i. rewrite map.get_put_diff by congruence. exact Hi.
Qed.

Lemma update_with_rel_adds (r : rel) (gc : global_context) :
  Sdom (update_global_context_with_rel r gc) r.
Proof.
  unfold Sdom, DistributedDatalogToHardwareCompiler.update_global_context_with_rel.
  destruct (map.get gc.(rmap) r) eqn:Hget; [exists r0; exact Hget|].
  cbn [DistributedDatalogToHardwareCompiler.rel_map]. exists gc.(rlast). apply map.get_put_same.
Qed.

Lemma collect_fact_Sdom (f : clause) (gc : global_context) (R : rel) :
  Sdom gc R -> Sdom (collect_global_names_fact f gc) R.
Proof.
  intros H. unfold DistributedDatalogToHardwareCompiler.collect_global_names_fact.
  apply update_with_rel_Sdom. exact H.
Qed.

Lemma collect_fact_adds (f : clause) (gc : global_context) :
  Sdom (collect_global_names_fact f gc) f.(Datalog.clause_rel).
Proof.
  unfold DistributedDatalogToHardwareCompiler.collect_global_names_fact.
  apply update_with_rel_adds.
Qed.

Lemma collect_rule_Sdom (r : rule) (gc : global_context) (R : rel) :
  Sdom gc R -> Sdom (collect_global_names_rule r gc) R.
Proof.
  intros H. destruct r as [cs hs | | ];
    cbn [DistributedDatalogToHardwareCompiler.collect_global_names_rule]; [| exact H | exact H].
  apply (fold_left_Q_mono (fun acc f => collect_global_names_fact f acc) (fun gc' => Sdom gc' R) cs
           (fun gc' a => collect_fact_Sdom a gc' R)).
  apply (fold_left_Q_mono (fun acc f => collect_global_names_fact f acc) (fun gc' => Sdom gc' R) hs
           (fun gc' a => collect_fact_Sdom a gc' R)).
  exact H.
Qed.

Lemma collect_rule_covers (cs hs : list (clause))
    (c : clause) (gc : global_context) :
  In c cs \/ In c hs ->
  Sdom (collect_global_names_rule (@Datalog.normal_rule rel var fn aggregator cs hs) gc) c.(Datalog.clause_rel).
Proof.
  intros Hc. cbn [DistributedDatalogToHardwareCompiler.collect_global_names_rule].
  destruct Hc as [Hcs | Hhs].
  - exact (fold_left_Q_covers (fun acc f => collect_global_names_fact f acc)
             (fun gc' => Sdom gc' c.(Datalog.clause_rel)) cs c
             (fun gc' a => collect_fact_Sdom a gc' c.(Datalog.clause_rel))
             (fun gc' => collect_fact_adds c gc') Hcs _).
  - apply (fold_left_Q_mono (fun acc f => collect_global_names_fact f acc)
             (fun gc' => Sdom gc' c.(Datalog.clause_rel)) cs
             (fun gc' a => collect_fact_Sdom a gc' c.(Datalog.clause_rel))).
    exact (fold_left_Q_covers (fun acc f => collect_global_names_fact f acc)
             (fun gc' => Sdom gc' c.(Datalog.clause_rel)) hs c
             (fun gc' a => collect_fact_Sdom a gc' c.(Datalog.clause_rel))
             (fun gc' => collect_fact_adds c gc') Hhs gc).
Qed.

Lemma collect_program_Sdom (p : program) (gc : global_context) (R : rel) :
  Sdom gc R -> Sdom (collect_global_names_program p gc) R.
Proof.
  intros H. unfold DistributedDatalogToHardwareCompiler.collect_global_names_program.
  apply (fold_left_Q_mono (fun acc r => collect_global_names_rule r acc) (fun gc' => Sdom gc' R) p
           (fun gc' a => collect_rule_Sdom a gc' R)).
  exact H.
Qed.

Lemma collect_program_covers (p : program) (cs hs : list (clause))
    (c : clause) (gc : global_context) :
  In (@Datalog.normal_rule rel var fn aggregator cs hs) p -> (In c cs \/ In c hs) ->
  Sdom (collect_global_names_program p gc) c.(Datalog.clause_rel).
Proof.
  intros Hr Hc. unfold DistributedDatalogToHardwareCompiler.collect_global_names_program.
  exact (fold_left_Q_covers (fun acc r => collect_global_names_rule r acc)
           (fun gc' => Sdom gc' c.(Datalog.clause_rel)) p (@Datalog.normal_rule rel var fn aggregator cs hs)
           (fun gc' a => collect_rule_Sdom a gc' c.(Datalog.clause_rel))
           (fun gc' => collect_rule_covers cs hs c gc' Hc) Hr gc).
Qed.

Lemma collect_layout_covers (layout : layout_map) (n : node_id) (p : program)
    (cs hs : list (clause)) (c : clause)
    (gc : global_context) :
  map.get layout n = Some p -> In (@Datalog.normal_rule rel var fn aggregator cs hs) p -> (In c cs \/ In c hs) ->
  Sdom (collect_global_names_layout layout gc) c.(Datalog.clause_rel).
Proof.
  intros Hget Hinr Hc. unfold DistributedDatalogToHardwareCompiler.collect_global_names_layout.
  enough (Haux : map.get layout n = Some p ->
            Sdom (map.fold (fun acc _ program => collect_global_names_program program acc) gc layout)
                 c.(Datalog.clause_rel)) by (apply Haux; exact Hget).
  apply (map.fold_spec (fun (m : layout_map) (acc : global_context) =>
           map.get m n = Some p -> Sdom acc c.(Datalog.clause_rel))).
  - intros Hempty. rewrite map.get_empty in Hempty. discriminate.
  - intros k v m acc Hgmk IH Hgputn. destruct (eqb_boolspec _ n k) as [->|Hne].
    + rewrite map.get_put_same in Hgputn. injection Hgputn as Hvp. rewrite Hvp.
      exact (collect_program_covers p cs hs c acc Hinr Hc).
    + rewrite map.get_put_diff in Hgputn by congruence. apply collect_program_Sdom. exact (IH Hgputn).
Qed.

(* SOURCE Sprogram IS AUTOMATIC: the rename pass collects every relation appearing in the layout. *)
Lemma source_Sprogram (layout : layout_map) :
  RelabelCorrect.Sprogram (Sdom (collect_global_names_layout layout initial_global_context))
    (source_program layout).
Proof.
  unfold RelabelCorrect.Sprogram. apply Forall_forall. intros r Hr.
  apply source_program_in in Hr. destruct Hr as [n [p [Hgetn Hinr]]].
  destruct r as [cs hs | | ]; cbn [RelabelCorrect.Srule]; [| exact I | exact I]. split.
  - apply Forall_forall. intros c Hc. unfold RelabelCorrect.Sclause.
    exact (collect_layout_covers layout n p cs hs c initial_global_context Hgetn Hinr (or_introl Hc)).
  - apply Forall_forall. intros c Hc. unfold RelabelCorrect.Sclause.
    exact (collect_layout_covers layout n p cs hs c initial_global_context Hgetn Hinr (or_intror Hc)).
Qed.

(* [relabel_fact] renames only the relation, so [rel_of] commutes with it. *)
Lemma rel_of_relabel_fact (rho : rel -> rel_id) (f : Datalog.fact) :
  Datalog.rel_of (RelabelCorrect.relabel_fact rho f) = rho (Datalog.rel_of f).
Proof. destruct f; reflexivity. Qed.

(* [global_rename_rel] of a relation in [gc]'s domain yields an id BELOW the fresh [last_rel_id]. *)
Lemma grrel_lt (gc : global_context) (HR : RelInv gc) (r : rel) (id : rel_id) :
  DistributedDatalogToHardwareCompiler.global_rename_rel r gc = Success id -> id < rlast gc.
Proof.
  unfold DistributedDatalogToHardwareCompiler.global_rename_rel.
  destruct (map.get gc.(DistributedDatalogToHardwareCompiler.rel_map) r) as [id1 |] eqn:Hgm;
    intros H; [| discriminate]. injection H as <-. exact (proj2 HR r id1 Hgm).
Qed.

(* Every key of the renamed producer table has an id BELOW [last_rel_id]: producers are collected, so
   each renames to a real id < the fresh counter.  Proved as a [map.fold] invariant -- the table is a
   MAP now, not a list, so the old list induction over [fold_left] is replaced by [map.fold_spec]. *)
Lemma grfl_id_lt (gc : global_context) (HR : RelInv gc)
    (fl : fact_locations) (res : lowered_fact_locations) :
  DistributedDatalogToHardwareCompiler.global_rename_fact_locations fl gc = Success res ->
  forall rid locs, map.get res rid = Some locs -> rid < rlast gc.
Proof.
  unfold DistributedDatalogToHardwareCompiler.global_rename_fact_locations.
  revert res.
  apply (map.fold_spec
    (fun (m : fact_locations) (acc : result lowered_fact_locations) =>
       forall res, acc = Success res -> forall rid locs, map.get res rid = Some locs -> rid < rlast gc)).
  - intros res Hres rid locs Hget. injection Hres as <-. rewrite map.get_empty in Hget. discriminate.
  - intros r locations m acc Hnone IH res Hres rid locs Hget.
    cbn beta iota in Hres.
    destruct acc as [acc0 | e]; cbn beta iota in Hres; [| discriminate Hres].
    destruct (DistributedDatalogToHardwareCompiler.global_rename_rel r gc) as [r_id | e] eqn:Hgrel;
      cbn beta iota in Hres; [| discriminate Hres].
    injection Hres as <-.
    destruct (Nat.eq_dec rid r_id) as [->|Hne].
    + exact (grrel_lt gc HR r r_id Hgrel).
    + rewrite map.get_put_diff in Hget by exact Hne. exact (IH acc0 eq_refl rid locs Hget).
Qed.

(* The fresh id [last_rel_id] -- where out-of-scope relations land -- routes nowhere: every key of the
   renamed producer table is a real id BELOW [last_rel_id] ([grfl_id_lt]), so [last_rel_id] has no entry. *)
Lemma rel_locs_rlast_nil (layout : layout_map) (fps : fact_locations) (lfp : lowered_fact_locations)
    (n : node_id) :
  DistributedDatalogToHardwareCompiler.global_rename_fact_locations fps
    (collect_global_names_layout layout initial_global_context) = Success lfp ->
  ~ In n (rel_locs lfp (rlast (collect_global_names_layout layout initial_global_context))).
Proof.
  intros Hgr Hin. apply rel_locs_In in Hin. destruct Hin as [locs [Hentry _]].
  exact (Nat.lt_irrefl _ (grfl_id_lt _ (collect_global_names_RelInv layout) fps lfp Hgr _ locs Hentry)).
Qed.

(* The renaming preserves each producer entry: a source entry [fps[R] = locs] reappears in the renamed
   table at the renamed key [rho_gc gc R] with the SAME locations.  Key facts used: [R] renamed via
   [global_rename_rel] lands at [rho_gc gc R]; renaming is INJECTIVE on [gc]'s domain (RelInv) and the
   fresh [last_rel_id] sits above every real id, so no two source keys collide in the renamed map. *)
Lemma grfl_get (gc : global_context) (HR : RelInv gc) (fps : fact_locations) (lfp : lowered_fact_locations) :
  DistributedDatalogToHardwareCompiler.global_rename_fact_locations fps gc = Success lfp ->
  forall R locs, map.get fps R = Some locs -> map.get lfp (rho_gc gc R) = Some locs.
Proof.
  unfold DistributedDatalogToHardwareCompiler.global_rename_fact_locations.
  revert lfp.
  apply (map.fold_spec
    (fun (m : fact_locations) (acc : result lowered_fact_locations) =>
       forall lfp, acc = Success lfp -> forall R locs, map.get m R = Some locs -> map.get lfp (rho_gc gc R) = Some locs)).
  - intros lfp Hlfp R locs Hget. rewrite map.get_empty in Hget. discriminate.
  - intros r locations m acc Hnone IH lfp Hlfp R locs Hget.
    cbn beta iota in Hlfp.
    destruct acc as [acc0 | e]; cbn beta iota in Hlfp; [| discriminate Hlfp].
    destruct (DistributedDatalogToHardwareCompiler.global_rename_rel r gc) as [r_id | e] eqn:Hgrel;
      cbn beta iota in Hlfp; [| discriminate Hlfp].
    injection Hlfp as <-.
    assert (Hrr : map.get gc.(DistributedDatalogToHardwareCompiler.rel_map) r = Some r_id).
    { unfold DistributedDatalogToHardwareCompiler.global_rename_rel in Hgrel.
      destruct (map.get gc.(DistributedDatalogToHardwareCompiler.rel_map) r) as [id|] eqn:Hg;
        [| discriminate Hgrel].
      injection Hgrel as Heq. f_equal. exact Heq. }
    destruct (rel_eqb_spec R r) as [HeqRr | HneRr].
    + subst R. rewrite map.get_put_same in Hget. injection Hget as Heq. subst locs.
      unfold rho_gc. rewrite Hrr. rewrite map.get_put_same. reflexivity.
    + rewrite map.get_put_diff in Hget by exact HneRr.
      assert (Hrho_ne : rho_gc gc R <> r_id).
      { unfold rho_gc. destruct (map.get gc.(DistributedDatalogToHardwareCompiler.rel_map) R) as [idR|] eqn:HgR.
        - intros Heq. subst idR. exact (HneRr (proj1 HR R r r_id HgR Hrr)).
        - intros Heq. pose proof (proj2 HR r r_id Hrr) as Hlt. rewrite Heq in Hlt. exact (Nat.lt_irrefl _ Hlt). }
      rewrite map.get_put_diff by exact Hrho_ne. exact (IH acc0 eq_refl R locs Hget).
Qed.

(* THE BRIDGE: source EDB-routability (over [fps]/[Qsrc], no renaming) implies the [rel_id]-level
   [edb_routable] the proof core uses, because the renamed producer table is just [fps] with keys
   renamed and locations preserved ([grfl_get]). *)
Lemma edb_routable_src_to_renamed (gc : global_context) (HR : RelInv gc)
    (fps : fact_locations) (lfp : lowered_fact_locations) (Qsrc : Datalog.fact -> Prop) :
  DistributedDatalogToHardwareCompiler.global_rename_fact_locations fps gc = Success lfp ->
  edb_routable_src fps Qsrc ->
  edb_routable lfp (RelabelCorrect.relabel_Q (rho_gc gc) Qsrc).
Proof.
  intros Hgr Hsrc f' [f [HQf Hrel]]. subst f'.
  destruct (Hsrc f HQf) as [n Hn]. unfold src_rel_locs in Hn.
  destruct (map.get fps (Datalog.rel_of f)) as [locs|] eqn:Hfps; [| destruct Hn].
  exists n. unfold rel_locs. rewrite rel_of_relabel_fact.
  rewrite (grfl_get gc HR fps lfp Hgr (Datalog.rel_of f) locs Hfps). exact Hn.
Qed.

(* source-level twins of the [rel_id]-level set-invariance lemmas (same proofs, over [rel]/[fn]).
   ([incl_b] and the layout-distributes-program checker live in the compiler file, aliased above.) *)
Lemma bare_meta_concl_rels_nil_src (p : program) :
  RelabelCorrect.bare_program p -> flat_map Datalog.meta_concl_rels p = [].
Proof.
  intros H. induction p as [| r p IH]; cbn; [reflexivity|].
  inversion H as [| r0 p0 Hr Hp]; subst.
  destruct r as [cs hs | | ]; cbn [RelabelCorrect.bare_rule] in Hr; [| contradiction | contradiction].
  cbn [Datalog.meta_concl_rels]. apply IH. exact Hp.
Qed.

Lemma prog_impl_set_iff_src (p1 p2 : program) (Q : Datalog.fact -> Prop) (f : Datalog.fact) :
  RelabelCorrect.bare_program p1 -> RelabelCorrect.bare_program p2 ->
  incl p1 p2 -> incl p2 p1 ->
  (Datalog.prog_impl p1 Q f <-> Datalog.prog_impl p2 Q f).
Proof.
  intros Hb1 Hb2 H12 H21. split; intros H.
  - apply (Datalog.prog_impl_subset p1 p2 Q f H12); [| exact H].
    intros r _. right. rewrite (bare_meta_concl_rels_nil_src p1 Hb1). intros x [].
  - apply (Datalog.prog_impl_subset p2 p1 Q f H21); [| exact H].
    intros r _. right. rewrite (bare_meta_concl_rels_nil_src p2 Hb2). intros x [].
Qed.

(*----"[rel_of fsrc] is in [P]" as the P-level query-in-scope condition----*)

(* the relations a program mentions, in any rule head or body. *)
Definition program_rels (P : program) : list rel := flat_map Datalog.all_rels P.

Lemma program_rels_incl (P1 P2 : program) : incl P1 P2 -> incl (program_rels P1) (program_rels P2).
Proof.
  intros H r Hr. apply in_flat_map in Hr. destruct Hr as [rule [Hrule Hr]].
  apply in_flat_map. exists rule. split; [apply H; exact Hrule | exact Hr].
Qed.

(* [collect_global_names_layout] is CORRECT in the sense we need: every relation the (bare) source
   program mentions is collected, i.e. lands in [Sdom].  So "rel in P" -- via [layout_distributes_
   program] -- yields the [Sdom] fact the relabel bridge wants, with no [collect_*] in the hypothesis. *)
Lemma program_rels_in_domain (layout : layout_map) (r : rel) :
  RelabelCorrect.bare_program (source_program layout) ->
  In r (program_rels (source_program layout)) ->
  Sdom (collect_global_names_layout layout initial_global_context) r.
Proof.
  intros Hbare Hin. apply in_flat_map in Hin. destruct Hin as [rule [Hrule Hr]].
  pose proof (proj1 (Forall_forall _ _) (source_Sprogram layout) rule Hrule) as HSr.
  pose proof (proj1 (Forall_forall _ _) Hbare rule Hrule) as Hbr.
  destruct rule as [cs hs | mcs mhs | cr ag hr];
    cbn [RelabelCorrect.bare_rule] in Hbr; [| contradiction | contradiction].
  cbn [RelabelCorrect.Srule] in HSr. destruct HSr as [HSc HSh].
  unfold Datalog.all_rels in Hr. cbn [Datalog.concl_rels Datalog.hyp_rels] in Hr.
  apply in_app_iff in Hr. destruct Hr as [Hr | Hr];
    apply in_map_iff in Hr; destruct Hr as [c [Hceq Hcin]]; subst r.
  - exact (proj1 (Forall_forall _ _) HSc c Hcin).
  - exact (proj1 (Forall_forall _ _) HSh c Hcin).
Qed.

(*========================================================================================*)
(*  RENAMING PRESERVES THE BARENESS CHECK.  [global_rename_*] only swaps relation/function     *)
(*  identifiers; it never changes whether an argument is a [var_expr] or a [fun_expr].  So the  *)
(*  (parametric) [bare_ruleb]/[bare_layoutb] check is rename-invariant, and the top theorem can *)
(*  state bareness over the SOURCE [layout], transporting it to the renamed [llayout].          *)
(*========================================================================================*)

(* renaming a plain-variable arg yields a plain-variable arg. *)
Lemma grn_expr_isvarb_fwd (gc : global_context) (e : Datalog.expr) (le : lowered_expr) :
  (match e with var_expr _ => true | fun_expr _ _ => false end) = true ->
  global_rename_expr fn_to_id e gc = Success le ->
  (match le with var_expr _ => true | fun_expr _ _ => false end) = true.
Proof.
  destruct e as [v | f0 args]; intros Hb Hren; [| discriminate].
  cbn in Hren. injection Hren as <-. reflexivity.
Qed.

Lemma grn_fact_bareb_fwd (gc : global_context) (f : clause) (lf : lowered_fact) :
  global_rename_fact fn_to_id f gc = Success lf -> bare_factb f = true -> bare_factb lf = true.
Proof.
  unfold DistributedDatalogToHardwareCompiler.global_rename_fact. intros Hren Hbare.
  destruct (global_rename_rel f.(Datalog.clause_rel) gc) as [rid | msg]; [| discriminate].
  match type of Hren with context[List.all_success ?x] =>
    destruct (List.all_success x) as [rargs | msg] eqn:Hall; [| discriminate] end.
  injection Hren as <-. unfold bare_factb in Hbare |- *. cbn [Datalog.clause_args].
  assert (Hres : Forall (fun b => (match b with var_expr _ => true | fun_expr _ _ => false end) = true) rargs).
  { apply (all_success_map_forall_pres (fun a => global_rename_expr fn_to_id a gc)
             (fun a => (match a with var_expr _ => true | fun_expr _ _ => false end) = true)
             (fun b => (match b with var_expr _ => true | fun_expr _ _ => false end) = true)
             (grn_expr_isvarb_fwd gc) f.(Datalog.clause_args) rargs); [| exact Hall].
    apply Forall_forall. exact (proj1 (forallb_forall _ _) Hbare). }
  apply forallb_forall. intros e He.
  rewrite Forall_forall in Hres. exact (Hres e He).
Qed.

(* the per-fact-list step (hyps / concls), via [grn_fact_bareb_fwd]. *)
Lemma grn_facts_bareb_fwd (gc : global_context) (fs : list (clause))
    (lfs : list lowered_fact) :
  List.all_success (List.map (fun f => global_rename_fact fn_to_id f gc) fs) = Success lfs ->
  forallb bare_factb fs = true -> forallb bare_factb lfs = true.
Proof.
  intros Hall Hbare.
  assert (Hres : Forall (fun lf => bare_factb lf = true) lfs).
  { apply (all_success_map_forall_pres (fun f => global_rename_fact fn_to_id f gc)
             (fun f => bare_factb f = true) (fun lf => bare_factb lf = true)
             (fun x y Hb Hg => grn_fact_bareb_fwd gc x y Hg Hb) fs lfs); [| exact Hall].
    apply Forall_forall. exact (proj1 (forallb_forall _ _) Hbare). }
  apply forallb_forall. intros lf Hlf.
  rewrite Forall_forall in Hres. exact (Hres lf Hlf).
Qed.

Lemma grn_rule_bareb_fwd (gc : global_context) (r : rule)
    (lr : lowered_rule) :
  global_rename_rule fn_to_id r gc = Success lr -> bare_ruleb r = true -> bare_ruleb lr = true.
Proof.
  intros Hren Hbare. destruct r as [rconcls rhyps | mcs mhs | cr agg hr];
    cbn [DistributedDatalogToHardwareCompiler.global_rename_rule] in Hren; [| discriminate | discriminate].
  match type of Hren with context[List.all_success (List.map ?ff rhyps)] =>
    destruct (List.all_success (List.map ff rhyps)) as [hyps_f | msg] eqn:Hfh; [| discriminate] end.
  match type of Hren with context[List.all_success (List.map ?ff rconcls)] =>
    destruct (List.all_success (List.map ff rconcls)) as [concls_f | msg] eqn:Hfc; [| discriminate] end.
  injection Hren as <-. cbn [bare_ruleb] in Hbare |- *.
  apply andb_true_iff in Hbare. destruct Hbare as [Hbh Hbc].
  apply andb_true_iff. split.
  - exact (grn_facts_bareb_fwd gc rhyps hyps_f Hfh Hbh).
  - exact (grn_facts_bareb_fwd gc rconcls concls_f Hfc Hbc).
Qed.

Lemma grn_program_bareb_fwd (gc : global_context) (p : program) (lp : lowered_program) :
  global_rename_program p gc = Success lp -> forallb bare_ruleb p = true -> forallb bare_ruleb lp = true.
Proof.
  unfold DistributedDatalogToHardwareCompiler.global_rename_program. intros Hren Hbare.
  match type of Hren with context[List.all_success ?x] =>
    destruct (List.all_success x) as [rs | msg] eqn:Hall; [| discriminate] end.
  injection Hren as <-.
  assert (Hres : Forall (fun lr => bare_ruleb lr = true) rs).
  { apply (all_success_map_forall_pres (fun r => global_rename_rule fn_to_id r gc)
             (fun r => bare_ruleb r = true) (fun lr => bare_ruleb lr = true)
             (fun x y Hb Hg => grn_rule_bareb_fwd gc x y Hg Hb) p rs); [| exact Hall].
    apply Forall_forall. exact (proj1 (forallb_forall _ _) Hbare). }
  apply forallb_forall. intros lr Hlr.
  rewrite Forall_forall in Hres. exact (Hres lr Hlr).
Qed.

(* converse of [bare_layoutb_entry]: a layout all of whose programs are bare passes [bare_layoutb]. *)
Lemma bare_layoutb_intro (llayout : lowered_layout_map) :
  (forall n p, map.get llayout n = Some p -> forallb bare_ruleb p = true) ->
  bare_layoutb llayout = true.
Proof.
  unfold bare_layoutb.
  apply (map.fold_spec
    (fun (m : lowered_layout_map) (b : bool) =>
       (forall n p, map.get m n = Some p -> forallb bare_ruleb p = true) -> b = true)).
  - intros _. reflexivity.
  - intros k v m r Hgmk IH Hall. apply andb_true_iff. split.
    + apply IH. intros n p Hget. apply (Hall n p).
      rewrite map.get_put_diff; [exact Hget |]. intros ->. rewrite Hgmk in Hget. discriminate.
    + exact (Hall k v (map.get_put_same m k v)).
Qed.

(* THE BRIDGE: [bare_layoutb] is rename-invariant, so the source layout's bareness transports. *)
Lemma rename_preserves_bare_layoutb (layout : layout_map) (gc : global_context) (llayout : lowered_layout_map) :
  global_rename_rule_layout layout gc = Success llayout ->
  bare_layoutb layout = true ->
  bare_layoutb llayout = true.
Proof.
  intros Hgr Hbl. apply bare_layoutb_intro. intros n lp Hgetll.
  destruct (global_rename_rule_layout_spec layout gc llayout n lp Hgr Hgetll) as [orig [Hgetlayout Hgrp]].
  exact (grn_program_bareb_fwd gc orig lp Hgrp (bare_layoutb_entry layout Hbl n orig Hgetlayout)).
Qed.

(*========================================================================================*)
(*  THE FINAL THEOREM: correctness over a USER-SUPPLIED program [P], given the layout is a     *)
(*  valid distribution of [P] ([layout_distributes_program], a checkable rule-set equality).    *)
(*  No relabel-equality / injectivity hyps (discharged); "inputs in scope" is ABSORBED by      *)
(*  [edb_routable]; the query-in-scope condition is the plain "[rel_of fsrc] is in [P]".         *)
(*========================================================================================*)
Theorem compile_implements_source
    (layout : layout_map) (fps fcs : fact_locations) (g : node_graph)
    (ninfos : list node_info) (llayout : lowered_layout_map) (lfp lfc : lowered_fact_locations)
    (gcontext : global_context)
    (* a decidable equality on source rules, so the distribution condition is a runnable boolean check
       (the concrete layer supplies it, e.g. a string-rule equality) *)
    (P : program)
    (Qsrc : Datalog.fact -> Prop) (fsrc : Datalog.fact) :
  (* the compiler succeeds *)
  compile layout fps fcs g = Success ninfos ->
  (* renaming of inputs to numbers *)
  lower_inputs layout fps fcs = Success (llayout, lfp, lfc, gcontext) ->
  (* the source layout only has variables (no functions) *)
  bare_layoutb layout = true ->
  (* the layout is a valid distribution of the reference program [P] (same rule set) -- a CHECKABLE
     boolean (examples discharge it by [vm_compute]); [layout_distributes_programb_spec] soundly turns
     it into the [Prop] the proof uses. *)
  layout_distributes_programb P layout = true ->
  (* the queried fact's relation appears in [P] *)
  In (Datalog.rel_of fsrc) (program_rels P) ->
  (* Every base fact's relation has a declared input node *)
  edb_routable_src fps Qsrc ->
  run_ninfos ninfos
    (* Input *)
    (fun n f0 => RelabelCorrect.relabel_Q (rho_gc gcontext) Qsrc f0 /\ In n (rel_locs lfp (Datalog.rel_of f0)))
    (* Output *)
    (fun n R => In n (rel_locs lfc R))
    (* Query *)
    (RelabelCorrect.relabel_fact (rho_gc gcontext) fsrc)
  <-> Datalog.prog_impl P Qsrc fsrc.
Proof.
  intros Hcomp Hlow Hbl_src Hdistb Hquery Hedbsrc.
  pose proof (layout_distributes_programb_spec P layout Hdistb) as Hdist.
  (* the [lower_inputs] equation IS the rename results: it names the compiler's actual renamed
     layout/fact-tables and the collected name context. *)
  destruct (lower_inputs_inv layout fps fcs llayout lfp lfc gcontext Hlow) as [Hgc0 [Hgrl [Hgrfp Hgrfc]]].
  subst gcontext.
  (* the SOURCE bareness check transports to the renamed [llayout] (renaming is bareness-invariant). *)
  assert (Hbl : bare_layoutb llayout = true)
    by exact (rename_preserves_bare_layoutb layout
                (collect_global_names_layout layout initial_global_context) llayout Hgrl Hbl_src).
  (* lift the source EDB-routability to the [rel_id]-level [edb_routable] the proof core uses, via the
     fact that the renamed producer table [lfp] is [fps] with keys renamed and locations preserved. *)
  assert (Hedb : edb_routable lfp
                   (RelabelCorrect.relabel_Q (rho_gc (collect_global_names_layout layout initial_global_context)) Qsrc)).
  { exact (edb_routable_src_to_renamed (collect_global_names_layout layout initial_global_context)
             (collect_global_names_RelInv layout) fps lfp Qsrc Hgrfp Hedbsrc). }
  (* "inputs are in scope" is FORCED by routability: an out-of-scope input renames to the fresh
     [last_rel_id], which has no producer node ([rel_locs_rlast_nil]), so [edb_routable] can't route
     it -- contradiction. *)
  assert (HSQ : facts_in_domain (collect_global_names_layout layout initial_global_context) Qsrc).
  { intros h Hh. unfold fact_in_domain, Sdom.
    destruct (map.get (collect_global_names_layout layout initial_global_context).(DistributedDatalogToHardwareCompiler.rel_map)
                (Datalog.rel_of h)) as [id |] eqn:Hget; [exists id; reflexivity |].
    exfalso.
    destruct (Hedb (RelabelCorrect.relabel_fact
                      (rho_gc (collect_global_names_layout layout initial_global_context)) h)
                (ex_intro _ h (conj Hh eq_refl))) as [n Hn].
    rewrite rel_of_relabel_fact in Hn. unfold rho_gc in Hn. rewrite Hget in Hn.
    exact (rel_locs_rlast_nil layout fps lfp n Hgrfp Hn). }
  (* bareness of the source program is implied by the layoutb check on the renamed layout. *)
  pose proof (source_bare_of_layoutb layout (collect_global_names_layout layout initial_global_context)
                llayout Hgrl Hbl) as Hbsrc.
  (* "rel of fsrc is in P" gives the [Sdom] fact (via [layout_distributes_program] + collect-correctness). *)
  assert (HSf : fact_in_domain (collect_global_names_layout layout initial_global_context) fsrc).
  { exact (program_rels_in_domain layout (Datalog.rel_of fsrc) Hbsrc
             (program_rels_incl P (source_program layout) (proj2 Hdist) (Datalog.rel_of fsrc) Hquery)). }
  (* the reference [P] has the same rules as [source_program layout], hence is bare and derives the
     same facts -- swap [prog_impl P] for [prog_impl (source_program layout)] and proceed as before. *)
  assert (HbareP : RelabelCorrect.bare_program P).
  { unfold RelabelCorrect.bare_program. apply Forall_forall. intros r Hr.
    exact (proj1 (Forall_forall _ _) Hbsrc r (proj2 Hdist r Hr)). }
  rewrite (prog_impl_set_iff_src P (source_program layout) Qsrc fsrc HbareP Hbsrc
             (proj2 Hdist) (proj1 Hdist)).
  pose proof (source_Sprogram layout) as HSsrc.
  set (gc0 := collect_global_names_layout layout initial_global_context) in *.
  rewrite (compile_distributed_correct layout fps fcs g ninfos llayout lfp lfc gc0
             (RelabelCorrect.relabel_Q (rho_gc gc0) Qsrc) Hlow Hcomp Hbl Hedb
             (RelabelCorrect.relabel_fact (rho_gc gc0) fsrc)).
  assert (Hrelsrc_bare :
            RelabelCorrect.bare_program
              (RelabelCorrect.relabel_program (rho_gc gc0) (fn_to_id) (source_program layout))).
  { unfold RelabelCorrect.bare_program. apply Forall_forall. intros r Hr.
    apply (proj1 (Forall_forall _ _) (canonical_renamed_bare llayout Hbl)).
    apply (proj2 (canonical_renamed_eq_relabel_source layout llayout r Hgrl Hbsrc HSsrc)).
    exact Hr. }
  rewrite (prog_impl_set_iff (canonical_program llayout)
             (RelabelCorrect.relabel_program (rho_gc gc0) (fn_to_id) (source_program layout))
             (RelabelCorrect.relabel_Q (rho_gc gc0) Qsrc)
             (RelabelCorrect.relabel_fact (rho_gc gc0) fsrc)
             (canonical_renamed_bare llayout Hbl) Hrelsrc_bare
             (fun r Hr => proj1 (canonical_renamed_eq_relabel_source layout llayout r Hgrl Hbsrc HSsrc) Hr)
             (fun r Hr => proj2 (canonical_renamed_eq_relabel_source layout llayout r Hgrl Hbsrc HSsrc) Hr)).
  exact (RelabelCorrect.prog_impl_relabel (rho_gc gc0) (fn_to_id) (Sdom gc0)
           (rho_gc_injective_collect layout) (source_program layout) Qsrc fsrc Hbsrc HSsrc HSQ HSf).
Qed.

End CompileTop.
