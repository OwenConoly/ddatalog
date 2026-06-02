(* This takes a datalog program, and for every rule, it generates the rules that it might depend on
   which will then be fed into gurobi to find an optimal layout. *)

From Datalog Require Import Datalog.
From Stdlib Require Import List String Bool ZArith Lia.
From coqutil Require Import Datatypes.List Map.Interface.
From DatalogRocq Require Import EqbSpec.

Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.

Section DependencyGenerator.

Context {rel var fn aggregator T : Type}.
Context `{sig : signature fn aggregator T} `{query_sig : query_signature rel}.
Context {context : map.map var T} {context_ok : map.ok context}.
Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}. 
Context {rel_eqb : rel -> rel -> bool} {rel_eqb_spec : forall x0 y0 : rel, BoolSpec (x0 = y0) (x0 <> y0) (rel_eqb x0 y0)}.
Context {fn_eqb : fn -> fn -> bool} {fn_eqb_spec : forall x0 y0 : fn, BoolSpec (x0 = y0) (x0 <> y0) (fn_eqb x0 y0)}.
Context {aggregator_eqb : aggregator -> aggregator -> bool}
        {aggregator_eqb_spec : forall x0 y0 : aggregator, BoolSpec (x0 = y0) (x0 <> y0) (aggregator_eqb x0 y0)}.

Definition expr := Datalog.expr var fn.
(* an atom in a rule is a [clause]; a rule is the [normal_rule | meta_rule | agg_rule]
   inductive.  The compiler only builds/reads [normal_rule]s (the bare fragment). *)
Definition fact := Datalog.clause rel var fn.
Definition rule := Datalog.rule rel var fn aggregator.
Definition program := list rule.

Context {expr_compatible : expr -> expr -> bool}.

(* Basic Utilities *)

Definition is_var (e : expr) : bool :=
  match e with
  | Datalog.var_expr _ => true
  | _ => false
  end.

Definition is_const (e : expr) : bool :=
  match e with
  | Datalog.fun_expr _ [] => true
  | _ => false
  end.

Definition is_fun_app (e : expr) : bool :=
  match e with
  | Datalog.fun_expr _ (_::_) => true
  | _ => false
  end.

Definition get_var (e : expr) : option var :=
  match e with
  | Datalog.var_expr v => Some v
  | _ => None
  end.

Definition get_const (e : expr) : option fn :=
  match e with
  | Datalog.fun_expr f [] => Some f
  | _ => None
  end.

Definition dedup {A : Type} (eqb : A -> A -> bool) (lst : list A) : list A :=
  fold_right (fun x acc =>
                if existsb (eqb x) acc then acc
                else x :: acc) [] (lst).

(* Eqb *)

Fixpoint map2 {A B C : Type} (f : A -> B -> C) l1 l2 :=
  match l1, l2 with
  | x1 :: l1', x2 :: l2' => f x1 x2 :: map2 f l1' l2'
  | _, _ => []
  end.

Fixpoint expr_eqb (e1 e2 : expr) : bool :=
  match e1, e2 with
  | Datalog.var_expr v1, Datalog.var_expr v2 => var_eqb v1 v2
  | Datalog.fun_expr f1 args1, Datalog.fun_expr f2 args2 =>
      fn_eqb f1 f2 &&
        Nat.eqb (List.length args1) (List.length args2) && 
        fold_right andb true (map2 expr_eqb args1 args2)
  | _, _ => false
  end.

Lemma fold_map_andb_spec_forall :
  forall f : expr -> expr -> bool,
  forall l1 l2,
    List.length l1 = List.length l2 ->
    Forall (fun e1 => forall e2, BoolSpec (e1 = e2) (e1 <> e2) (f e1 e2)) l1 ->
    BoolSpec (l1 = l2)
             (l1 <> l2)
             (fold_right andb true (map2 f l1 l2)).
Proof.
  intros f.
  induction l1 as [|x1 xs1 IH]; intros l2 Hbd Hf; destruct l2 as [|x2 xs2]; simpl in *; try (constructor; congruence).
  inversion Hf; subst.
  destruct (H1 x2); subst; simpl; try (constructor; congruence).
  destruct (IH xs2); try (constructor; congruence); inversion Hbd; auto.
Qed.

Lemma expr_eqb_spec :
  forall e1 e2,
    BoolSpec (e1 = e2) (e1 <> e2) (expr_eqb e1 e2).
Proof.
  induction e1; destruct e2; simpl; try (constructor; congruence).
  - destruct (var_eqb_spec v v0); subst; simpl; try (constructor; congruence).
  - destruct (fn_eqb_spec f f0); subst; simpl; try (constructor; congruence).
    destruct (Nat.eqb_spec (List.length args) (List.length args0)); simpl; try (constructor; congruence).
    destruct (fold_map_andb_spec_forall expr_eqb  args args0 e H); try (constructor; congruence).
Qed.

Definition fact_eqb (f1 f2 : fact) : bool :=
  rel_eqb (Datalog.clause_rel f1) (Datalog.clause_rel f2) &&
  list_eqb expr_eqb (Datalog.clause_args f1) (Datalog.clause_args f2).

Lemma fact_eqb_spec :
  forall f1 f2,
    BoolSpec (f1 = f2) (f1 <> f2) (fact_eqb f1 f2).
Proof.
  intros [R1 args1] [R2 args2]; unfold fact_eqb; simpl.
  destruct (rel_eqb_spec R1 R2); try (constructor; congruence).
  destruct (@list_eqb_spec _ expr_eqb expr_eqb_spec args1 args2); subst; simpl; try (constructor; congruence).
Qed.

(* equality on meta-clauses (used only to give [rule_eqb] a total, spec-correct
   definition over all three rule constructors; the bare fragment only uses [normal_rule]) *)
Definition meta_clause_eqb (m1 m2 : Datalog.meta_clause rel var fn) : bool :=
  rel_eqb (Datalog.meta_clause_rel m1) (Datalog.meta_clause_rel m2) &&
  list_eqb (option_eqb expr_eqb) (Datalog.meta_clause_args m1) (Datalog.meta_clause_args m2).

Lemma meta_clause_eqb_spec :
  forall m1 m2,
    BoolSpec (m1 = m2) (m1 <> m2) (meta_clause_eqb m1 m2).
Proof.
  intros [R1 args1] [R2 args2]; unfold meta_clause_eqb; simpl.
  destruct (rel_eqb_spec R1 R2); subst; simpl; try (constructor; congruence).
  destruct (@list_eqb_spec _ (option_eqb expr_eqb)
              (option_eqb_spec expr_eqb expr_eqb_spec) args1 args2);
    subst; simpl; try (constructor; congruence).
Qed.

Definition rule_eqb (r1 r2 : rule) : bool :=
  match r1, r2 with
  | Datalog.normal_rule c1 h1, Datalog.normal_rule c2 h2 =>
      list_eqb fact_eqb c1 c2 && list_eqb fact_eqb h1 h2
  | Datalog.meta_rule c1 h1, Datalog.meta_rule c2 h2 =>
      list_eqb meta_clause_eqb c1 c2 && list_eqb meta_clause_eqb h1 h2
  | Datalog.agg_rule cr1 a1 hr1, Datalog.agg_rule cr2 a2 hr2 =>
      rel_eqb cr1 cr2 && aggregator_eqb a1 a2 && rel_eqb hr1 hr2
  | _, _ => false
  end.

Definition rule_eqb_spec :
  forall r1 r2,
    BoolSpec (r1 = r2) (r1 <> r2) (rule_eqb r1 r2).
Proof.
  intros [c1 h1 | c1 h1 | cr1 a1 hr1] [c2 h2 | c2 h2 | cr2 a2 hr2]; simpl;
    try (constructor; congruence).
  - destruct (@list_eqb_spec _ fact_eqb fact_eqb_spec c1 c2); simpl; try (constructor; congruence).
    destruct (@list_eqb_spec _ fact_eqb fact_eqb_spec h1 h2); simpl; try (constructor; congruence).
  - destruct (@list_eqb_spec _ meta_clause_eqb meta_clause_eqb_spec c1 c2); simpl; try (constructor; congruence).
    destruct (@list_eqb_spec _ meta_clause_eqb meta_clause_eqb_spec h1 h2); simpl; try (constructor; congruence).
  - destruct (rel_eqb_spec cr1 cr2); subst; simpl; try (constructor; congruence).
    destruct (aggregator_eqb_spec a1 a2); subst; simpl; try (constructor; congruence).
    destruct (rel_eqb_spec hr1 hr2); subst; simpl; try (constructor; congruence).
Qed.

(* Pruning.  The compiler only ever produces [normal_rule]s (the bare fragment),
   so concls/hyps are read by matching that constructor directly. *)
Definition prune_empty_concl_rules (p : program) : program :=
  filter (fun r => match r with
                   | Datalog.normal_rule concls _ => negb (list_eqb fact_eqb concls [])
                   | _ => false
                   end) p.

(* Collect *)
Fixpoint collect_vars (e : expr) : list var :=
  match e with
  | Datalog.var_expr v => [v]
  | Datalog.fun_expr _ args => 
      flat_map collect_vars args
  end.

Fixpoint collect_consts (e : expr) : list fn :=
  match e with
  | Datalog.var_expr _ => []
  | Datalog.fun_expr f [] => [f]
  | Datalog.fun_expr _ args => 
      flat_map collect_consts args
  end.

Fixpoint collect_funs (e : expr) : list fn :=
  match e with
  | Datalog.var_expr _ => []
  | Datalog.fun_expr f args => 
      f :: flat_map collect_funs args
  end.

(* Collect Fact *)

Definition collect_vars_from_fact (f : fact) : list var :=
  flat_map collect_vars (Datalog.clause_args f).

Definition collect_consts_from_fact (f : fact) : list fn :=
  flat_map collect_consts (Datalog.clause_args f).

Definition collect_funs_from_fact (f : fact) : list fn :=
  flat_map collect_funs (Datalog.clause_args f).

Definition is_abstract (f : fact) : bool :=
  forallb is_var (Datalog.clause_args f).

Definition is_grounded_fact (f : fact) : bool :=
  forallb is_const (Datalog.clause_args f).

(* Collect for Rules.  Only [normal_rule]s arise in the bare fragment, so we
   match that constructor directly (meta/agg rules contribute nothing here). *)

Definition collect_vars_from_hyps (r : rule) : list var :=
  match r with Datalog.normal_rule _ hyps => flat_map collect_vars_from_fact hyps | _ => [] end.

Definition collect_vars_from_concls (r : rule) : list var :=
  match r with Datalog.normal_rule concls _ => flat_map collect_vars_from_fact concls | _ => [] end.

Definition collect_vars_from_rule (r : rule) : list var :=
  collect_vars_from_hyps r ++ collect_vars_from_concls r.

Definition collect_consts_from_hyps (r : rule) : list fn :=
  match r with Datalog.normal_rule _ hyps => flat_map collect_consts_from_fact hyps | _ => [] end.

Definition collect_consts_from_concls (r : rule) : list fn :=
  match r with Datalog.normal_rule concls _ => flat_map collect_consts_from_fact concls | _ => [] end.

Definition collect_consts_from_rule (r : rule) : list fn :=
  collect_consts_from_hyps r ++ collect_consts_from_concls r.

Definition collect_funs_from_hyps (r : rule) : list fn :=
  match r with Datalog.normal_rule _ hyps => flat_map collect_funs_from_fact hyps | _ => [] end.

Definition collect_funs_from_concls (r : rule) : list fn :=
  match r with Datalog.normal_rule concls _ => flat_map collect_funs_from_fact concls | _ => [] end.

Definition collect_funs_from_rule (r : rule) : list fn :=
  collect_funs_from_hyps r ++ collect_funs_from_concls r.

Definition get_rule_concls_rels (r : rule) : list rel := Datalog.concl_rels r.

Definition get_rule_hyps_rels (r : rule) : list rel := Datalog.hyp_rels r.

(* Pattern Matching.  No aggregation: a rule's hypotheses are just its
   [normal_rule] hyps (no agg hyps to append). *)

Definition get_all_hyps (r : rule) : list fact :=
  match r with Datalog.normal_rule _ hyps => hyps | _ => [] end.

Definition facts_compatible (f1 f2 : fact) : bool :=
  rel_eqb (Datalog.clause_rel f1) (Datalog.clause_rel f2) &&
  list_eqb expr_compatible (Datalog.clause_args f1) (Datalog.clause_args f2).

Definition conc_matches_hyp (conc hyp : fact) : bool :=
  facts_compatible conc hyp.

Definition rule_concls_match_hyps (r1 r2 : rule) : bool :=
  existsb (fun conc =>
    existsb (fun hyp => conc_matches_hyp conc hyp) (get_all_hyps r2)
  ) (match r1 with Datalog.normal_rule concls _ => concls | _ => [] end).

Definition rule_depends_on (r1 r2 : rule) : bool :=
  rule_concls_match_hyps r1 r2.

Definition get_rule_dependencies (p : program) (r : rule) : program :=
  filter (fun r' => rule_depends_on r' r) p.

Definition get_rules_dependent_on (p : program) (r : rule) : program :=
  filter (fun r' => rule_depends_on r r') p.

Definition rel_appears_in_hyps (R : rel) (r : rule) : bool :=
  existsb (fun f => rel_eqb (Datalog.clause_rel f) R)
    (match r with Datalog.normal_rule _ hyps => hyps | _ => [] end).

Definition rel_appears_in_concls (R : rel) (r : rule) : bool :=
  existsb (fun f => rel_eqb (Datalog.clause_rel f) R)
    (match r with Datalog.normal_rule concls _ => concls | _ => [] end).

(* Program Dependencies *)

Definition get_program_dependencies (p : program) : list (rule * list rule) :=
  map (fun r => (r, get_rule_dependencies p r)) p.

Fixpoint lookup_rule_number (r : rule) (p : program) (n : nat) : option nat :=
  match p with
  | [] => None
  | r' :: ps =>
      if rule_eqb r r' then Some n
      else lookup_rule_number r ps (n + 1)
  end.

Definition get_program_dependencies_by_index (p : program) : list (nat * list nat) :=
  let fix aux lst n :=
      match lst with
      | [] => []
      | r :: rs =>
          let deps := get_rule_dependencies p r in
          let dep_indices :=
            flat_map (fun dep =>
                        match lookup_rule_number dep p 0 with
                        | Some idx => [idx]
                        | None => []
                        end) deps
          in
          (n, dep_indices) :: aux rs (n + 1)
      end
  in aux p 0.

Definition get_program_dependencies_flat (p : program) : list (nat * nat) :=
  flat_map (fun '(n, deps) => List.map (fun idx => (n, idx)) deps)
           (get_program_dependencies_by_index p).

Definition get_program_input_rels (p : program) : list rel :=
  dedup rel_eqb (flat_map get_rule_hyps_rels p).

Definition get_program_output_rels (p : program) : list rel :=
  dedup rel_eqb (flat_map get_rule_concls_rels p).

Fixpoint lookup_rel_number (R : rel) (rels : list rel) (n : nat) : option nat :=
  match rels with
  | [] => None
  | R' :: Rs =>
      if rel_eqb R R' then Some n
      else lookup_rel_number R Rs (n + 1)
  end.

Definition get_input_rels_depedencies (p : program) : list (rel * list rule) :=
  map (fun R =>
         let dependent_rules := filter (fun r => rel_appears_in_hyps R r) p in
         (R, dependent_rules))
      (get_program_input_rels p).

Definition get_input_rels_depedencies_by_index (p : program) : list (nat * list nat) :=
  let input_rels := get_program_input_rels p in
  let fix aux rels n :=
      match rels with
      | [] => []
      | R :: Rs =>
          let dependent_rules := filter (fun r => rel_appears_in_hyps R r) p in
          let dependent_rule_indices :=
            flat_map (fun r =>
                        match lookup_rule_number r p 0 with
                        | Some idx => [idx]
                        | None => []
                        end) dependent_rules
          in
          (n, dependent_rule_indices) :: aux Rs (n + 1)
      end
  in aux input_rels 0.

Definition get_input_rels_depedencies_flat (p : program) : list (nat * nat) :=
  flat_map (fun '(rel_idx, rule_indices) =>
               List.map (fun rule_idx => (rel_idx, rule_idx)) rule_indices)
           (get_input_rels_depedencies_by_index p).

Definition get_output_rels_dependencies (p : program) : list (rel * list rule) :=
  map (fun R =>
         let producing_rules := filter (fun r => rel_appears_in_concls R r) p in
         (R, producing_rules))
      (get_program_output_rels p).

Definition get_output_rels_dependencies_by_index (p : program) : list (nat * list nat) :=
  let output_rels := get_program_output_rels p in
  let output := get_program_output_rels p in
  let fix aux rels n :=
      match rels with
      | [] => []
      | R :: Rs =>
          let producing_rules := filter (fun r => rel_appears_in_concls R r) p in
          let producing_rule_indices :=
            flat_map (fun r =>
                        match lookup_rule_number r p 0 with
                        | Some idx => [idx]
                        | None => []
                        end) producing_rules
          in
          (n, producing_rule_indices) :: aux Rs (n + 1)
      end
  in aux output_rels 0.

Definition get_output_rels_dependencies_flat (p : program) : list (nat * nat) :=
  flat_map (fun '(rel_idx, rule_indices) =>
               List.map (fun rule_idx => (rule_idx, rel_idx)) rule_indices)
           (get_output_rels_dependencies_by_index p).

End DependencyGenerator.
