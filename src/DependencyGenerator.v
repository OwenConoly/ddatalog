(* This takes a datalog program, and for every rule, it generates the rules that it might depend on
   which will then be fed into gurobi to find an optimal layout. *)

From Stdlib Require Import List String Bool ZArith Lia.
From coqutil Require Import Datatypes.List Datatypes.Option Map.Interface Tactics Tactics.fwd Eqb.
From Datalog Require Import Datalog List Eqb.
From DatalogRocq Require Import EqbSpec.

Import ListNotations.
Open Scope bool_scope.

Section DependencyGenerator.

Context {rel : relT} {var : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
Context `{sig : signature fn aggregator T}.
Context {context : map.map var T} {context_ok : map.ok context}.
Context {var_eqb : Eqb var} {rel_eqb : Eqb rel} {fn_eqb : Eqb fn} {aggregator_eqb : Eqb aggregator}.

Definition program := list rule.

Context {expr_compatible : expr -> expr -> bool}.

(* Basic Utilities *)

Definition is_var (e : expr) : bool :=
  match e with
  | var_expr _ => true
  | _ => false
  end.

Definition is_const (e : expr) : bool :=
  match e with
  | fun_expr _ [] => true
  | _ => false
  end.

Definition is_fun_app (e : expr) : bool :=
  match e with
  | fun_expr _ (_::_) => true
  | _ => false
  end.

Definition get_var (e : expr) : option var :=
  match e with
  | var_expr v => Some v
  | _ => None
  end.

Definition get_const (e : expr) : option fn :=
  match e with
  | fun_expr f [] => Some f
  | _ => None
  end.

Definition dedup {A} {aeqb : Eqb A} (lst : list A) : list A :=
  fold_right (fun x acc =>
                if existsb (eqb x) acc then acc
                else x :: acc) [] lst.

(* [Eqb] for [clause]/[meta_clause]/[rule] lives in [EqbSpec]; here we just use [eqb]. *)

(* Pruning.  The compiler only ever produces [normal_rule]s (the bare fragment),
   so concls/hyps are read by matching that constructor directly. *)
Definition prune_empty_concl_rules (p : program) : program :=
  filter (fun r => match r with
                   | normal_rule concls _ => negb (eqb concls [])
                   | _ => false
                   end) p.

(* Collect *)
Fixpoint collect_vars (e : expr) : list var :=
  match e with
  | var_expr v => [v]
  | fun_expr _ args =>
      flat_map collect_vars args
  end.

Fixpoint collect_consts (e : expr) : list fn :=
  match e with
  | var_expr _ => []
  | fun_expr f [] => [f]
  | fun_expr _ args =>
      flat_map collect_consts args
  end.

Fixpoint collect_funs (e : expr) : list fn :=
  match e with
  | var_expr _ => []
  | fun_expr f args =>
      f :: flat_map collect_funs args
  end.

(* Collect from a clause *)

Definition collect_vars_from_clause (c : clause) : list var :=
  flat_map collect_vars (clause_args c).

Definition collect_consts_from_clause (c : clause) : list fn :=
  flat_map collect_consts (clause_args c).

Definition collect_funs_from_clause (c : clause) : list fn :=
  flat_map collect_funs (clause_args c).

Definition is_abstract (c : clause) : bool :=
  forallb is_var (clause_args c).

Definition is_grounded_clause (c : clause) : bool :=
  forallb is_const (clause_args c).

(* Collect for Rules.  Only [normal_rule]s arise in the bare fragment, so we
   match that constructor directly (meta/agg rules contribute nothing here). *)

Definition collect_vars_from_hyps (r : rule) : list var :=
  match r with normal_rule _ hyps => flat_map collect_vars_from_clause hyps | _ => [] end.

Definition collect_vars_from_concls (r : rule) : list var :=
  match r with normal_rule concls _ => flat_map collect_vars_from_clause concls | _ => [] end.

Definition collect_vars_from_rule (r : rule) : list var :=
  collect_vars_from_hyps r ++ collect_vars_from_concls r.

Definition collect_consts_from_hyps (r : rule) : list fn :=
  match r with normal_rule _ hyps => flat_map collect_consts_from_clause hyps | _ => [] end.

Definition collect_consts_from_concls (r : rule) : list fn :=
  match r with normal_rule concls _ => flat_map collect_consts_from_clause concls | _ => [] end.

Definition collect_consts_from_rule (r : rule) : list fn :=
  collect_consts_from_hyps r ++ collect_consts_from_concls r.

Definition collect_funs_from_hyps (r : rule) : list fn :=
  match r with normal_rule _ hyps => flat_map collect_funs_from_clause hyps | _ => [] end.

Definition collect_funs_from_concls (r : rule) : list fn :=
  match r with normal_rule concls _ => flat_map collect_funs_from_clause concls | _ => [] end.

Definition collect_funs_from_rule (r : rule) : list fn :=
  collect_funs_from_hyps r ++ collect_funs_from_concls r.

Definition get_rule_concls_rels (r : rule) : list rel := concl_rels r.

Definition get_rule_hyps_rels (r : rule) : list rel := hyp_rels r.

(* Pattern Matching.  No aggregation: a rule's hypotheses are just its
   [normal_rule] hyps (no agg hyps to append). *)

Definition get_all_hyps (r : rule) : list clause :=
  match r with normal_rule _ hyps => hyps | _ => [] end.

Definition clauses_compatible (c1 c2 : clause) : bool :=
  eqb (clause_rel c1) (clause_rel c2) &&
  list_eqb (aeqb := expr_compatible) (clause_args c1) (clause_args c2).

Definition conc_matches_hyp (conc hyp : clause) : bool :=
  clauses_compatible conc hyp.

Definition rule_concls_match_hyps (r1 r2 : rule) : bool :=
  existsb (fun conc =>
    existsb (fun hyp => conc_matches_hyp conc hyp) (get_all_hyps r2)
  ) (match r1 with normal_rule concls _ => concls | _ => [] end).

Definition rule_depends_on (r1 r2 : rule) : bool :=
  rule_concls_match_hyps r1 r2.

Definition get_rule_dependencies (p : program) (r : rule) : program :=
  filter (fun r' => rule_depends_on r' r) p.

Definition get_rules_dependent_on (p : program) (r : rule) : program :=
  filter (fun r' => rule_depends_on r r') p.

Definition rel_appears_in_hyps (R : rel) (r : rule) : bool :=
  existsb (fun c => eqb (clause_rel c) R)
    (match r with normal_rule _ hyps => hyps | _ => [] end).

Definition rel_appears_in_concls (R : rel) (r : rule) : bool :=
  existsb (fun c => eqb (clause_rel c) R)
    (match r with normal_rule concls _ => concls | _ => [] end).

(* Program Dependencies *)

Definition get_program_dependencies (p : program) : list (rule * list rule) :=
  map (fun r => (r, get_rule_dependencies p r)) p.

Fixpoint lookup_rule_number (r : rule) (p : program) (n : nat) : option nat :=
  match p with
  | [] => None
  | r' :: ps =>
      if eqb r r' then Some n
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
  dedup (flat_map get_rule_hyps_rels p).

Definition get_program_output_rels (p : program) : list rel :=
  dedup (flat_map get_rule_concls_rels p).

Fixpoint lookup_rel_number (R : rel) (rels : list rel) (n : nat) : option nat :=
  match rels with
  | [] => None
  | R' :: Rs =>
      if eqb R R' then Some n
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
