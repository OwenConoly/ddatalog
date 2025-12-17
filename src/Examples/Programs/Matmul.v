From Stdlib Require Import Strings.String List.
From Datalog Require Import Datalog FancyNotations CompilerExamples.
From DatalogRocq Require Import ATLDatalogParams DependencyGenerator.
Import ListNotations.
Import ATLToDatalog.
Open Scope string_scope.

Import ATLDatalogParams.

(* Temp fix, may use typeclasses later *)
Definition get_program_dependencies (p : list rule) :=
  DependencyGenerator.get_program_dependencies
    (rel := rel) (var := var) (fn := fn) (aggregator := aggregator)
    (rel_eqb := rel_eqb) (expr_compatible := expr_compatible)
    p.

Definition get_rule_dependencies (p : list rule) (r : rule) :=
  DependencyGenerator.get_rule_dependencies
    (rel := rel) (var := var) (fn := fn) (aggregator := aggregator)
    (rel_eqb := rel_eqb) (expr_compatible := expr_compatible)
    p r.

Definition get_program_dependencies_flat (p : list rule) :=
  DependencyGenerator.get_program_dependencies_flat
    (rel := rel) (var := var) (fn := fn) (aggregator := aggregator)
    (rel_eqb := rel_eqb) (expr_compatible := expr_compatible)
    (fn_eqb := fn_eqb) (var_eqb := var_eqb)
    p.

Definition prune_empty_concl_rules (p : list rule) :=
  DependencyGenerator.prune_empty_concl_rules
    (rel := rel) (var := var) (fn := fn) (aggregator := aggregator)
    (rel_eqb := rel_eqb) (fn_eqb := fn_eqb) (var_eqb := var_eqb)
    p.

(* Example computations *)

Compute get_program_dependencies datalog_matmul.
Definition empty_rule : rule :=
  datalog_rule:( [ ] :- [ ] ).

Compute (length datalog_matmul).
Compute get_rule_dependencies
        datalog_matmul
        (nth 0 datalog_matmul empty_rule).
Compute get_program_dependencies_flat datalog_matmul.
Compute prune_empty_concl_rules datalog_matmul.
Print datalog_matmul.