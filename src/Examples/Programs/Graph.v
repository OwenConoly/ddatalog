From Stdlib Require Import Strings.String List.
From Datalog Require Import Datalog FancyNotations.
From Datalog Require Import FancyNotations.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope string_scope.

Import StringDatalogParams.

Definition path_base_r : rule := datalog_rule:([ Path($a, $b) ] :- [ Edge($a, $b) ]).
Definition path_step_r : rule := datalog_rule:([ Path($a, $c) ] :- [ Edge($a, $b); Path($b, $c) ]).
Definition two_step_r : rule := datalog_rule:([ TwoStep($a, $c) ] :- [ Edge($a, $b); Edge($b, $c) ]).
Definition cycle_r : rule := datalog_rule:([ Cycle($a) ] :- [ Path($a, $a) ]).
Definition triangle_r : rule := datalog_rule:([ Triangle($a, $b) ] :- [ Edge($a, $b); Edge($b, $c); Edge($c, $a) ]).
Definition bipath_r : rule := datalog_rule:([ BiPath($a, $b) ] :- [ Path($a, $b); Path($b, $a) ]).

Definition graph_program : list rule :=
   [ path_base_r;
    path_step_r;
    two_step_r;
    cycle_r;
    triangle_r;
    bipath_r ].

Definition name_overrides : list (rule * string) :=
  [ (path_base_r, "path_base");
    (path_step_r, "path_step");
    (two_step_r, "two_step");
    (cycle_r, "cycle");
    (triangle_r, "triangle");
    (bipath_r, "bipath")
  ].


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

Compute get_program_dependencies graph_program.
Compute get_program_dependencies_flat graph_program.