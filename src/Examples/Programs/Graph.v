From Stdlib Require Import Strings.String List.
From Datalog Require Import Datalog FancyNotations.
From Datalog Require Import FancyNotations.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope string_scope.

Import StringDatalogParams.

Definition r_path_base : rule := 
  datalog_rule:([ Path($a, $b) ] :- [ Edge($a, $b) ]).

Definition r_path_step : rule := 
  datalog_rule:([ Path($a, $c) ] :- [ Edge($a, $b); Path($b, $c) ]).

Definition r_two_step : rule := 
  datalog_rule:([ TwoStep($a, $c) ] :- [ Edge($a, $b); Edge($b, $c) ]).

Definition r_cycle : rule := 
  datalog_rule:([ Cycle($a) ] :- [ Path($a, $a) ]).

Definition r_triangle : rule := 
  datalog_rule:([ Triangle($a, $b) ] :- [ Edge($a, $b); Edge($b, $c); Edge($c, $a) ]).

Definition r_bipath : rule := 
  datalog_rule:([ BiPath($a, $b) ] :- [ Path($a, $b); Path($b, $a) ]).

Definition graph_program : list rule :=
   [ r_path_base;
    r_path_step;
    r_two_step;
    r_cycle;
    r_triangle;
    r_bipath ].

Definition name_overrides : list (rule * string) :=
  [ (r_path_base, "path_base");
    (r_path_step, "path_step");
    (r_two_step, "two_step");
    (r_cycle, "cycle");
    (r_triangle, "triangle");
    (r_bipath, "bipath")
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
    (aggregator_eqb := aggregator_eqb) (rel_eqb := rel_eqb)
    (expr_compatible := expr_compatible) (fn_eqb := fn_eqb) (var_eqb := var_eqb)
    p.

Compute get_program_dependencies graph_program.
Compute get_program_dependencies_flat graph_program.