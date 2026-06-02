From Stdlib Require Import Strings.String List.
From Datalog Require Import Datalog.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope string_scope.

Import StringDatalogParams.

Definition r_path_base : rule :=
  normal_rule
    [ {| clause_rel := "Path"; clause_args := [var_expr "a"; var_expr "b"] |} ]
    [ {| clause_rel := "Edge"; clause_args := [var_expr "a"; var_expr "b"] |} ].

Definition r_path_step : rule :=
  normal_rule
    [ {| clause_rel := "Path"; clause_args := [var_expr "a"; var_expr "c"] |} ]
    [ {| clause_rel := "Edge"; clause_args := [var_expr "a"; var_expr "b"] |};
      {| clause_rel := "Path"; clause_args := [var_expr "b"; var_expr "c"] |} ].

Definition r_two_step : rule :=
  normal_rule
    [ {| clause_rel := "TwoStep"; clause_args := [var_expr "a"; var_expr "c"] |} ]
    [ {| clause_rel := "Edge"; clause_args := [var_expr "a"; var_expr "b"] |};
      {| clause_rel := "Edge"; clause_args := [var_expr "b"; var_expr "c"] |} ].

Definition r_cycle : rule :=
  normal_rule
    [ {| clause_rel := "Cycle"; clause_args := [var_expr "a"] |} ]
    [ {| clause_rel := "Path"; clause_args := [var_expr "a"; var_expr "a"] |} ].

Definition r_triangle : rule :=
  normal_rule
    [ {| clause_rel := "Triangle"; clause_args := [var_expr "a"; var_expr "b"] |} ]
    [ {| clause_rel := "Edge"; clause_args := [var_expr "a"; var_expr "b"] |};
      {| clause_rel := "Edge"; clause_args := [var_expr "b"; var_expr "c"] |};
      {| clause_rel := "Edge"; clause_args := [var_expr "c"; var_expr "a"] |} ].

Definition r_bipath : rule :=
  normal_rule
    [ {| clause_rel := "BiPath"; clause_args := [var_expr "a"; var_expr "b"] |} ]
    [ {| clause_rel := "Path"; clause_args := [var_expr "a"; var_expr "b"] |};
      {| clause_rel := "Path"; clause_args := [var_expr "b"; var_expr "a"] |} ].

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