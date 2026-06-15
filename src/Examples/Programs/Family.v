From Stdlib Require Import Strings.String List.
From Datalog Require Import Datalog.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope string_scope.

Import StringDatalogParams.

(* Individual rules, written with plain (non-fancy) clause/normal_rule syntax.
   [ {| clause_rel := R; clause_args := [...] |} ] are the conclusions, then the hypotheses. *)

Definition r_ancestor1 : rule :=
  normal_rule
    [ {| clause_rel := "ancestor"; clause_args := [var_expr "x"; var_expr "y"] |} ]
    [ {| clause_rel := "parent";   clause_args := [var_expr "x"; var_expr "y"] |} ].

Definition r_ancestor2 : rule :=
  normal_rule
    [ {| clause_rel := "ancestor"; clause_args := [var_expr "y"; var_expr "x"] |} ]
    [ {| clause_rel := "parent";   clause_args := [var_expr "p"; var_expr "x"] |};
      {| clause_rel := "ancestor"; clause_args := [var_expr "y"; var_expr "p"] |} ].

Definition r_sibling : rule :=
  normal_rule
    [ {| clause_rel := "sibling"; clause_args := [var_expr "x"; var_expr "y"] |} ]
    [ {| clause_rel := "parent";  clause_args := [var_expr "p"; var_expr "x"] |};
      {| clause_rel := "parent";  clause_args := [var_expr "p"; var_expr "y"] |} ].

Definition r_aunt: rule :=
  normal_rule
    [ {| clause_rel := "aunt"; clause_args := [var_expr "x"; var_expr "y"] |} ]
    [ {| clause_rel := "sibling"; clause_args := [var_expr "x"; var_expr "p"] |};
      {| clause_rel := "parent";  clause_args := [var_expr "p"; var_expr "y"] |};
      {| clause_rel := "female";  clause_args := [var_expr "x"] |} ].

Definition r_uncle : rule :=
  normal_rule
    [ {| clause_rel := "uncle"; clause_args := [var_expr "x"; var_expr "y"] |} ]
    [ {| clause_rel := "sibling"; clause_args := [var_expr "x"; var_expr "p"] |};
      {| clause_rel := "parent";  clause_args := [var_expr "p"; var_expr "y"] |};
      {| clause_rel := "male";    clause_args := [var_expr "x"] |} ].

Definition r_cousin : rule :=
  normal_rule
    [ {| clause_rel := "cousin"; clause_args := [var_expr "x"; var_expr "y"] |} ]
    [ {| clause_rel := "parent";  clause_args := [var_expr "px"; var_expr "x"] |};
      {| clause_rel := "parent";  clause_args := [var_expr "py"; var_expr "y"] |};
      {| clause_rel := "sibling"; clause_args := [var_expr "px"; var_expr "py"] |} ].

Definition r_related1 : rule :=
  normal_rule
    [ {| clause_rel := "related";  clause_args := [var_expr "x"; var_expr "y"] |} ]
    [ {| clause_rel := "ancestor"; clause_args := [var_expr "x"; var_expr "y"] |} ].

Definition r_related2 : rule :=
  normal_rule
    [ {| clause_rel := "related";  clause_args := [var_expr "x"; var_expr "y"] |} ]
    [ {| clause_rel := "ancestor"; clause_args := [var_expr "y"; var_expr "x"] |} ].

(* The full program, referencing the rules directly *)
Definition family_program : list rule :=
  [ r_ancestor1;
    r_ancestor2;
    r_sibling;
    r_aunt;
    r_uncle;
    r_cousin;
    r_related1;
    r_related2].


Definition name_overrides : list (rule * string) :=
  [ (r_ancestor1, "ancestor1");
    (r_ancestor2, "ancestor2");
    (r_sibling, "sibling");
    (r_aunt, "aunt");
    (r_uncle, "uncle");
    (r_cousin, "cousin");
    (r_related1, "related1");
    (r_related2, "related2")
  ].

(* Temp fix, may use typeclasses later *)
Definition get_program_dependencies (p : list rule) :=
  DependencyGenerator.get_program_dependencies (expr_compatible := expr_compatible)
    p.

Definition get_rule_dependencies (p : list rule) (r : rule) :=
  DependencyGenerator.get_rule_dependencies (expr_compatible := expr_compatible)
    p r.

Definition get_program_dependencies_flat (p : list rule) :=
  DependencyGenerator.get_program_dependencies_flat
    (expr_compatible := expr_compatible)
    p.

(* Example computations *)
Compute get_program_dependencies family_program.
Compute get_rule_dependencies
        family_program
        r_ancestor2.

Compute get_program_dependencies_flat family_program.