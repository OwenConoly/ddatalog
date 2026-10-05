From Stdlib Require Import Strings.String List.
From Datalog Require Import Datalog.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope string_scope.

Import StringDatalogParams.

(* Individual rules, written with plain (non-fancy) clause/rule.impl syntax.
   [ {| clause.rel := R; clause.args := [...] |} ] are the conclusions, then the hypotheses. *)

Definition r_ancestor1 : rule :=
  rule.impl
    [ {| clause.rel := "ancestor"; clause.args := [expr.var "x"; expr.var "y"] |} ]
    [ {| clause.rel := "parent";   clause.args := [expr.var "x"; expr.var "y"] |} ].

Definition r_ancestor2 : rule :=
  rule.impl
    [ {| clause.rel := "ancestor"; clause.args := [expr.var "y"; expr.var "x"] |} ]
    [ {| clause.rel := "parent";   clause.args := [expr.var "p"; expr.var "x"] |};
      {| clause.rel := "ancestor"; clause.args := [expr.var "y"; expr.var "p"] |} ].

Definition r_sibling : rule :=
  rule.impl
    [ {| clause.rel := "sibling"; clause.args := [expr.var "x"; expr.var "y"] |} ]
    [ {| clause.rel := "parent";  clause.args := [expr.var "p"; expr.var "x"] |};
      {| clause.rel := "parent";  clause.args := [expr.var "p"; expr.var "y"] |} ].

Definition r_aunt: rule :=
  rule.impl
    [ {| clause.rel := "aunt"; clause.args := [expr.var "x"; expr.var "y"] |} ]
    [ {| clause.rel := "sibling"; clause.args := [expr.var "x"; expr.var "p"] |};
      {| clause.rel := "parent";  clause.args := [expr.var "p"; expr.var "y"] |};
      {| clause.rel := "female";  clause.args := [expr.var "x"] |} ].

Definition r_uncle : rule :=
  rule.impl
    [ {| clause.rel := "uncle"; clause.args := [expr.var "x"; expr.var "y"] |} ]
    [ {| clause.rel := "sibling"; clause.args := [expr.var "x"; expr.var "p"] |};
      {| clause.rel := "parent";  clause.args := [expr.var "p"; expr.var "y"] |};
      {| clause.rel := "male";    clause.args := [expr.var "x"] |} ].

Definition r_cousin : rule :=
  rule.impl
    [ {| clause.rel := "cousin"; clause.args := [expr.var "x"; expr.var "y"] |} ]
    [ {| clause.rel := "parent";  clause.args := [expr.var "px"; expr.var "x"] |};
      {| clause.rel := "parent";  clause.args := [expr.var "py"; expr.var "y"] |};
      {| clause.rel := "sibling"; clause.args := [expr.var "px"; expr.var "py"] |} ].

Definition r_related1 : rule :=
  rule.impl
    [ {| clause.rel := "related";  clause.args := [expr.var "x"; expr.var "y"] |} ]
    [ {| clause.rel := "ancestor"; clause.args := [expr.var "x"; expr.var "y"] |} ].

Definition r_related2 : rule :=
  rule.impl
    [ {| clause.rel := "related";  clause.args := [expr.var "x"; expr.var "y"] |} ]
    [ {| clause.rel := "ancestor"; clause.args := [expr.var "y"; expr.var "x"] |} ].

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