From Stdlib Require Import Strings.String List.
From Datalog Require Import Datalog FancyNotations.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope string_scope.

Import StringDatalogParams.

Module family_examples.

(* Individual rules using fancy Datalog notation *)

Definition r_ancestor1 : rule :=
  datalog_rule:( [ ancestor($x, $y) ] :- [ parent($x, $y) ] ).

Definition r_ancestor2 : rule :=
  datalog_rule:( [ ancestor($x, $y) ] :- [ parent($x, $z); ancestor($z, $y) ] ).

Definition r_sibling : rule :=
  datalog_rule:( [ sibling($x, $y) ] :- [ parent($p, $x); parent($p, $y) ] ).

Definition r_aunt_uncle : rule :=
  datalog_rule:( [ aunt_uncle($x, $y) ] :- [ sibling($x, $p); parent($p, $y) ] ).

Definition r_cousin : rule :=
  datalog_rule:( [ cousin($x, $y) ] :- [ parent($px, $x); parent($py, $y); sibling($px, $py) ] ).

(* The full program, referencing the rules directly *)
Definition family_program : list rule :=
  [ r_ancestor1;
    r_ancestor2;
    r_sibling;
    r_aunt_uncle;
    r_cousin ].

End family_examples.

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

(* Example computations *)
Compute get_program_dependencies family_examples.family_program.
Compute get_rule_dependencies
        family_examples.family_program
        family_examples.r_ancestor2.

Compute get_program_dependencies_flat
        family_examples.family_program.