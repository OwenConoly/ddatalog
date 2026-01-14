From Stdlib Require Import Strings.String List.
From Datalog Require Import Datalog FancyNotations.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope string_scope.

Import StringDatalogParams.

(* Individual rules using fancy Datalog notation *)

Definition r_ancestor1 : rule :=
  datalog_rule:( [ ancestor($x, $y) ] :- [ parent($x, $y) ] ).

Definition r_ancestor2 : rule :=
  datalog_rule:( [ ancestor($y, $x) ] :- [ parent($p, $x); ancestor($y, $p) ] ).

Definition r_sibling : rule :=
  datalog_rule:( [ sibling($x, $y) ] :- [ parent($p, $x); parent($p, $y) ] ).

Definition r_aunt: rule :=
  datalog_rule:( [ aunt($x, $y) ] :- [ sibling($x, $p); parent($p, $y); female($x) ] ).

Definition r_uncle : rule :=
  datalog_rule:( [ uncle($x, $y) ] :- [ sibling($x, $p); parent($p, $y); male($x) ] ).

Definition r_cousin : rule :=
  datalog_rule:( [ cousin($x, $y) ] :- [ parent($px, $x); parent($py, $y); sibling($px, $py) ] ).

Definition r_related1 : rule :=
  datalog_rule:( [ related($x, $y) ] :- [ ancestor($x, $y) ] ).

Definition r_related2 : rule :=
  datalog_rule:( [ related($x, $y) ] :- [ ancestor($y, $x) ] ).

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
Compute get_program_dependencies family_program.
Compute get_rule_dependencies
        family_program
        r_ancestor2.

Compute get_program_dependencies_flat family_program.