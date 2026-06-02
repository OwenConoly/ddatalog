(* Auto-generated from SouffleExamples/tc.dl by souffle_to_rocq *)
From Stdlib Require Import Strings.String List Bool.
From Stdlib Require Import ZArith.
From Datalog Require Import Datalog.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* Type parameters                                                      *)
(* Souffle relation/variable names are strings; we use string for       *)
(* rel, var, and fn.  aggregator = unit (aggregation not supported).    *)
(* ------------------------------------------------------------------ *)
Definition rel         := string.
Definition var         := string.
Definition fn          := string.
Definition aggregator  := unit.

Definition rule     := Datalog.rule     rel var fn aggregator.
Definition expr     := Datalog.expr     var fn.
Definition fact     := Datalog.clause     rel var fn.

(* Nullary function application = constant value *)
Definition const (c : fn) : expr := fun_expr c [].

(* ------------------------------------------------------------------ *)
(* Schema                                                               *)
(* ------------------------------------------------------------------ *)
(* .decl  tcl(node1:number{->Z}, node2:number{->Z}) *)
(* .decl  tcr(node1:number{->Z}, node2:number{->Z}) *)
(* .decl  base(node1:number{->Z}, node2:number{->Z}) *)
(* .decl  tc(node1:number{->Z}, node2:number{->Z}) *)

(* tcl(X, Y) :- base(X, Y). *)
Definition rule_0 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "tcl"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| Datalog.clause_rel := "base"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]).

(* tcl(X, Y) :- tcl(X, Z), base(Z, Y). *)
Definition rule_1 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "tcl"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| Datalog.clause_rel := "tcl"; Datalog.clause_args := [(var_expr "X"); (var_expr "Z")] |};
      {| Datalog.clause_rel := "base"; Datalog.clause_args := [(var_expr "Z"); (var_expr "Y")] |}
    ]).

(* tcr(X, Y) :- base(X, Y). *)
Definition rule_2 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "tcr"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| Datalog.clause_rel := "base"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]).

(* tcr(X, Y) :- base(X, Z), tcr(Z, Y). *)
Definition rule_3 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "tcr"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| Datalog.clause_rel := "base"; Datalog.clause_args := [(var_expr "X"); (var_expr "Z")] |};
      {| Datalog.clause_rel := "tcr"; Datalog.clause_args := [(var_expr "Z"); (var_expr "Y")] |}
    ]).

(* tc(X, Y) :- base(X, Y). *)
Definition rule_4 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "tc"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| Datalog.clause_rel := "base"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]).

(* tc(X, Y) :- tc(X, Z), tc(Z, Y). *)
Definition rule_5 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "tc"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| Datalog.clause_rel := "tc"; Datalog.clause_args := [(var_expr "X"); (var_expr "Z")] |};
      {| Datalog.clause_rel := "tc"; Datalog.clause_args := [(var_expr "Z"); (var_expr "Y")] |}
    ]).

Definition program : list rule :=
  [rule_0;
   rule_1;
   rule_2;
   rule_3;
   rule_4;
   rule_5].

Definition computed_program := Eval compute in program.
Print computed_program.


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
    
Compute get_program_dependencies computed_program.
Compute get_rule_dependencies
        computed_program
        rule_1.

Compute get_program_dependencies_flat computed_program.