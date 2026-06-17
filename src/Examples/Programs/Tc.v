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


(* Nullary function application = constant value *)
Definition const (c : string) : expr := fun_expr c [].

(* ------------------------------------------------------------------ *)
(* Schema                                                               *)
(* ------------------------------------------------------------------ *)
(* .decl  tcl(node1:number{->Z}, node2:number{->Z}) *)
(* .decl  tcr(node1:number{->Z}, node2:number{->Z}) *)
(* .decl  base(node1:number{->Z}, node2:number{->Z}) *)
(* .decl  tc(node1:number{->Z}, node2:number{->Z}) *)

(* tcl(X, Y) :- base(X, Y). *)
Definition rule_0 : rule :=
normal_rule ([
      {| clause_rel := "tcl"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| clause_rel := "base"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]).

(* tcl(X, Y) :- tcl(X, Z), base(Z, Y). *)
Definition rule_1 : rule :=
normal_rule ([
      {| clause_rel := "tcl"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| clause_rel := "tcl"; clause_args := [(var_expr "X"); (var_expr "Z")] |};
      {| clause_rel := "base"; clause_args := [(var_expr "Z"); (var_expr "Y")] |}
    ]).

(* tcr(X, Y) :- base(X, Y). *)
Definition rule_2 : rule :=
normal_rule ([
      {| clause_rel := "tcr"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| clause_rel := "base"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]).

(* tcr(X, Y) :- base(X, Z), tcr(Z, Y). *)
Definition rule_3 : rule :=
normal_rule ([
      {| clause_rel := "tcr"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| clause_rel := "base"; clause_args := [(var_expr "X"); (var_expr "Z")] |};
      {| clause_rel := "tcr"; clause_args := [(var_expr "Z"); (var_expr "Y")] |}
    ]).

(* tc(X, Y) :- base(X, Y). *)
Definition rule_4 : rule :=
normal_rule ([
      {| clause_rel := "tc"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| clause_rel := "base"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]).

(* tc(X, Y) :- tc(X, Z), tc(Z, Y). *)
Definition rule_5 : rule :=
normal_rule ([
      {| clause_rel := "tc"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| clause_rel := "tc"; clause_args := [(var_expr "X"); (var_expr "Z")] |};
      {| clause_rel := "tc"; clause_args := [(var_expr "Z"); (var_expr "Y")] |}
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
  DependencyGenerator.get_program_dependencies (expr_compatible := expr_compatible)
    p.

Definition get_rule_dependencies (p : list rule) (r : rule) :=
  DependencyGenerator.get_rule_dependencies (expr_compatible := expr_compatible)
    p r.

Definition get_program_dependencies_flat (p : list rule) :=
  DependencyGenerator.get_program_dependencies_flat
    (expr_compatible := expr_compatible)
    p.

Compute get_program_dependencies computed_program.
Compute get_rule_dependencies
        computed_program
        rule_1.

Compute get_program_dependencies_flat computed_program.