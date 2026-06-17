(* Auto-generated from SouffleExamples/trans.dl by souffle_to_rocq *)
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
(* .decl  A(x:number{->Z}, y:number{->Z}) *)

(* A(x, z) :- A(x, y), A(y, z). *)
Definition rule_0 : rule :=
normal_rule ([
      {| clause_rel := "A"; clause_args := [(var_expr "x"); (var_expr "z")] |}
    ]) ([
      {| clause_rel := "A"; clause_args := [(var_expr "x"); (var_expr "y")] |};
      {| clause_rel := "A"; clause_args := [(var_expr "y"); (var_expr "z")] |}
    ]).

Definition program : list rule :=
  [rule_0].

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
        rule_0.

Compute get_program_dependencies_flat computed_program.