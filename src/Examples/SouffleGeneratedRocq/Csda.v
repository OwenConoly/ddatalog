(* Auto-generated from SouffleExamples/csda.dl by souffle_to_rocq *)
From Stdlib Require Import Strings.String List Bool.
From Datalog Require Import Datalog.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.

(* {0: (0, 1), 1: (0, 0)} *)

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
(* .decl  nullEdge(x:symbol{->string}, y:symbol{->string}) *)
(* .decl  arc(x:symbol{->string}, y:symbol{->string}) *)
(* .decl  null(x:symbol{->string}, y:symbol{->string}) *)
(* .input  nullEdge *)
(* .input  arc *)
(* .output null *)

(* null(X, Y) :- nullEdge(X, Y). *)
Definition rule_0 : rule :=
normal_rule ([
      {| clause_rel := "null"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| clause_rel := "nullEdge"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]).

(* null(X, Y) :- null(X, W), arc(W, Y). *)
Definition rule_1 : rule :=
normal_rule ([
      {| clause_rel := "null"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| clause_rel := "null"; clause_args := [(var_expr "X"); (var_expr "W")] |};
      {| clause_rel := "arc"; clause_args := [(var_expr "W"); (var_expr "Y")] |}
    ]).

Definition program : list rule :=
  [rule_0;
   rule_1].

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