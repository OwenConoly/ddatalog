(* Auto-generated from SouffleExamples/cspa.dl by souffle_to_rocq *)
From Stdlib Require Import Strings.String List Bool.
From Datalog Require Import Datalog.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.

(* {0: (2, 2), 1: (0, 1), 2: (0, 2), 3: (1, 0), 4: (1, 2), 5: (2, 1), 6: (1, 1), 7: (2, 0), 8: (0, 0), 9: (1, 1)} *)

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
(* .decl  assign(x:symbol{->string}, y:symbol{->string}) *)
(* .decl  dereference(x:symbol{->string}, y:symbol{->string}) *)
(* .decl  valueFlow(x:symbol{->string}, y:symbol{->string}) *)
(* .decl  valueAlias(x:symbol{->string}, y:symbol{->string}) *)
(* .decl  memoryAlias(x:symbol{->string}, y:symbol{->string}) *)
(* .input  assign *)
(* .input  dereference *)
(* .output valueFlow *)
(* .output valueAlias *)
(* .output memoryAlias *)

(* valueFlow(Y, X) :- assign(Y, X). *)
Definition rule_0 : rule :=
normal_rule ([
      {| clause_rel := "valueFlow"; clause_args := [(var_expr "Y"); (var_expr "X")] |}
    ]) ([
      {| clause_rel := "assign"; clause_args := [(var_expr "Y"); (var_expr "X")] |}
    ]).

(* valueFlow(X, X) :- assign(X, Y). *)
Definition rule_1 : rule :=
normal_rule ([
      {| clause_rel := "valueFlow"; clause_args := [(var_expr "X"); (var_expr "X")] |}
    ]) ([
      {| clause_rel := "assign"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]).

(* valueFlow(X, X) :- assign(Y, X). *)
Definition rule_2 : rule :=
normal_rule ([
      {| clause_rel := "valueFlow"; clause_args := [(var_expr "X"); (var_expr "X")] |}
    ]) ([
      {| clause_rel := "assign"; clause_args := [(var_expr "Y"); (var_expr "X")] |}
    ]).

(* valueFlow(X, Y) :- assign(X, Z), memoryAlias(Z, Y). *)
Definition rule_3 : rule :=
normal_rule ([
      {| clause_rel := "valueFlow"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| clause_rel := "assign"; clause_args := [(var_expr "X"); (var_expr "Z")] |};
      {| clause_rel := "memoryAlias"; clause_args := [(var_expr "Z"); (var_expr "Y")] |}
    ]).

(* valueFlow(X, Y) :- valueFlow(X, Z), valueFlow(Z, Y). *)
Definition rule_4 : rule :=
normal_rule ([
      {| clause_rel := "valueFlow"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| clause_rel := "valueFlow"; clause_args := [(var_expr "X"); (var_expr "Z")] |};
      {| clause_rel := "valueFlow"; clause_args := [(var_expr "Z"); (var_expr "Y")] |}
    ]).

(* valueAlias(X, Y) :- valueFlow(Z, X), valueFlow(Z, Y). *)
Definition rule_5 : rule :=
normal_rule ([
      {| clause_rel := "valueAlias"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| clause_rel := "valueFlow"; clause_args := [(var_expr "Z"); (var_expr "X")] |};
      {| clause_rel := "valueFlow"; clause_args := [(var_expr "Z"); (var_expr "Y")] |}
    ]).

(* valueAlias(X, Y) :- valueFlow(Z, X), memoryAlias(Z, W), valueFlow(W, Y). *)
Definition rule_6 : rule :=
normal_rule ([
      {| clause_rel := "valueAlias"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| clause_rel := "valueFlow"; clause_args := [(var_expr "Z"); (var_expr "X")] |};
      {| clause_rel := "memoryAlias"; clause_args := [(var_expr "Z"); (var_expr "W")] |};
      {| clause_rel := "valueFlow"; clause_args := [(var_expr "W"); (var_expr "Y")] |}
    ]).

(* memoryAlias(X, X) :- assign(Y, X). *)
Definition rule_7 : rule :=
normal_rule ([
      {| clause_rel := "memoryAlias"; clause_args := [(var_expr "X"); (var_expr "X")] |}
    ]) ([
      {| clause_rel := "assign"; clause_args := [(var_expr "Y"); (var_expr "X")] |}
    ]).

(* memoryAlias(X, X) :- assign(X, Y). *)
Definition rule_8 : rule :=
normal_rule ([
      {| clause_rel := "memoryAlias"; clause_args := [(var_expr "X"); (var_expr "X")] |}
    ]) ([
      {| clause_rel := "assign"; clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]).

(* memoryAlias(X, W) :- dereference(Y, X), valueAlias(Y, Z), dereference(Z, W). *)
Definition rule_9 : rule :=
normal_rule ([
      {| clause_rel := "memoryAlias"; clause_args := [(var_expr "X"); (var_expr "W")] |}
    ]) ([
      {| clause_rel := "dereference"; clause_args := [(var_expr "Y"); (var_expr "X")] |};
      {| clause_rel := "valueAlias"; clause_args := [(var_expr "Y"); (var_expr "Z")] |};
      {| clause_rel := "dereference"; clause_args := [(var_expr "Z"); (var_expr "W")] |}
    ]).

Definition program : list rule :=
  [rule_0;
   rule_1;
   rule_2;
   rule_3;
   rule_4;
   rule_5;
   rule_6;
   rule_7;
   rule_8;
   rule_9].

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