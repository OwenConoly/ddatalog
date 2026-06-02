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
Datalog.normal_rule ([
      {| Datalog.clause_rel := "valueFlow"; Datalog.clause_args := [(var_expr "Y"); (var_expr "X")] |}
    ]) ([
      {| Datalog.clause_rel := "assign"; Datalog.clause_args := [(var_expr "Y"); (var_expr "X")] |}
    ]).

(* valueFlow(X, X) :- assign(X, Y). *)
Definition rule_1 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "valueFlow"; Datalog.clause_args := [(var_expr "X"); (var_expr "X")] |}
    ]) ([
      {| Datalog.clause_rel := "assign"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]).

(* valueFlow(X, X) :- assign(Y, X). *)
Definition rule_2 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "valueFlow"; Datalog.clause_args := [(var_expr "X"); (var_expr "X")] |}
    ]) ([
      {| Datalog.clause_rel := "assign"; Datalog.clause_args := [(var_expr "Y"); (var_expr "X")] |}
    ]).

(* valueFlow(X, Y) :- assign(X, Z), memoryAlias(Z, Y). *)
Definition rule_3 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "valueFlow"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| Datalog.clause_rel := "assign"; Datalog.clause_args := [(var_expr "X"); (var_expr "Z")] |};
      {| Datalog.clause_rel := "memoryAlias"; Datalog.clause_args := [(var_expr "Z"); (var_expr "Y")] |}
    ]).

(* valueFlow(X, Y) :- valueFlow(X, Z), valueFlow(Z, Y). *)
Definition rule_4 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "valueFlow"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| Datalog.clause_rel := "valueFlow"; Datalog.clause_args := [(var_expr "X"); (var_expr "Z")] |};
      {| Datalog.clause_rel := "valueFlow"; Datalog.clause_args := [(var_expr "Z"); (var_expr "Y")] |}
    ]).

(* valueAlias(X, Y) :- valueFlow(Z, X), valueFlow(Z, Y). *)
Definition rule_5 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "valueAlias"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| Datalog.clause_rel := "valueFlow"; Datalog.clause_args := [(var_expr "Z"); (var_expr "X")] |};
      {| Datalog.clause_rel := "valueFlow"; Datalog.clause_args := [(var_expr "Z"); (var_expr "Y")] |}
    ]).

(* valueAlias(X, Y) :- valueFlow(Z, X), memoryAlias(Z, W), valueFlow(W, Y). *)
Definition rule_6 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "valueAlias"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]) ([
      {| Datalog.clause_rel := "valueFlow"; Datalog.clause_args := [(var_expr "Z"); (var_expr "X")] |};
      {| Datalog.clause_rel := "memoryAlias"; Datalog.clause_args := [(var_expr "Z"); (var_expr "W")] |};
      {| Datalog.clause_rel := "valueFlow"; Datalog.clause_args := [(var_expr "W"); (var_expr "Y")] |}
    ]).

(* memoryAlias(X, X) :- assign(Y, X). *)
Definition rule_7 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "memoryAlias"; Datalog.clause_args := [(var_expr "X"); (var_expr "X")] |}
    ]) ([
      {| Datalog.clause_rel := "assign"; Datalog.clause_args := [(var_expr "Y"); (var_expr "X")] |}
    ]).

(* memoryAlias(X, X) :- assign(X, Y). *)
Definition rule_8 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "memoryAlias"; Datalog.clause_args := [(var_expr "X"); (var_expr "X")] |}
    ]) ([
      {| Datalog.clause_rel := "assign"; Datalog.clause_args := [(var_expr "X"); (var_expr "Y")] |}
    ]).

(* memoryAlias(X, W) :- dereference(Y, X), valueAlias(Y, Z), dereference(Z, W). *)
Definition rule_9 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "memoryAlias"; Datalog.clause_args := [(var_expr "X"); (var_expr "W")] |}
    ]) ([
      {| Datalog.clause_rel := "dereference"; Datalog.clause_args := [(var_expr "Y"); (var_expr "X")] |};
      {| Datalog.clause_rel := "valueAlias"; Datalog.clause_args := [(var_expr "Y"); (var_expr "Z")] |};
      {| Datalog.clause_rel := "dereference"; Datalog.clause_args := [(var_expr "Z"); (var_expr "W")] |}
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