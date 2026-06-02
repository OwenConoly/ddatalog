(* Auto-generated from SouffleExamples/pointsto.dl by souffle_to_rocq *)
From Stdlib Require Import Strings.String List Bool.
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
(* .type Variable <: symbol  {-> string} *)
(* .type Allocation <: symbol  {-> string} *)
(* .type Field <: symbol  {-> string} *)
(* .decl  AssignAlloc(var:Variable{->string}, heap:Allocation{->string}) *)
(* .decl  Assign(source:Variable{->string}, destination:Variable{->string}) *)
(* .decl  PrimitiveAssign(source:Variable{->string}, dest:Variable{->string}) *)
(* .decl  Load(base:Variable{->string}, dest:Variable{->string}, field:Field{->string}) *)
(* .decl  Store(source:Variable{->string}, base:Variable{->string}, field:Field{->string}) *)
(* .decl  VarPointsTo(var:Variable{->string}, heap:Allocation{->string}) *)
(* .decl  Alias(x:Variable{->string}, y:Variable{->string}) *)

(* Assign(var1, var2) :- PrimitiveAssign(var1, var2). *)
Definition rule_0 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "Assign"; Datalog.clause_args := [(var_expr "var1"); (var_expr "var2")] |}
    ]) ([
      {| Datalog.clause_rel := "PrimitiveAssign"; Datalog.clause_args := [(var_expr "var1"); (var_expr "var2")] |}
    ]).

(* Alias(instanceVar, iVar) :- VarPointsTo(instanceVar, instanceHeap), VarPointsTo(iVar, instanceHeap). *)
Definition rule_1 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "Alias"; Datalog.clause_args := [(var_expr "instanceVar"); (var_expr "iVar")] |}
    ]) ([
      {| Datalog.clause_rel := "VarPointsTo"; Datalog.clause_args := [(var_expr "instanceVar"); (var_expr "instanceHeap")] |};
      {| Datalog.clause_rel := "VarPointsTo"; Datalog.clause_args := [(var_expr "iVar"); (var_expr "instanceHeap")] |}
    ]).

(* VarPointsTo(var, heap) :- AssignAlloc(var, heap). *)
Definition rule_2 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "VarPointsTo"; Datalog.clause_args := [(var_expr "var"); (var_expr "heap")] |}
    ]) ([
      {| Datalog.clause_rel := "AssignAlloc"; Datalog.clause_args := [(var_expr "var"); (var_expr "heap")] |}
    ]).

(* VarPointsTo(var1, heap) :- Assign(var2, var1), VarPointsTo(var2, heap). *)
Definition rule_3 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "VarPointsTo"; Datalog.clause_args := [(var_expr "var1"); (var_expr "heap")] |}
    ]) ([
      {| Datalog.clause_rel := "Assign"; Datalog.clause_args := [(var_expr "var2"); (var_expr "var1")] |};
      {| Datalog.clause_rel := "VarPointsTo"; Datalog.clause_args := [(var_expr "var2"); (var_expr "heap")] |}
    ]).

(* Assign(var1, var2) :- Store(var1, instanceVar2, field), Alias(instanceVar2, instanceVar1), Load(instanceVar1, var2, field). *)
Definition rule_4 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "Assign"; Datalog.clause_args := [(var_expr "var1"); (var_expr "var2")] |}
    ]) ([
      {| Datalog.clause_rel := "Store"; Datalog.clause_args := [(var_expr "var1"); (var_expr "instanceVar2"); (var_expr "field")] |};
      {| Datalog.clause_rel := "Alias"; Datalog.clause_args := [(var_expr "instanceVar2"); (var_expr "instanceVar1")] |};
      {| Datalog.clause_rel := "Load"; Datalog.clause_args := [(var_expr "instanceVar1"); (var_expr "var2"); (var_expr "field")] |}
    ]).

Definition program : list rule :=
  [rule_0;
   rule_1;
   rule_2;
   rule_3;
   rule_4].

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