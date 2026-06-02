(* Auto-generated from SouffleExamples/po5.dl by souffle_to_rocq *)
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
(* .decl  Check(n1:number{->Z}, n2:number{->Z}, n3:number{->Z}, n4:number{->Z}, n5:number{->Z}, n6:number{->Z}) *)
(* .decl  In(n1:number{->Z}, n2:number{->Z}, n3:number{->Z}, n4:number{->Z}, n5:number{->Z}, n6:number{->Z}, in:number{->Z}) *)
(* .decl  A(l:number{->Z}, o:number{->Z}) *)

(* A("1", i) :- Check(a, b, c, d, e, f), In(a, b, c, d, e, f, i). *)
Definition rule_0 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "1" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "c"); (var_expr "d"); (var_expr "e"); (var_expr "f")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "c"); (var_expr "d"); (var_expr "e"); (var_expr "f"); (var_expr "i")] |}
    ]).

(* A("2", i) :- Check(a, _anon0, _anon1, d, e, f), In(a, _anon2, _anon3, d, e, f, i). *)
Definition rule_1 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "2" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "_anon0"); (var_expr "_anon1"); (var_expr "d"); (var_expr "e"); (var_expr "f")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "_anon2"); (var_expr "_anon3"); (var_expr "d"); (var_expr "e"); (var_expr "f"); (var_expr "i")] |}
    ]).

(* A("3", i) :- Check(a, b, _anon0, d, e, f), In(a, b, _anon1, d, e, f, i). *)
Definition rule_2 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "3" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "_anon0"); (var_expr "d"); (var_expr "e"); (var_expr "f")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "_anon1"); (var_expr "d"); (var_expr "e"); (var_expr "f"); (var_expr "i")] |}
    ]).

(* A("4", i) :- Check(a, _anon0, _anon1, _anon2, e, f), In(a, _anon3, _anon4, _anon5, e, f, i). *)
Definition rule_3 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "4" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2"); (var_expr "e"); (var_expr "f")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "_anon3"); (var_expr "_anon4"); (var_expr "_anon5"); (var_expr "e"); (var_expr "f"); (var_expr "i")] |}
    ]).

(* A("5", i) :- Check(a, b, _anon0, _anon1, _anon2, f), In(a, b, _anon3, _anon4, _anon5, f, i). *)
Definition rule_4 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "5" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2"); (var_expr "f")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "_anon3"); (var_expr "_anon4"); (var_expr "_anon5"); (var_expr "f"); (var_expr "i")] |}
    ]).

(* A("6", i) :- Check(a, _anon0, _anon1, _anon2, _anon3, _anon4), In(a, _anon5, _anon6, _anon7, _anon8, _anon9, i). *)
Definition rule_5 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "6" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2"); (var_expr "_anon3"); (var_expr "_anon4")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "_anon5"); (var_expr "_anon6"); (var_expr "_anon7"); (var_expr "_anon8"); (var_expr "_anon9"); (var_expr "i")] |}
    ]).

(* A("7", i) :- Check(a, b, _anon0, d, e, f), In(a, b, _anon1, d, e, f, i). *)
Definition rule_6 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "7" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "_anon0"); (var_expr "d"); (var_expr "e"); (var_expr "f")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "_anon1"); (var_expr "d"); (var_expr "e"); (var_expr "f"); (var_expr "i")] |}
    ]).

(* A("8", i) :- Check(a, b, _anon0, _anon1, e, f), In(a, b, _anon2, _anon3, e, f, i). *)
Definition rule_7 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "8" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "_anon0"); (var_expr "_anon1"); (var_expr "e"); (var_expr "f")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "_anon2"); (var_expr "_anon3"); (var_expr "e"); (var_expr "f"); (var_expr "i")] |}
    ]).

(* A("9", i) :- Check(a, b, _anon0, _anon1, _anon2, f), In(a, b, _anon3, _anon4, _anon5, f, i). *)
Definition rule_8 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "9" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2"); (var_expr "f")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "_anon3"); (var_expr "_anon4"); (var_expr "_anon5"); (var_expr "f"); (var_expr "i")] |}
    ]).

(* A("10", i) :- Check(a, b, _anon0, _anon1, _anon2, _anon3), In(a, b, _anon4, _anon5, _anon6, _anon7, i). *)
Definition rule_9 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "10" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2"); (var_expr "_anon3")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "_anon4"); (var_expr "_anon5"); (var_expr "_anon6"); (var_expr "_anon7"); (var_expr "i")] |}
    ]).

(* A("11", i) :- Check(a, b, c, _anon0, e, f), In(a, b, c, _anon1, e, f, i). *)
Definition rule_10 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "11" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "c"); (var_expr "_anon0"); (var_expr "e"); (var_expr "f")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "c"); (var_expr "_anon1"); (var_expr "e"); (var_expr "f"); (var_expr "i")] |}
    ]).

(* A("12", i) :- Check(a, _anon0, c, _anon1, _anon2, f), In(a, _anon3, c, _anon4, _anon5, f, i). *)
Definition rule_11 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "12" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "_anon0"); (var_expr "c"); (var_expr "_anon1"); (var_expr "_anon2"); (var_expr "f")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "_anon3"); (var_expr "c"); (var_expr "_anon4"); (var_expr "_anon5"); (var_expr "f"); (var_expr "i")] |}
    ]).

(* A("13", i) :- Check(a, b, c, _anon0, _anon1, _anon2), In(a, b, c, _anon3, _anon4, _anon5, i). *)
Definition rule_12 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "13" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "c"); (var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "c"); (var_expr "_anon3"); (var_expr "_anon4"); (var_expr "_anon5"); (var_expr "i")] |}
    ]).

(* A("14", i) :- Check(a, b, c, d, _anon0, f), In(a, b, c, d, _anon1, f, i). *)
Definition rule_13 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "14" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "c"); (var_expr "d"); (var_expr "_anon0"); (var_expr "f")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "b"); (var_expr "c"); (var_expr "d"); (var_expr "_anon1"); (var_expr "f"); (var_expr "i")] |}
    ]).

(* A("15", i) :- Check(a, _anon0, c, d, _anon1, _anon2), In(a, _anon3, c, d, _anon4, _anon5, i). *)
Definition rule_14 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "A"; Datalog.clause_args := [(fun_expr "15" []); (var_expr "i")] |}
    ]) ([
      {| Datalog.clause_rel := "Check"; Datalog.clause_args := [(var_expr "a"); (var_expr "_anon0"); (var_expr "c"); (var_expr "d"); (var_expr "_anon1"); (var_expr "_anon2")] |};
      {| Datalog.clause_rel := "In"; Datalog.clause_args := [(var_expr "a"); (var_expr "_anon3"); (var_expr "c"); (var_expr "d"); (var_expr "_anon4"); (var_expr "_anon5"); (var_expr "i")] |}
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
   rule_9;
   rule_10;
   rule_11;
   rule_12;
   rule_13;
   rule_14].

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