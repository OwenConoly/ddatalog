(* Auto-generated from ../Benchmarks/SouffleExamples/unitprop1.dl by souffle_to_rocq *)
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
(* .type Val <: symbol  {-> string} *)
(* .decl  forced_true(x:symbol{->string}) *)
(* .decl  forced_false(x:symbol{->string}) *)
(* .decl  sat(c:symbol{->string}) *)
(* .decl  contradiction(x:symbol{->string}) *)
(* .decl  clause0(lit_v0:Val{->string}) *)
(* .decl  clause1(lit_nv0:Val{->string}, lit_v1:Val{->string}) *)
(* .decl  clause2(lit_nv0:Val{->string}, lit_v2:Val{->string}) *)
(* .decl  clause3(lit_nv1:Val{->string}, lit_nv2:Val{->string}, lit_v3:Val{->string}) *)
(* .decl  clause4(lit_nv1:Val{->string}, lit_v4:Val{->string}) *)
(* .decl  clause5(lit_nv2:Val{->string}, lit_nv3:Val{->string}, lit_v5:Val{->string}) *)
(* .decl  clause6(lit_nv3:Val{->string}, lit_nv4:Val{->string}, lit_v6:Val{->string}) *)
(* .decl  clause7(lit_nv5:Val{->string}, lit_nv6:Val{->string}, lit_nv7:Val{->string}) *)
(* .decl  clause8(lit_nv5:Val{->string}, lit_v8:Val{->string}) *)
(* .decl  clause9(lit_nv6:Val{->string}, lit_v9:Val{->string}) *)
(* .decl  clause10(lit_nv8:Val{->string}, lit_v10:Val{->string}) *)
(* .decl  clause11(lit_nv9:Val{->string}, lit_v11:Val{->string}) *)
(* .decl  clause12(lit_nv10:Val{->string}, lit_nv11:Val{->string}, lit_nv12:Val{->string}) *)
(* .decl  clause13(lit_nv11:Val{->string}, lit_nv12:Val{->string}, lit_v13:Val{->string}) *)
(* .decl  clause14(lit_nv10:Val{->string}, lit_nv13:Val{->string}, lit_v14:Val{->string}) *)
(* .decl  clause15(lit_v7:Val{->string}, lit_v12:Val{->string}, lit_v14:Val{->string}) *)
(* .decl  clause16(lit_nv4:Val{->string}, lit_nv8:Val{->string}, lit_v13:Val{->string}, lit_v14:Val{->string}) *)
(* .decl  clause17(lit_nv13:Val{->string}, lit_nv14:Val{->string}, lit_v0:Val{->string}, lit_v1:Val{->string}) *)
(* .decl  clause18(lit_v2:Val{->string}, lit_v4:Val{->string}, lit_v6:Val{->string}, lit_v8:Val{->string}) *)
(* .decl  clause19(lit_nv0:Val{->string}, lit_nv1:Val{->string}, lit_nv2:Val{->string}, lit_v3:Val{->string}, lit_v5:Val{->string}) *)
(* .decl  unsat(r:symbol{->string}) *)
(* .output forced_true *)
(* .output forced_false *)
(* .output sat *)
(* .output unsat *)
(* .output contradiction *)

(* clause0("unknown"). *)
Definition rule_0 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause0"; Datalog.clause_args := [(fun_expr "unknown" [])] |}
    ]) ([]).

(* clause0("true") :- forced_true("v0"). *)
Definition rule_1 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause0"; Datalog.clause_args := [(fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]).

(* clause0("false") :- forced_false("v0"). *)
Definition rule_2 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause0"; Datalog.clause_args := [(fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]).

(* forced_true("v0"). *)
Definition rule_3 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]) ([]).

(* sat("C0") :- clause0("true"). *)
Definition rule_4 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C0" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause0"; Datalog.clause_args := [(fun_expr "true" [])] |}
    ]).

(* clause1("unknown", "unknown"). *)
Definition rule_5 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause1"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause1("true", B) :- clause1(_anon0, B), forced_false("v0"). *)
Definition rule_6 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause1"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause1"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]).

(* clause1("false", B) :- clause1(_anon0, B), forced_true("v0"). *)
Definition rule_7 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause1"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause1"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]).

(* clause1(A, "true") :- clause1(A, _anon0), forced_true("v1"). *)
Definition rule_8 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause1"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause1"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]).

(* clause1(A, "false") :- clause1(A, _anon0), forced_false("v1"). *)
Definition rule_9 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause1"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause1"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]).

(* sat("C1") :- clause1("true", _anon0). *)
Definition rule_10 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C1" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause1"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0")] |}
    ]).

(* sat("C1") :- clause1(_anon0, "true"). *)
Definition rule_11 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C1" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause1"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v1") :- clause1("false", "unknown"). *)
Definition rule_12 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause1"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v0") :- clause1("unknown", "false"). *)
Definition rule_13 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause1"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause2("unknown", "unknown"). *)
Definition rule_14 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause2"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause2("true", B) :- clause2(_anon0, B), forced_false("v0"). *)
Definition rule_15 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause2"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause2"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]).

(* clause2("false", B) :- clause2(_anon0, B), forced_true("v0"). *)
Definition rule_16 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause2"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause2"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]).

(* clause2(A, "true") :- clause2(A, _anon0), forced_true("v2"). *)
Definition rule_17 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause2"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause2"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]).

(* clause2(A, "false") :- clause2(A, _anon0), forced_false("v2"). *)
Definition rule_18 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause2"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause2"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]).

(* sat("C2") :- clause2("true", _anon0). *)
Definition rule_19 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C2" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause2"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0")] |}
    ]).

(* sat("C2") :- clause2(_anon0, "true"). *)
Definition rule_20 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C2" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause2"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v2") :- clause2("false", "unknown"). *)
Definition rule_21 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause2"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v0") :- clause2("unknown", "false"). *)
Definition rule_22 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause2"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause3("unknown", "unknown", "unknown"). *)
Definition rule_23 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause3("true", B, C) :- clause3(_anon0, B, C), forced_false("v1"). *)
Definition rule_24 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]).

(* clause3("false", B, C) :- clause3(_anon0, B, C), forced_true("v1"). *)
Definition rule_25 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]).

(* clause3(A, "true", C) :- clause3(A, _anon0, C), forced_false("v2"). *)
Definition rule_26 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]).

(* clause3(A, "false", C) :- clause3(A, _anon0, C), forced_true("v2"). *)
Definition rule_27 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]).

(* clause3(A, B, "true") :- clause3(A, B, _anon0), forced_true("v3"). *)
Definition rule_28 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v3" [])] |}
    ]).

(* clause3(A, B, "false") :- clause3(A, B, _anon0), forced_false("v3"). *)
Definition rule_29 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v3" [])] |}
    ]).

(* sat("C3") :- clause3("true", _anon0, _anon1). *)
Definition rule_30 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C3" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0"); (var_expr "_anon1")] |}
    ]).

(* sat("C3") :- clause3(_anon0, "true", _anon1). *)
Definition rule_31 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C3" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" []); (var_expr "_anon1")] |}
    ]).

(* sat("C3") :- clause3(_anon0, _anon1, "true"). *)
Definition rule_32 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C3" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v3") :- clause3("false", "false", "unknown"). *)
Definition rule_33 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v3" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v1") :- clause3("unknown", "false", "false"). *)
Definition rule_34 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_false("v2") :- clause3("false", "unknown", "false"). *)
Definition rule_35 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause3"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause4("unknown", "unknown"). *)
Definition rule_36 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause4"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause4("true", B) :- clause4(_anon0, B), forced_false("v1"). *)
Definition rule_37 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause4"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause4"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]).

(* clause4("false", B) :- clause4(_anon0, B), forced_true("v1"). *)
Definition rule_38 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause4"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause4"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]).

(* clause4(A, "true") :- clause4(A, _anon0), forced_true("v4"). *)
Definition rule_39 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause4"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause4"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v4" [])] |}
    ]).

(* clause4(A, "false") :- clause4(A, _anon0), forced_false("v4"). *)
Definition rule_40 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause4"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause4"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v4" [])] |}
    ]).

(* sat("C4") :- clause4("true", _anon0). *)
Definition rule_41 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C4" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause4"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0")] |}
    ]).

(* sat("C4") :- clause4(_anon0, "true"). *)
Definition rule_42 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C4" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause4"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v4") :- clause4("false", "unknown"). *)
Definition rule_43 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v4" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause4"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v1") :- clause4("unknown", "false"). *)
Definition rule_44 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause4"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause5("unknown", "unknown", "unknown"). *)
Definition rule_45 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause5("true", B, C) :- clause5(_anon0, B, C), forced_false("v2"). *)
Definition rule_46 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]).

(* clause5("false", B, C) :- clause5(_anon0, B, C), forced_true("v2"). *)
Definition rule_47 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]).

(* clause5(A, "true", C) :- clause5(A, _anon0, C), forced_false("v3"). *)
Definition rule_48 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v3" [])] |}
    ]).

(* clause5(A, "false", C) :- clause5(A, _anon0, C), forced_true("v3"). *)
Definition rule_49 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v3" [])] |}
    ]).

(* clause5(A, B, "true") :- clause5(A, B, _anon0), forced_true("v5"). *)
Definition rule_50 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v5" [])] |}
    ]).

(* clause5(A, B, "false") :- clause5(A, B, _anon0), forced_false("v5"). *)
Definition rule_51 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v5" [])] |}
    ]).

(* sat("C5") :- clause5("true", _anon0, _anon1). *)
Definition rule_52 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C5" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0"); (var_expr "_anon1")] |}
    ]).

(* sat("C5") :- clause5(_anon0, "true", _anon1). *)
Definition rule_53 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C5" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" []); (var_expr "_anon1")] |}
    ]).

(* sat("C5") :- clause5(_anon0, _anon1, "true"). *)
Definition rule_54 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C5" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v5") :- clause5("false", "false", "unknown"). *)
Definition rule_55 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v5" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v2") :- clause5("unknown", "false", "false"). *)
Definition rule_56 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_false("v3") :- clause5("false", "unknown", "false"). *)
Definition rule_57 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v3" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause5"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause6("unknown", "unknown", "unknown"). *)
Definition rule_58 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause6("true", B, C) :- clause6(_anon0, B, C), forced_false("v3"). *)
Definition rule_59 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v3" [])] |}
    ]).

(* clause6("false", B, C) :- clause6(_anon0, B, C), forced_true("v3"). *)
Definition rule_60 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v3" [])] |}
    ]).

(* clause6(A, "true", C) :- clause6(A, _anon0, C), forced_false("v4"). *)
Definition rule_61 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v4" [])] |}
    ]).

(* clause6(A, "false", C) :- clause6(A, _anon0, C), forced_true("v4"). *)
Definition rule_62 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v4" [])] |}
    ]).

(* clause6(A, B, "true") :- clause6(A, B, _anon0), forced_true("v6"). *)
Definition rule_63 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v6" [])] |}
    ]).

(* clause6(A, B, "false") :- clause6(A, B, _anon0), forced_false("v6"). *)
Definition rule_64 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v6" [])] |}
    ]).

(* sat("C6") :- clause6("true", _anon0, _anon1). *)
Definition rule_65 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C6" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0"); (var_expr "_anon1")] |}
    ]).

(* sat("C6") :- clause6(_anon0, "true", _anon1). *)
Definition rule_66 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C6" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" []); (var_expr "_anon1")] |}
    ]).

(* sat("C6") :- clause6(_anon0, _anon1, "true"). *)
Definition rule_67 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C6" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v6") :- clause6("false", "false", "unknown"). *)
Definition rule_68 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v6" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v3") :- clause6("unknown", "false", "false"). *)
Definition rule_69 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v3" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_false("v4") :- clause6("false", "unknown", "false"). *)
Definition rule_70 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v4" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause6"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause7("unknown", "unknown", "unknown"). *)
Definition rule_71 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause7("true", B, C) :- clause7(_anon0, B, C), forced_false("v5"). *)
Definition rule_72 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v5" [])] |}
    ]).

(* clause7("false", B, C) :- clause7(_anon0, B, C), forced_true("v5"). *)
Definition rule_73 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v5" [])] |}
    ]).

(* clause7(A, "true", C) :- clause7(A, _anon0, C), forced_false("v6"). *)
Definition rule_74 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v6" [])] |}
    ]).

(* clause7(A, "false", C) :- clause7(A, _anon0, C), forced_true("v6"). *)
Definition rule_75 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v6" [])] |}
    ]).

(* clause7(A, B, "true") :- clause7(A, B, _anon0), forced_false("v7"). *)
Definition rule_76 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v7" [])] |}
    ]).

(* clause7(A, B, "false") :- clause7(A, B, _anon0), forced_true("v7"). *)
Definition rule_77 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v7" [])] |}
    ]).

(* sat("C7") :- clause7("true", _anon0, _anon1). *)
Definition rule_78 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C7" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0"); (var_expr "_anon1")] |}
    ]).

(* sat("C7") :- clause7(_anon0, "true", _anon1). *)
Definition rule_79 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C7" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" []); (var_expr "_anon1")] |}
    ]).

(* sat("C7") :- clause7(_anon0, _anon1, "true"). *)
Definition rule_80 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C7" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (fun_expr "true" [])] |}
    ]).

(* forced_false("v7") :- clause7("false", "false", "unknown"). *)
Definition rule_81 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v7" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v5") :- clause7("unknown", "false", "false"). *)
Definition rule_82 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v5" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_false("v6") :- clause7("false", "unknown", "false"). *)
Definition rule_83 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v6" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause7"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause8("unknown", "unknown"). *)
Definition rule_84 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause8"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause8("true", B) :- clause8(_anon0, B), forced_false("v5"). *)
Definition rule_85 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause8"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause8"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v5" [])] |}
    ]).

(* clause8("false", B) :- clause8(_anon0, B), forced_true("v5"). *)
Definition rule_86 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause8"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause8"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v5" [])] |}
    ]).

(* clause8(A, "true") :- clause8(A, _anon0), forced_true("v8"). *)
Definition rule_87 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause8"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause8"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v8" [])] |}
    ]).

(* clause8(A, "false") :- clause8(A, _anon0), forced_false("v8"). *)
Definition rule_88 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause8"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause8"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v8" [])] |}
    ]).

(* sat("C8") :- clause8("true", _anon0). *)
Definition rule_89 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C8" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause8"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0")] |}
    ]).

(* sat("C8") :- clause8(_anon0, "true"). *)
Definition rule_90 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C8" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause8"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v8") :- clause8("false", "unknown"). *)
Definition rule_91 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v8" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause8"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v5") :- clause8("unknown", "false"). *)
Definition rule_92 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v5" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause8"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause9("unknown", "unknown"). *)
Definition rule_93 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause9"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause9("true", B) :- clause9(_anon0, B), forced_false("v6"). *)
Definition rule_94 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause9"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause9"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v6" [])] |}
    ]).

(* clause9("false", B) :- clause9(_anon0, B), forced_true("v6"). *)
Definition rule_95 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause9"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause9"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v6" [])] |}
    ]).

(* clause9(A, "true") :- clause9(A, _anon0), forced_true("v9"). *)
Definition rule_96 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause9"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause9"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v9" [])] |}
    ]).

(* clause9(A, "false") :- clause9(A, _anon0), forced_false("v9"). *)
Definition rule_97 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause9"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause9"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v9" [])] |}
    ]).

(* sat("C9") :- clause9("true", _anon0). *)
Definition rule_98 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C9" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause9"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0")] |}
    ]).

(* sat("C9") :- clause9(_anon0, "true"). *)
Definition rule_99 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C9" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause9"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v9") :- clause9("false", "unknown"). *)
Definition rule_100 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v9" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause9"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v6") :- clause9("unknown", "false"). *)
Definition rule_101 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v6" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause9"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause10("unknown", "unknown"). *)
Definition rule_102 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause10"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause10("true", B) :- clause10(_anon0, B), forced_false("v8"). *)
Definition rule_103 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause10"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause10"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v8" [])] |}
    ]).

(* clause10("false", B) :- clause10(_anon0, B), forced_true("v8"). *)
Definition rule_104 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause10"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause10"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v8" [])] |}
    ]).

(* clause10(A, "true") :- clause10(A, _anon0), forced_true("v10"). *)
Definition rule_105 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause10"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause10"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v10" [])] |}
    ]).

(* clause10(A, "false") :- clause10(A, _anon0), forced_false("v10"). *)
Definition rule_106 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause10"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause10"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v10" [])] |}
    ]).

(* sat("C10") :- clause10("true", _anon0). *)
Definition rule_107 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C10" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause10"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0")] |}
    ]).

(* sat("C10") :- clause10(_anon0, "true"). *)
Definition rule_108 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C10" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause10"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v10") :- clause10("false", "unknown"). *)
Definition rule_109 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v10" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause10"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v8") :- clause10("unknown", "false"). *)
Definition rule_110 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v8" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause10"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause11("unknown", "unknown"). *)
Definition rule_111 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause11"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause11("true", B) :- clause11(_anon0, B), forced_false("v9"). *)
Definition rule_112 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause11"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause11"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v9" [])] |}
    ]).

(* clause11("false", B) :- clause11(_anon0, B), forced_true("v9"). *)
Definition rule_113 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause11"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B")] |}
    ]) ([
      {| Datalog.clause_rel := "clause11"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v9" [])] |}
    ]).

(* clause11(A, "true") :- clause11(A, _anon0), forced_true("v11"). *)
Definition rule_114 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause11"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause11"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v11" [])] |}
    ]).

(* clause11(A, "false") :- clause11(A, _anon0), forced_false("v11"). *)
Definition rule_115 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause11"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause11"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v11" [])] |}
    ]).

(* sat("C11") :- clause11("true", _anon0). *)
Definition rule_116 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C11" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause11"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0")] |}
    ]).

(* sat("C11") :- clause11(_anon0, "true"). *)
Definition rule_117 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C11" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause11"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v11") :- clause11("false", "unknown"). *)
Definition rule_118 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v11" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause11"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v9") :- clause11("unknown", "false"). *)
Definition rule_119 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v9" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause11"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause12("unknown", "unknown", "unknown"). *)
Definition rule_120 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause12("true", B, C) :- clause12(_anon0, B, C), forced_false("v10"). *)
Definition rule_121 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v10" [])] |}
    ]).

(* clause12("false", B, C) :- clause12(_anon0, B, C), forced_true("v10"). *)
Definition rule_122 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v10" [])] |}
    ]).

(* clause12(A, "true", C) :- clause12(A, _anon0, C), forced_false("v11"). *)
Definition rule_123 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v11" [])] |}
    ]).

(* clause12(A, "false", C) :- clause12(A, _anon0, C), forced_true("v11"). *)
Definition rule_124 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v11" [])] |}
    ]).

(* clause12(A, B, "true") :- clause12(A, B, _anon0), forced_false("v12"). *)
Definition rule_125 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v12" [])] |}
    ]).

(* clause12(A, B, "false") :- clause12(A, B, _anon0), forced_true("v12"). *)
Definition rule_126 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v12" [])] |}
    ]).

(* sat("C12") :- clause12("true", _anon0, _anon1). *)
Definition rule_127 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C12" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0"); (var_expr "_anon1")] |}
    ]).

(* sat("C12") :- clause12(_anon0, "true", _anon1). *)
Definition rule_128 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C12" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" []); (var_expr "_anon1")] |}
    ]).

(* sat("C12") :- clause12(_anon0, _anon1, "true"). *)
Definition rule_129 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C12" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (fun_expr "true" [])] |}
    ]).

(* forced_false("v12") :- clause12("false", "false", "unknown"). *)
Definition rule_130 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v12" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v10") :- clause12("unknown", "false", "false"). *)
Definition rule_131 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v10" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_false("v11") :- clause12("false", "unknown", "false"). *)
Definition rule_132 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v11" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause12"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause13("unknown", "unknown", "unknown"). *)
Definition rule_133 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause13("true", B, C) :- clause13(_anon0, B, C), forced_false("v11"). *)
Definition rule_134 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v11" [])] |}
    ]).

(* clause13("false", B, C) :- clause13(_anon0, B, C), forced_true("v11"). *)
Definition rule_135 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v11" [])] |}
    ]).

(* clause13(A, "true", C) :- clause13(A, _anon0, C), forced_false("v12"). *)
Definition rule_136 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v12" [])] |}
    ]).

(* clause13(A, "false", C) :- clause13(A, _anon0, C), forced_true("v12"). *)
Definition rule_137 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v12" [])] |}
    ]).

(* clause13(A, B, "true") :- clause13(A, B, _anon0), forced_true("v13"). *)
Definition rule_138 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v13" [])] |}
    ]).

(* clause13(A, B, "false") :- clause13(A, B, _anon0), forced_false("v13"). *)
Definition rule_139 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v13" [])] |}
    ]).

(* sat("C13") :- clause13("true", _anon0, _anon1). *)
Definition rule_140 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C13" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0"); (var_expr "_anon1")] |}
    ]).

(* sat("C13") :- clause13(_anon0, "true", _anon1). *)
Definition rule_141 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C13" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" []); (var_expr "_anon1")] |}
    ]).

(* sat("C13") :- clause13(_anon0, _anon1, "true"). *)
Definition rule_142 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C13" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v13") :- clause13("false", "false", "unknown"). *)
Definition rule_143 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v13" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v11") :- clause13("unknown", "false", "false"). *)
Definition rule_144 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v11" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_false("v12") :- clause13("false", "unknown", "false"). *)
Definition rule_145 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v12" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause13"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause14("unknown", "unknown", "unknown"). *)
Definition rule_146 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause14("true", B, C) :- clause14(_anon0, B, C), forced_false("v10"). *)
Definition rule_147 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v10" [])] |}
    ]).

(* clause14("false", B, C) :- clause14(_anon0, B, C), forced_true("v10"). *)
Definition rule_148 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v10" [])] |}
    ]).

(* clause14(A, "true", C) :- clause14(A, _anon0, C), forced_false("v13"). *)
Definition rule_149 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v13" [])] |}
    ]).

(* clause14(A, "false", C) :- clause14(A, _anon0, C), forced_true("v13"). *)
Definition rule_150 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v13" [])] |}
    ]).

(* clause14(A, B, "true") :- clause14(A, B, _anon0), forced_true("v14"). *)
Definition rule_151 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v14" [])] |}
    ]).

(* clause14(A, B, "false") :- clause14(A, B, _anon0), forced_false("v14"). *)
Definition rule_152 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v14" [])] |}
    ]).

(* sat("C14") :- clause14("true", _anon0, _anon1). *)
Definition rule_153 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C14" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0"); (var_expr "_anon1")] |}
    ]).

(* sat("C14") :- clause14(_anon0, "true", _anon1). *)
Definition rule_154 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C14" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" []); (var_expr "_anon1")] |}
    ]).

(* sat("C14") :- clause14(_anon0, _anon1, "true"). *)
Definition rule_155 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C14" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v14") :- clause14("false", "false", "unknown"). *)
Definition rule_156 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v14" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v10") :- clause14("unknown", "false", "false"). *)
Definition rule_157 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v10" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_false("v13") :- clause14("false", "unknown", "false"). *)
Definition rule_158 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v13" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause14"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* clause15("unknown", "unknown", "unknown"). *)
Definition rule_159 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause15("true", B, C) :- clause15(_anon0, B, C), forced_true("v7"). *)
Definition rule_160 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v7" [])] |}
    ]).

(* clause15("false", B, C) :- clause15(_anon0, B, C), forced_false("v7"). *)
Definition rule_161 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B"); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v7" [])] |}
    ]).

(* clause15(A, "true", C) :- clause15(A, _anon0, C), forced_true("v12"). *)
Definition rule_162 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v12" [])] |}
    ]).

(* clause15(A, "false", C) :- clause15(A, _anon0, C), forced_false("v12"). *)
Definition rule_163 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" []); (var_expr "C")] |}
    ]) ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v12" [])] |}
    ]).

(* clause15(A, B, "true") :- clause15(A, B, _anon0), forced_true("v14"). *)
Definition rule_164 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v14" [])] |}
    ]).

(* clause15(A, B, "false") :- clause15(A, B, _anon0), forced_false("v14"). *)
Definition rule_165 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v14" [])] |}
    ]).

(* sat("C15") :- clause15("true", _anon0, _anon1). *)
Definition rule_166 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C15" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0"); (var_expr "_anon1")] |}
    ]).

(* sat("C15") :- clause15(_anon0, "true", _anon1). *)
Definition rule_167 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C15" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" []); (var_expr "_anon1")] |}
    ]).

(* sat("C15") :- clause15(_anon0, _anon1, "true"). *)
Definition rule_168 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C15" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v7") :- clause15("unknown", "false", "false"). *)
Definition rule_169 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v7" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_true("v12") :- clause15("false", "unknown", "false"). *)
Definition rule_170 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v12" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* forced_true("v14") :- clause15("false", "false", "unknown"). *)
Definition rule_171 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v14" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause15"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* clause16("unknown", "unknown", "unknown", "unknown"). *)
Definition rule_172 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause16("true", B, C, D) :- clause16(_anon0, B, C, D), forced_false("v4"). *)
Definition rule_173 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B"); (var_expr "C"); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v4" [])] |}
    ]).

(* clause16("false", B, C, D) :- clause16(_anon0, B, C, D), forced_true("v4"). *)
Definition rule_174 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B"); (var_expr "C"); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v4" [])] |}
    ]).

(* clause16(A, "true", C, D) :- clause16(A, _anon0, C, D), forced_false("v8"). *)
Definition rule_175 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" []); (var_expr "C"); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v8" [])] |}
    ]).

(* clause16(A, "false", C, D) :- clause16(A, _anon0, C, D), forced_true("v8"). *)
Definition rule_176 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" []); (var_expr "C"); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v8" [])] |}
    ]).

(* clause16(A, B, "true", D) :- clause16(A, B, _anon0, D), forced_true("v13"). *)
Definition rule_177 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "true" []); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v13" [])] |}
    ]).

(* clause16(A, B, "false", D) :- clause16(A, B, _anon0, D), forced_false("v13"). *)
Definition rule_178 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "false" []); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v13" [])] |}
    ]).

(* clause16(A, B, C, "true") :- clause16(A, B, C, _anon0), forced_true("v14"). *)
Definition rule_179 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v14" [])] |}
    ]).

(* clause16(A, B, C, "false") :- clause16(A, B, C, _anon0), forced_false("v14"). *)
Definition rule_180 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v14" [])] |}
    ]).

(* sat("C16") :- clause16("true", _anon0, _anon1, _anon2). *)
Definition rule_181 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C16" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2")] |}
    ]).

(* sat("C16") :- clause16(_anon0, "true", _anon1, _anon2). *)
Definition rule_182 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C16" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" []); (var_expr "_anon1"); (var_expr "_anon2")] |}
    ]).

(* sat("C16") :- clause16(_anon0, _anon1, "true", _anon2). *)
Definition rule_183 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C16" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (fun_expr "true" []); (var_expr "_anon2")] |}
    ]).

(* sat("C16") :- clause16(_anon0, _anon1, _anon2, "true"). *)
Definition rule_184 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C16" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v13") :- clause16("false", "false", "unknown", "false"). *)
Definition rule_185 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v13" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* forced_true("v14") :- clause16("false", "false", "false", "unknown"). *)
Definition rule_186 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v14" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v4") :- clause16("unknown", "false", "false", "false"). *)
Definition rule_187 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v4" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_false("v8") :- clause16("false", "unknown", "false", "false"). *)
Definition rule_188 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v8" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause16"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* clause17("unknown", "unknown", "unknown", "unknown"). *)
Definition rule_189 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause17("true", B, C, D) :- clause17(_anon0, B, C, D), forced_false("v13"). *)
Definition rule_190 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B"); (var_expr "C"); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v13" [])] |}
    ]).

(* clause17("false", B, C, D) :- clause17(_anon0, B, C, D), forced_true("v13"). *)
Definition rule_191 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B"); (var_expr "C"); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v13" [])] |}
    ]).

(* clause17(A, "true", C, D) :- clause17(A, _anon0, C, D), forced_false("v14"). *)
Definition rule_192 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" []); (var_expr "C"); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v14" [])] |}
    ]).

(* clause17(A, "false", C, D) :- clause17(A, _anon0, C, D), forced_true("v14"). *)
Definition rule_193 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" []); (var_expr "C"); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v14" [])] |}
    ]).

(* clause17(A, B, "true", D) :- clause17(A, B, _anon0, D), forced_true("v0"). *)
Definition rule_194 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "true" []); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]).

(* clause17(A, B, "false", D) :- clause17(A, B, _anon0, D), forced_false("v0"). *)
Definition rule_195 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "false" []); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]).

(* clause17(A, B, C, "true") :- clause17(A, B, C, _anon0), forced_true("v1"). *)
Definition rule_196 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]).

(* clause17(A, B, C, "false") :- clause17(A, B, C, _anon0), forced_false("v1"). *)
Definition rule_197 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]).

(* sat("C17") :- clause17("true", _anon0, _anon1, _anon2). *)
Definition rule_198 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C17" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2")] |}
    ]).

(* sat("C17") :- clause17(_anon0, "true", _anon1, _anon2). *)
Definition rule_199 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C17" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" []); (var_expr "_anon1"); (var_expr "_anon2")] |}
    ]).

(* sat("C17") :- clause17(_anon0, _anon1, "true", _anon2). *)
Definition rule_200 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C17" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (fun_expr "true" []); (var_expr "_anon2")] |}
    ]).

(* sat("C17") :- clause17(_anon0, _anon1, _anon2, "true"). *)
Definition rule_201 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C17" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v0") :- clause17("false", "false", "unknown", "false"). *)
Definition rule_202 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* forced_true("v1") :- clause17("false", "false", "false", "unknown"). *)
Definition rule_203 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v13") :- clause17("unknown", "false", "false", "false"). *)
Definition rule_204 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v13" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_false("v14") :- clause17("false", "unknown", "false", "false"). *)
Definition rule_205 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v14" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause17"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* clause18("unknown", "unknown", "unknown", "unknown"). *)
Definition rule_206 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause18("true", B, C, D) :- clause18(_anon0, B, C, D), forced_true("v2"). *)
Definition rule_207 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B"); (var_expr "C"); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]).

(* clause18("false", B, C, D) :- clause18(_anon0, B, C, D), forced_false("v2"). *)
Definition rule_208 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B"); (var_expr "C"); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]).

(* clause18(A, "true", C, D) :- clause18(A, _anon0, C, D), forced_true("v4"). *)
Definition rule_209 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" []); (var_expr "C"); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v4" [])] |}
    ]).

(* clause18(A, "false", C, D) :- clause18(A, _anon0, C, D), forced_false("v4"). *)
Definition rule_210 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" []); (var_expr "C"); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v4" [])] |}
    ]).

(* clause18(A, B, "true", D) :- clause18(A, B, _anon0, D), forced_true("v6"). *)
Definition rule_211 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "true" []); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v6" [])] |}
    ]).

(* clause18(A, B, "false", D) :- clause18(A, B, _anon0, D), forced_false("v6"). *)
Definition rule_212 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "false" []); (var_expr "D")] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0"); (var_expr "D")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v6" [])] |}
    ]).

(* clause18(A, B, C, "true") :- clause18(A, B, C, _anon0), forced_true("v8"). *)
Definition rule_213 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v8" [])] |}
    ]).

(* clause18(A, B, C, "false") :- clause18(A, B, C, _anon0), forced_false("v8"). *)
Definition rule_214 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v8" [])] |}
    ]).

(* sat("C18") :- clause18("true", _anon0, _anon1, _anon2). *)
Definition rule_215 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C18" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2")] |}
    ]).

(* sat("C18") :- clause18(_anon0, "true", _anon1, _anon2). *)
Definition rule_216 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C18" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" []); (var_expr "_anon1"); (var_expr "_anon2")] |}
    ]).

(* sat("C18") :- clause18(_anon0, _anon1, "true", _anon2). *)
Definition rule_217 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C18" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (fun_expr "true" []); (var_expr "_anon2")] |}
    ]).

(* sat("C18") :- clause18(_anon0, _anon1, _anon2, "true"). *)
Definition rule_218 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C18" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v2") :- clause18("unknown", "false", "false", "false"). *)
Definition rule_219 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_true("v4") :- clause18("false", "unknown", "false", "false"). *)
Definition rule_220 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v4" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_true("v6") :- clause18("false", "false", "unknown", "false"). *)
Definition rule_221 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v6" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* forced_true("v8") :- clause18("false", "false", "false", "unknown"). *)
Definition rule_222 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v8" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause18"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* clause19("unknown", "unknown", "unknown", "unknown", "unknown"). *)
Definition rule_223 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" []); (fun_expr "unknown" [])] |}
    ]) ([]).

(* clause19("true", B, C, D, E) :- clause19(_anon0, B, C, D, E), forced_false("v0"). *)
Definition rule_224 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "B"); (var_expr "C"); (var_expr "D"); (var_expr "E")] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C"); (var_expr "D"); (var_expr "E")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]).

(* clause19("false", B, C, D, E) :- clause19(_anon0, B, C, D, E), forced_true("v0"). *)
Definition rule_225 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(fun_expr "false" []); (var_expr "B"); (var_expr "C"); (var_expr "D"); (var_expr "E")] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "B"); (var_expr "C"); (var_expr "D"); (var_expr "E")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]).

(* clause19(A, "true", C, D, E) :- clause19(A, _anon0, C, D, E), forced_false("v1"). *)
Definition rule_226 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (fun_expr "true" []); (var_expr "C"); (var_expr "D"); (var_expr "E")] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C"); (var_expr "D"); (var_expr "E")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]).

(* clause19(A, "false", C, D, E) :- clause19(A, _anon0, C, D, E), forced_true("v1"). *)
Definition rule_227 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (fun_expr "false" []); (var_expr "C"); (var_expr "D"); (var_expr "E")] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "_anon0"); (var_expr "C"); (var_expr "D"); (var_expr "E")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]).

(* clause19(A, B, "true", D, E) :- clause19(A, B, _anon0, D, E), forced_false("v2"). *)
Definition rule_228 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "true" []); (var_expr "D"); (var_expr "E")] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0"); (var_expr "D"); (var_expr "E")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]).

(* clause19(A, B, "false", D, E) :- clause19(A, B, _anon0, D, E), forced_true("v2"). *)
Definition rule_229 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (fun_expr "false" []); (var_expr "D"); (var_expr "E")] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "_anon0"); (var_expr "D"); (var_expr "E")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]).

(* clause19(A, B, C, "true", E) :- clause19(A, B, C, _anon0, E), forced_true("v3"). *)
Definition rule_230 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (fun_expr "true" []); (var_expr "E")] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (var_expr "_anon0"); (var_expr "E")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v3" [])] |}
    ]).

(* clause19(A, B, C, "false", E) :- clause19(A, B, C, _anon0, E), forced_false("v3"). *)
Definition rule_231 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (fun_expr "false" []); (var_expr "E")] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (var_expr "_anon0"); (var_expr "E")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v3" [])] |}
    ]).

(* clause19(A, B, C, D, "true") :- clause19(A, B, C, D, _anon0), forced_true("v5"). *)
Definition rule_232 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (var_expr "D"); (fun_expr "true" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (var_expr "D"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v5" [])] |}
    ]).

(* clause19(A, B, C, D, "false") :- clause19(A, B, C, D, _anon0), forced_false("v5"). *)
Definition rule_233 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (var_expr "D"); (fun_expr "false" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "A"); (var_expr "B"); (var_expr "C"); (var_expr "D"); (var_expr "_anon0")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v5" [])] |}
    ]).

(* sat("C19") :- clause19("true", _anon0, _anon1, _anon2, _anon3). *)
Definition rule_234 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C19" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(fun_expr "true" []); (var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2"); (var_expr "_anon3")] |}
    ]).

(* sat("C19") :- clause19(_anon0, "true", _anon1, _anon2, _anon3). *)
Definition rule_235 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C19" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "_anon0"); (fun_expr "true" []); (var_expr "_anon1"); (var_expr "_anon2"); (var_expr "_anon3")] |}
    ]).

(* sat("C19") :- clause19(_anon0, _anon1, "true", _anon2, _anon3). *)
Definition rule_236 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C19" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (fun_expr "true" []); (var_expr "_anon2"); (var_expr "_anon3")] |}
    ]).

(* sat("C19") :- clause19(_anon0, _anon1, _anon2, "true", _anon3). *)
Definition rule_237 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C19" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2"); (fun_expr "true" []); (var_expr "_anon3")] |}
    ]).

(* sat("C19") :- clause19(_anon0, _anon1, _anon2, _anon3, "true"). *)
Definition rule_238 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "sat"; Datalog.clause_args := [(fun_expr "C19" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(var_expr "_anon0"); (var_expr "_anon1"); (var_expr "_anon2"); (var_expr "_anon3"); (fun_expr "true" [])] |}
    ]).

(* forced_true("v3") :- clause19("false", "false", "false", "unknown", "false"). *)
Definition rule_239 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v3" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" [])] |}
    ]).

(* forced_true("v5") :- clause19("false", "false", "false", "false", "unknown"). *)
Definition rule_240 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(fun_expr "v5" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" [])] |}
    ]).

(* forced_false("v0") :- clause19("unknown", "false", "false", "false", "false"). *)
Definition rule_241 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v0" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_false("v1") :- clause19("false", "unknown", "false", "false", "false"). *)
Definition rule_242 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v1" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* forced_false("v2") :- clause19("false", "false", "unknown", "false", "false"). *)
Definition rule_243 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(fun_expr "v2" [])] |}
    ]) ([
      {| Datalog.clause_rel := "clause19"; Datalog.clause_args := [(fun_expr "false" []); (fun_expr "false" []); (fun_expr "unknown" []); (fun_expr "false" []); (fun_expr "false" [])] |}
    ]).

(* contradiction(X) :- forced_true(X), forced_false(X). *)
Definition rule_244 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "contradiction"; Datalog.clause_args := [(var_expr "X")] |}
    ]) ([
      {| Datalog.clause_rel := "forced_true"; Datalog.clause_args := [(var_expr "X")] |};
      {| Datalog.clause_rel := "forced_false"; Datalog.clause_args := [(var_expr "X")] |}
    ]).

(* unsat("UNSAT") :- contradiction(_anon0). *)
Definition rule_245 : rule :=
Datalog.normal_rule ([
      {| Datalog.clause_rel := "unsat"; Datalog.clause_args := [(fun_expr "UNSAT" [])] |}
    ]) ([
      {| Datalog.clause_rel := "contradiction"; Datalog.clause_args := [(var_expr "_anon0")] |}
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
   rule_14;
   rule_15;
   rule_16;
   rule_17;
   rule_18;
   rule_19;
   rule_20;
   rule_21;
   rule_22;
   rule_23;
   rule_24;
   rule_25;
   rule_26;
   rule_27;
   rule_28;
   rule_29;
   rule_30;
   rule_31;
   rule_32;
   rule_33;
   rule_34;
   rule_35;
   rule_36;
   rule_37;
   rule_38;
   rule_39;
   rule_40;
   rule_41;
   rule_42;
   rule_43;
   rule_44;
   rule_45;
   rule_46;
   rule_47;
   rule_48;
   rule_49;
   rule_50;
   rule_51;
   rule_52;
   rule_53;
   rule_54;
   rule_55;
   rule_56;
   rule_57;
   rule_58;
   rule_59;
   rule_60;
   rule_61;
   rule_62;
   rule_63;
   rule_64;
   rule_65;
   rule_66;
   rule_67;
   rule_68;
   rule_69;
   rule_70;
   rule_71;
   rule_72;
   rule_73;
   rule_74;
   rule_75;
   rule_76;
   rule_77;
   rule_78;
   rule_79;
   rule_80;
   rule_81;
   rule_82;
   rule_83;
   rule_84;
   rule_85;
   rule_86;
   rule_87;
   rule_88;
   rule_89;
   rule_90;
   rule_91;
   rule_92;
   rule_93;
   rule_94;
   rule_95;
   rule_96;
   rule_97;
   rule_98;
   rule_99;
   rule_100;
   rule_101;
   rule_102;
   rule_103;
   rule_104;
   rule_105;
   rule_106;
   rule_107;
   rule_108;
   rule_109;
   rule_110;
   rule_111;
   rule_112;
   rule_113;
   rule_114;
   rule_115;
   rule_116;
   rule_117;
   rule_118;
   rule_119;
   rule_120;
   rule_121;
   rule_122;
   rule_123;
   rule_124;
   rule_125;
   rule_126;
   rule_127;
   rule_128;
   rule_129;
   rule_130;
   rule_131;
   rule_132;
   rule_133;
   rule_134;
   rule_135;
   rule_136;
   rule_137;
   rule_138;
   rule_139;
   rule_140;
   rule_141;
   rule_142;
   rule_143;
   rule_144;
   rule_145;
   rule_146;
   rule_147;
   rule_148;
   rule_149;
   rule_150;
   rule_151;
   rule_152;
   rule_153;
   rule_154;
   rule_155;
   rule_156;
   rule_157;
   rule_158;
   rule_159;
   rule_160;
   rule_161;
   rule_162;
   rule_163;
   rule_164;
   rule_165;
   rule_166;
   rule_167;
   rule_168;
   rule_169;
   rule_170;
   rule_171;
   rule_172;
   rule_173;
   rule_174;
   rule_175;
   rule_176;
   rule_177;
   rule_178;
   rule_179;
   rule_180;
   rule_181;
   rule_182;
   rule_183;
   rule_184;
   rule_185;
   rule_186;
   rule_187;
   rule_188;
   rule_189;
   rule_190;
   rule_191;
   rule_192;
   rule_193;
   rule_194;
   rule_195;
   rule_196;
   rule_197;
   rule_198;
   rule_199;
   rule_200;
   rule_201;
   rule_202;
   rule_203;
   rule_204;
   rule_205;
   rule_206;
   rule_207;
   rule_208;
   rule_209;
   rule_210;
   rule_211;
   rule_212;
   rule_213;
   rule_214;
   rule_215;
   rule_216;
   rule_217;
   rule_218;
   rule_219;
   rule_220;
   rule_221;
   rule_222;
   rule_223;
   rule_224;
   rule_225;
   rule_226;
   rule_227;
   rule_228;
   rule_229;
   rule_230;
   rule_231;
   rule_232;
   rule_233;
   rule_234;
   rule_235;
   rule_236;
   rule_237;
   rule_238;
   rule_239;
   rule_240;
   rule_241;
   rule_242;
   rule_243;
   rule_244;
   rule_245].

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