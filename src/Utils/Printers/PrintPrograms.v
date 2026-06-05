From JSON Require Import Encode Printer.
From Datalog Require Import Datalog (* JSON FancyNotations CompilerExamples ATLToDatalog : broken *).
From Stdlib Require Import List String.
Import ListNotations.
From DatalogRocq Require Import BasicProgram Family Examples.Programs.Graph (* Matmul : ATL *) NetkatWithoutStar Csda Cspa Po1 Po2 Po3 Po4 Po5 Pointsto Ranpo Reach Tc Trans Triangle X9 Unitprop1.

(* Local JSON encoders for the *source* datalog AST, decoupled from the broken [Datalog.JSON]
   submodule file.  (Mirrors how [PrintHardwareEncoding] defines encoders for the hardware AST.) *)
Section SourceEncoders.
Context {rel var fn aggregator : Type}.
Context `{JEncode rel} `{JEncode var} `{JEncode fn} `{JEncode aggregator}.

Fixpoint encode_dexpr (e : Datalog.expr var fn) : json :=
  match e with
  | var_expr v => JSON__Object [("var_expr", encode v)]
  | fun_expr f args =>
      JSON__Object [("fun_expr", encode f);
                    ("args", JSON__Array (List.map encode_dexpr args))]
  end.
#[global] Instance JEncode__dexpr : JEncode (Datalog.expr var fn) := encode_dexpr.

#[global] Instance JEncode__dclause : JEncode (Datalog.clause rel var fn) := fun c =>
  JSON__Object [("clause_rel", encode c.(clause_rel));
                ("clause_args", encode c.(clause_args))].

#[global] Instance JEncode__dmeta_clause : JEncode (Datalog.meta_clause rel var fn) := fun c =>
  JSON__Object [("meta_clause_rel", encode c.(meta_clause_rel));
                ("meta_clause_args", encode c.(meta_clause_args))].

#[global] Instance JEncode__drule : JEncode (Datalog.rule rel var fn aggregator) := fun r =>
  match r with
  | normal_rule concls hyps =>
      JSON__Object [("normal_rule",
        JSON__Object [("concls", encode concls); ("hyps", encode hyps)])]
  | meta_rule concls hyps =>
      JSON__Object [("meta_rule",
        JSON__Object [("concls", encode concls); ("hyps", encode hyps)])]
  | agg_rule cr agg hr =>
      JSON__Object [("agg_rule",
        JSON__Object [("concl_rel", encode cr); ("agg", encode agg); ("hyp_rel", encode hr)])]
  end.
End SourceEncoders.

Redirect "json_examples/basic_program" Eval compute in (to_string (encode basic_program)).
Redirect "json_examples/family_program" Eval compute in (to_string (encode family_program)).
Redirect "json_examples/csda" Eval compute in (to_string (encode Csda.computed_program)).
(* Redirect "json_examples/graph_program" Eval compute in (to_string (encode graph_program)). *)
Redirect "json_examples/cspa" Eval compute in (to_string (encode Cspa.computed_program)).
Redirect "json_examples/po1" Eval compute in (to_string (encode Po1.computed_program)).
Redirect "json_examples/po2" Eval compute in (to_string (encode Po2.computed_program)).
Redirect "json_examples/po3" Eval compute in (to_string (encode Po3.computed_program)).
Redirect "json_examples/po4" Eval compute in (to_string (encode Po4.computed_program)).
Redirect "json_examples/po5" Eval compute in (to_string (encode Po5.computed_program)).
Redirect "json_examples/pointsto" Eval compute in (to_string (encode Pointsto.computed_program)).
Redirect "json_examples/ranpo" Eval compute in (to_string (encode Ranpo.computed_program)).
Redirect "json_examples/reach" Eval compute in (to_string (encode Reach.computed_program)).
Redirect "json_examples/tc" Eval compute in (to_string (encode Tc.computed_program)).
Redirect "json_examples/trans" Eval compute in (to_string (encode Trans.computed_program)).
Redirect "json_examples/triangle" Eval compute in (to_string (encode Triangle.computed_program)).
Redirect "json_examples/x9" Eval compute in (to_string (encode X9.computed_program)).
Redirect "json_examples/netkat_program" Eval compute in (to_string (encode netkat_program)).
Redirect "json_examples/unitprop1_program" Eval compute in (to_string (encode Unitprop1.computed_program)).

(* ---- ATL-only encoders + matmul example: ATLToDatalog is broken, so commented out ----
Instance JEncode_Bfn : JEncode Bfn :=
  fun f =>
    match f with
    | fn_BAnd => JSON__String "/\b"
    | fn_BLt => JSON__String "<b"
    | fn_BEq => JSON__String "=b"
    | fn_BLe => JSON__String "<=b"
    | fn_BLit b =>  JSON__String (if b then "trueb" else "falseb")
    | fn_BNot => JSON__String "~b"
    end.

Instance JEncode_Zfn : JEncode Zfn :=
  fun f =>
    match f with
    | fn_ZPlus => JSON__String "+z"
    | fn_ZMinus => JSON__String "-z"
    | fn_ZTimes => JSON__String "*z"
    | fn_ZDivf => JSON__String "/zf"
    | fn_ZDivc => JSON__String "/zc"
    | fn_ZMod => JSON__String "modz"
    | fn_Zmax => JSON__String "maxz"
    | fn_ZLit z => JSON__Number z
    | fn_ZRange => JSON__String "rangez"
    end.


(* TODO eventually we need to work out all the reals in here so that 
   it doesn't cause any problems *)

Instance JEncode_Rfn : JEncode Rfn :=
  fun f =>
    match f with
    | fn_SMul => JSON__String "*r"
    | fn_SAdd => JSON__String "+r"
    | fn_SDiv => JSON__String "/r"
    | fn_SSub => JSON__String "-r"
    | fn_SLit r => JSON__String "real_not_supported"
    end.

Instance JEncode_ATL_Rel : JEncode ATLToDatalog.rel :=
  fun r =>
    match r with
    | str_rel s =>
        JSON__Array [JSON__String "str_rel"; JSON__String s]
    | nat_rel n =>
        JSON__Array [JSON__String "nat_rel"; JSON__Number (Z.of_nat n)]
    | true_rel =>
        JSON__Array [JSON__String "true_rel"; JSON__True]
    end.

Instance JEncode_ATL_Fn : JEncode ATLToDatalog.fn :=
  fun f =>
    match f with
    | fn_B b => encode b
    | fn_Z z => encode z
    | fn_R r => encode r
    end.

Instance JEncode_ATL_aggregator : JEncode ATLToDatalog.aggregator :=
  fun agg =>
    match agg with
    | sum => JSON__String "sum"
    end.

Definition x := (to_string (encode datalog_matmul)).

Redirect "json_examples/matmul_program" Eval compute in (to_string (encode datalog_matmul)).
---- end ATL-only block ---- *)