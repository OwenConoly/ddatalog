From JSON Require Import Encode Printer.
From Datalog Require Import Datalog (* JSON FancyNotations CompilerExamples ATLToDatalog : broken *).
From Stdlib Require Import List String.
Import ListNotations.
From DatalogRocq Require Import Examples.Programs.BasicProgram Examples.Programs.Family (* Graph: deprecated old non-Souffle version removed; use Examples.Programs.Graph *) (* Matmul : ATL *) Examples.Programs.NetkatWithoutStar Examples.Programs.Csda Examples.Programs.Cspa Examples.Programs.Po1 Examples.Programs.Po2 Examples.Programs.Po3 Examples.Programs.Po4 Examples.Programs.Po5 Examples.Programs.Pointsto Examples.Programs.Ranpo Examples.Programs.Reach Examples.Programs.Tc Examples.Programs.Trans Examples.Programs.Triangle Examples.Programs.X9 Examples.Programs.Unitprop1.

(* The source-AST JSON encoders now live in EncodeProgram.v so they can be reused (e.g. by the
   pipeline's emit driver) without importing the example programs. *)
From DatalogRocq Require Import EncodeProgram.

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