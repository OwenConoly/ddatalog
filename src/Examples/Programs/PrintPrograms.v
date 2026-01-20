From JSON Require Import Encode Printer.
From Datalog Require Import JSON FancyNotations CompilerExamples ATLToDatalog.
From DatalogRocq Require Import BasicProgram Family Graph Matmul NetkatWithoutStar.
Print Printer.

Redirect "json_examples/basic_program" Eval compute in (to_string (encode basic_program)).
Redirect "json_examples/family_program" Eval compute in (to_string (encode family_program)).
Redirect "json_examples/graph_program" Eval compute in (to_string (encode graph_program)).
Redirect "json_examples/netkat_program" Eval compute in (to_string (encode netkat_program)).

Instance JEncode_Bfn : JEncode Bfn :=
  fun f =>
    match f with
    | fn_BAnd => JSON__String "/\b"
    | fn_BLt => JSON__String "<b"
    | fn_BEq => JSON__String "=b"
    | fn_BLe => JSON__String "<=b"
    | fn_BLit b =>  match b with
                  | true => JSON__True
                  | false => JSON__False
                  end
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
    | str_rel s => JSON__String s
    | nat_rel n => JSON__Number (Z.of_nat n)
    | true_rel => JSON__True
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