From Datalog Require Export Datalog List.
From Stdlib Require Import String List.
From coqutil Require Export Eqb.   (* re-export so [string]'s [Eqb] reaches importers *)
From DatalogRocq Require Import EqbSpec.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.

(* The string instantiation of the datalog signature: relations, variables and function symbols
   are strings, aggregation is unused ([unit]), values are strings.  Registering each type as a
   typeclass instance lets every downstream [rule]/[clause]/... and every [eqb] be
   inferred -- no per-type aliases or equality definitions are needed ([string] has [Eqb] in
   coqutil, [unit] in [EqbSpec]). *)
#[export] Instance string_rel : relT := string.
#[export] Instance string_var : exprvarT := string.
#[export] Instance string_fn : fnT := string.
#[export] Instance string_aggregator : aggregatorT := unit.
#[export] Instance string_valueT : valueT := string.

(* Structural compatibility of two expressions for unification (NOT decidable equality):
   a variable matches anything; two applications match iff same head and compatible args. *)
Fixpoint expr_compatible (e1 e2 : expr) : bool :=
  match e1, e2 with
  | var_expr _, _ => true
  | _, var_expr _ => true
  | fun_expr f1 args1, fun_expr f2 args2 =>
      eqb f1 f2 && list_eqb (aeqb := expr_compatible) args1 args2
  end.
