(* Project-side [Eqb]/[Eqb_ok] instances that the datalog submodule and coqutil do not
   already provide: [unit] (coqutil covers bool/nat/string/int), and the rule-AST types
   [clause]/[rule] (the submodule provides [expr]'s instance in [Datalog]). *)

From Stdlib Require Import List Bool.
From coqutil Require Import Datatypes.List Datatypes.Option Tactics Tactics.fwd Eqb.
From Datalog Require Import Datalog.
From Datalog.Util Require Import List Eqb.
Import ListNotations.

#[global] Instance unit_eqb : Eqb unit := fun _ _ => true.
#[global] Instance unit_eqb_ok : Eqb_ok unit_eqb.
Proof. intros [] []. cbv [eqb unit_eqb]. reflexivity. Qed.

Section DatalogEqb.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT}.
  Context {var_eqb : Eqb exprvar} {var_eqb_ok : Eqb_ok var_eqb}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context {fn_eqb : Eqb fn} {fn_eqb_ok : Eqb_ok fn_eqb}.
  Context {aggregator_eqb : Eqb aggregator} {aggregator_eqb_ok : Eqb_ok aggregator_eqb}.

  #[global] Instance clause_eqb : Eqb clause :=
    fun c1 c2 => eqb c1.(clause.rel) c2.(clause.rel) && eqb c1.(clause.args) c2.(clause.args).

  #[global] Instance clause_eqb_ok : Eqb_ok clause_eqb.
  Proof.
    intros [R1 args1] [R2 args2]. cbv [eqb clause_eqb]. simpl.
    destr (rel_eqb R1 R2); [|congruence]. destr (list_eqb args1 args2); congruence.
  Qed.

  #[global] Instance rule_eqb : Eqb rule :=
    fun r1 r2 =>
      match r1, r2 with
      | rule.impl c1 h1, rule.impl c2 h2 =>
          eqb c1 c2 && eqb h1 h2
      | rule.agg cr1 a1 hr1, rule.agg cr2 a2 hr2 =>
          eqb cr1 cr2 && eqb a1 a2 && eqb hr1 hr2
      | _, _ => false
      end.

  #[global] Instance rule_eqb_ok : Eqb_ok rule_eqb.
  Proof.
    intros [c1 h1 | cr1 a1 hr1] [c2 h2 | cr2 a2 hr2]; cbv [eqb rule_eqb]; try congruence.
    - destr (list_eqb c1 c2); [|congruence]. destr (list_eqb h1 h2); congruence.
    - destr (rel_eqb cr1 cr2); [|congruence]. destr (aggregator_eqb a1 a2); [|congruence].
      destr (rel_eqb hr1 hr2); congruence.
  Qed.
End DatalogEqb.
