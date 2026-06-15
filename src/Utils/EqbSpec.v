(* Project-side [Eqb]/[Eqb_ok] instances that the datalog submodule and coqutil do not
   already provide: [unit] (coqutil covers bool/nat/string/int), and the rule-AST types
   [clause]/[meta_clause]/[rule] (the submodule provides [expr]'s instance in [Interpreter]). *)

From Stdlib Require Import List Bool.
From coqutil Require Import Datatypes.List Datatypes.Option Tactics Tactics.fwd Eqb.
From Datalog Require Import Datalog Interpreter List Eqb.
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
    fun c1 c2 =>
      eqb (clause_rel c1) (clause_rel c2) &&
      eqb (clause_args c1) (clause_args c2).

  #[global] Instance clause_eqb_ok : Eqb_ok clause_eqb.
  Proof.
    intros [R1 args1] [R2 args2]. cbv [eqb clause_eqb].
    cbn [clause_rel clause_args].
    pose proof (eqb_spec R1 R2) as HR. cbv [eqb] in HR.
    destruct (rel_eqb R1 R2); cbn [andb]; [subst|congruence].
    pose proof (eqb_spec args1 args2) as Hl. cbv [eqb] in Hl.
    destruct (list_eqb args1 args2); [subst|]; congruence.
  Qed.

  (* equality on meta-clauses (used only to give [rule_eqb] a total definition over all
     three rule constructors; the bare fragment only ever uses [normal_rule]) *)
  #[global] Instance meta_clause_eqb : Eqb meta_clause :=
    fun m1 m2 =>
      eqb (meta_clause_rel m1) (meta_clause_rel m2) &&
      eqb (meta_clause_args m1) (meta_clause_args m2).

  #[global] Instance meta_clause_eqb_ok : Eqb_ok meta_clause_eqb.
  Proof.
    intros [R1 args1] [R2 args2]. cbv [eqb meta_clause_eqb].
    cbn [meta_clause_rel meta_clause_args].
    pose proof (eqb_spec R1 R2) as HR. cbv [eqb] in HR.
    destruct (rel_eqb R1 R2); cbn [andb]; [subst|congruence].
    pose proof (eqb_spec args1 args2) as Hl. cbv [eqb] in Hl.
    destruct (list_eqb args1 args2); [subst|]; congruence.
  Qed.

  #[global] Instance rule_eqb : Eqb rule :=
    fun r1 r2 =>
      match r1, r2 with
      | normal_rule c1 h1, normal_rule c2 h2 =>
          eqb c1 c2 && eqb h1 h2
      | meta_rule c1 h1, meta_rule c2 h2 =>
          eqb c1 c2 && eqb h1 h2
      | agg_rule cr1 a1 hr1, agg_rule cr2 a2 hr2 =>
          eqb cr1 cr2 && eqb a1 a2 && eqb hr1 hr2
      | _, _ => false
      end.

  #[global] Instance rule_eqb_ok : Eqb_ok rule_eqb.
  Proof.
    intros [c1 h1 | c1 h1 | cr1 a1 hr1] [c2 h2 | c2 h2 | cr2 a2 hr2];
      cbv [eqb rule_eqb]; try congruence.
    - pose proof (eqb_spec c1 c2) as Hc. cbv [eqb] in Hc.
      destruct (list_eqb c1 c2); cbn [andb]; [subst|congruence].
      pose proof (eqb_spec h1 h2) as Hh. cbv [eqb] in Hh.
      destruct (list_eqb h1 h2); [subst|]; congruence.
    - pose proof (eqb_spec c1 c2) as Hc. cbv [eqb] in Hc.
      destruct (list_eqb c1 c2); cbn [andb]; [subst|congruence].
      pose proof (eqb_spec h1 h2) as Hh. cbv [eqb] in Hh.
      destruct (list_eqb h1 h2); [subst|]; congruence.
    - pose proof (eqb_spec cr1 cr2) as Hcr. cbv [eqb] in Hcr.
      destruct (rel_eqb cr1 cr2); cbn [andb]; [subst|congruence].
      pose proof (eqb_spec a1 a2) as Ha. cbv [eqb] in Ha.
      destruct (aggregator_eqb a1 a2); cbn [andb]; [subst|congruence].
      pose proof (eqb_spec hr1 hr2) as Hhr. cbv [eqb] in Hhr.
      destruct (rel_eqb hr1 hr2); [subst|]; congruence.
  Qed.
End DatalogEqb.
