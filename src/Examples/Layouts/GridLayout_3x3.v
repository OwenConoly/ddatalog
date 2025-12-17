From Stdlib Require Import List Bool ZArith.Znat Lia.
From DatalogRocq Require Import Dataflow GridGraph DependencyGenerator ATLDatalogParams Matmul GridLayout.
From Datalog Require Import Datalog CompilerExamples ATLToDatalog.
From coqutil Require Import Map.Interface Map.Properties Map.Solver.
Import ListNotations.

Section SmallExample.
  Definition rel := ATLDatalogParams.rel.
  Definition var := ATLDatalogParams.var.
  Definition fn := ATLDatalogParams.fn.
  Definition aggregator := ATLDatalogParams.aggregator.
  Definition T := ATLDatalogParams.T.
  Definition rule := Datalog.rule rel var fn aggregator.

  Context {context : map.map var T}.
  Context {context_ok : map.ok context}.
  Context {sig : signature fn aggregator T}.
  Context {query_sig : query_signature rel}.

  Definition dims : list nat := [3; 3].

  Definition program : list rule := datalog_matmul. 

  Print datalog_matmul.

  Definition indexed_layout : list (Node * list nat) := 
    [([2;0], [0]); 
    ([0;2], [1]); 
    ([0;0], [2]); 
    ([2;2], [3]); 
    ([1;2], [4]); 
    ([1;1], [5]); 
    ([1;0], [6]); 
    ([2;1], [7]); 
    ([0;1], [8])].

  Definition datalog_matmul_3x3 := @mk_dataflow_network rel var fn aggregator T dims indexed_layout program.
  Definition rule_eqb := @DependencyGenerator.rule_eqb rel var fn aggregator var_eqb rel_eqb fn_eqb.
  Definition rule_eqb_spec := @DependencyGenerator.rule_eqb_spec rel var fn aggregator T sig query_sig context context_ok var_eqb var_eqb_spec rel_eqb rel_eqb_spec fn_eqb fn_eqb_spec aggregator_eqb aggregator_eqb_spec expr_compatible.

  Definition check_layout := @GridLayout.check_layout rel var fn aggregator rule_eqb.
  Definition mk_layout := @GridLayout.mk_layout_from_indexed_layout rel var fn aggregator.

  (* Should be True! Our layout passes the checker *)
  Compute check_layout dims (mk_layout_from_indexed_layout dims indexed_layout program) program.

  Definition soundness := @GridLayout.soundness rel var fn aggregator T sig context rule_eqb rule_eqb_spec.

  Theorem soundness_check :
    forall f,
      network_prog_impl_fact
      (mk_dataflow_network dims indexed_layout program) f ->
      prog_impl_fact program f.
  Proof.
    intros.
    eapply soundness; eauto.
    vm_compute. reflexivity.
  Qed.

End SmallExample.
