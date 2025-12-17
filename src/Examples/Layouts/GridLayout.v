From Stdlib Require Import List Bool Lia.
From Datalog Require Import Datalog.
From DatalogRocq Require Import Dataflow GridGraph.
From coqutil Require Import Map.Interface.
Import ListNotations.

Section GridLayout.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T} `{query_sig : query_signature rel}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.
  Context {rel_eqb : rel -> rel -> bool} {rel_eqb_spec : forall x0 y0 : rel, BoolSpec (x0 = y0) (x0 <> y0) (rel_eqb x0 y0)}.
  Context {fn_eqb : fn -> fn -> bool} {fn_eqb_spec : forall x0 y0 : fn, BoolSpec (x0 = y0) (x0 <> y0) (fn_eqb x0 y0)}.
  Context {aggregator_eqb : aggregator -> aggregator -> bool}
          {aggregator_eqb_spec : forall x0 y0 : aggregator, BoolSpec (x0 = y0) (x0 <> y0) (aggregator_eqb x0 y0)}.

  Definition rule := Datalog.rule rel var fn aggregator.

  Context {rule_eqb : rule -> rule -> bool}.
  Context {rule_eqb_spec : forall r1 r2 : rule,
                            BoolSpec (r1 = r2) (r1 <> r2) (rule_eqb r1 r2)}.

  Definition mk_grid_graph (dims : list nat) : Dataflow.Graph := GridGraph dims.

  Definition mk_layout_from_indexed_layout (dims : list nat) (indexed_layout : list (Node * list nat)) (program : list rule) (n : Node) : list rule :=
      if check_node_in_bounds dims n then
      match find (fun p => GridGraph.node_eqb (fst p) n) indexed_layout with
      | None => []
      | Some (_, ris) =>
          fold_right
            (fun ri acc =>
               match nth_error program ri with
               | Some r => r :: acc
               | None => acc
               end)
            [] ris
      end
    else [].

  (* Just putting in some dummy values for now *)
  Definition mk_always_forward_table (dims : list nat) (n : Node) : rel * (list T) -> list Node :=
    fun f => filter (GridGraph.is_neighbor dims n) (all_nodes_h dims).

  Definition mk_no_input_fn (n : Node) (f : rel * (list T)) : Prop := False.

  Definition mk_all_output_fn (n : Node) (f : rel * (list T)) : Prop := True.

  Definition mk_dataflow_network
             (dims : list nat)
             (indexed_layout : list (Node * list nat))
             (program : list rule) : Dataflow.DataflowNetwork :=
    {|
      Dataflow.graph := mk_grid_graph dims;
      Dataflow.layout := mk_layout_from_indexed_layout dims indexed_layout program;
      Dataflow.forward := mk_always_forward_table dims;
      Dataflow.input := mk_no_input_fn;
      Dataflow.output := mk_all_output_fn
    |}.

  Definition rule_in_layout (r : rule) (layout : Node -> list rule) (dims : list nat): bool :=
    existsb (fun n => existsb (rule_eqb r) (layout n))
            (all_nodes_h dims).

  Definition node_rules_ok (n : Node) (layout : Node -> list rule) (program : list rule): bool :=
    forallb (fun r => existsb (rule_eqb r) program)
            (layout n).

  Definition check_layout (dims : list nat) (layout : Node -> list rule) (program : list rule) : bool :=
    forallb (fun n => node_rules_ok n layout program) (all_nodes_h dims) &&
    forallb (fun r => rule_in_layout r layout dims) program.

  Lemma layout_nonempty_only_valid_nodes :
    forall n r dims indexed_layout program,
      In r (mk_layout_from_indexed_layout dims indexed_layout program n) ->
      GridGraph.is_graph_node dims n.
  Proof.
    intros n r dims indexed_layout program Hlayout.
    unfold mk_layout_from_indexed_layout in Hlayout.
    destruct (check_node_in_bounds dims n) eqn:Hbounds; try discriminate.
    - apply GridGraph.check_node_in_bounds_h_correct; eauto.
    - contradiction.
  Qed.

Theorem good_layout :
    forall dims indexed_layout program,
    check_layout dims (mk_layout_from_indexed_layout dims indexed_layout program) program = true ->
    Dataflow.good_layout (mk_layout_from_indexed_layout dims indexed_layout program) (GridGraph dims).(nodes) program.
Proof.
    unfold check_layout.
    unfold Dataflow.good_layout.
    intros.
    split.
    - apply Forall_forall. intros. apply andb_true_iff in H. destruct H as [H_nodes_ok H_rule_in_layout].
      rewrite forallb_forall in H_rule_in_layout.
      apply H_rule_in_layout in H0 as H_layout.
      unfold rule_in_layout in H_layout. rewrite existsb_exists in H_layout.
      destruct H_layout as [n [H_n_in_nodes H_r_in_layout]].
      rewrite existsb_exists in H_r_in_layout.
      destruct H_r_in_layout as [r H_r_eq].
      exists n. destruct H_r_eq as [Hin H_r_eq]. 
      destruct (rule_eqb_spec x r).
      + subst. split; auto. apply all_nodes_correct. apply H_n_in_nodes.
      + discriminate H_r_eq.
    - intros.
      apply andb_true_iff in H. destruct H as [H_nodes_ok H_rule_in_layout].
      rewrite forallb_forall in H_nodes_ok.
      rewrite forallb_forall in H_rule_in_layout.
      split.
      + apply layout_nonempty_only_valid_nodes in H0 as H_layout_nonempty.
        auto.
      + apply layout_nonempty_only_valid_nodes in H0 as H_layout_nonempty.
        apply all_nodes_correct in H_layout_nonempty.
        specialize (H_nodes_ok n H_layout_nonempty).
        unfold node_rules_ok in H_nodes_ok.
        rewrite forallb_forall in H_nodes_ok.
        specialize (H_nodes_ok r H0).
        rewrite existsb_exists in H_nodes_ok.
        destruct H_nodes_ok as [r' H_r'_in_program].
        destruct H_r'_in_program as [Hin H_r_eq].
        destruct (rule_eqb_spec r r').
        * subst. auto.
        * discriminate H_r_eq.
Qed.

Lemma good_network :
  forall dims indexed_layout program,
  check_layout dims (mk_layout_from_indexed_layout dims indexed_layout program) program = true ->
  Dataflow.good_network (mk_dataflow_network dims indexed_layout program) program.
Proof.
  intros dims indexed_layout program Hcheck.
  unfold mk_dataflow_network. unfold good_network.
  split.
  - apply GridGraph.good_graph.
  - split. 
    + apply good_layout. assumption.
    + split.
      * simpl. unfold good_forwarding. intros. unfold mk_always_forward_table in H.
        apply filter_In in H.
        destruct H as [Hneighbor Hin].
        apply GridGraph.is_neighbor_correct in Hin.
        split; try inversion Hin; auto.
      * simpl. unfold good_input. intros. inversion H.
Qed.

Theorem soundness :
    forall dims indexed_layout program,
    check_layout dims (mk_layout_from_indexed_layout dims indexed_layout program) program = true ->
    forall f,
    network_prog_impl_fact (mk_dataflow_network dims indexed_layout program) f ->
    prog_impl_fact program f.
Proof.
  intros dims indexed_layout program Hcheck f Hnetwork.
  apply (Dataflow.soundness (mk_dataflow_network dims indexed_layout program) program); auto.
  apply good_network; auto.
Qed.

End GridLayout.