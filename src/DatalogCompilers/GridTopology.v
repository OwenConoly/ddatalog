(* GridTopology: the *topology* backend for the compiler -- node ids and the grid graph.
   This is entirely independent of the datalog program types (relations/variables/functions):
   it only fixes what a node identifier is and how to build a grid topology graph from
   dimensions.  Combine it with a datalog backend (e.g. StringDatalog) to get a concrete
   compiler.

   Node ids are grid coordinates represented as [list nat] -- exactly [GridGraph.Node] -- so the
   grid connectivity proofs apply directly,
   with no extra encoding.  This works for grids of any dimension, not just 2D. *)

From Stdlib Require Import List ZArith.
From DatalogRocq Require Import DistributedDatalogToHardwareCompiler GridGraph SortedListList SortedListNat ComputableGraph.
From coqutil Require Import Map.Interface Eqb Decidable Datatypes.List.
From GraphSearch Require Import GraphInterface GraphImpl.
Import ListNotations.

#[global] Instance node_id_map T : map.map Node T := @SortedListList.map nat Nat.ltb SortedListNat.Nat_strict_order T.

Lemma node_id_map_ok T : map.ok (node_id_map T).
Proof. exact (@SortedListList.ok nat Nat.ltb SortedListNat.Nat_strict_order T). Qed.

(* Build the grid topology graph (node set + neighbor edges) from dimensions.  Since a node id
   *is* its coordinate list, there is no destructuring/reassembly. *)
Definition build_topo_node_set (dims : GridGraph.Dimensions) : node_id_map unit :=
  List.fold_left
    (fun acc n => map.put acc n tt)
    (GridGraph.all_nodes_h dims)
    map.empty.

#[global] Instance node_id_eqb : Eqb Node := list_eqb Nat.eqb.

Lemma nat_eqb_dec : EqDecider Nat.eqb.
Proof. intros x y. destruct (Nat.eqb_spec x y); constructor; assumption. Qed.

#[global] Instance node_id_eqb_ok : Eqb_ok node_id_eqb.
Proof.
  intros a b. unfold eqb, node_id_eqb.
  destruct (@list_eqb_spec nat Nat.eqb nat_eqb_dec a b); assumption.
Qed.

#[global] Instance node_id_graph : graph.graph Node :=
  @GraphImpl.graph_map Node node_id_eqb node_id_eqb_ok
    (node_id_map unit) (node_id_map_ok unit)
    (node_id_map (node_id_map unit)) (node_id_map_ok _).

#[global] Instance node_id_graph_ok : graph.ok node_id_graph.
Proof. exact (@GraphImpl.graph_map_ok Node node_id_eqb node_id_eqb_ok
                (node_id_map unit) (node_id_map_ok unit)
                (node_id_map (node_id_map unit)) (node_id_map_ok _)). Qed.

Definition build_topo_edges (dims : GridGraph.Dimensions) : node_id_graph :=
  let nodes := GridGraph.all_nodes_h dims in
  List.fold_left
    (fun acc n =>
      graph.put_edges acc n (List.filter (fun n2 => GridGraph.is_neighbor dims n n2) nodes))
    nodes graph.empty.

Definition make_topo_graph (dims : GridGraph.Dimensions)
    : @ComputableGraph Node (node_id_map unit) node_id_graph :=
  {| ComputableGraph.nodes := build_topo_node_set dims;
     ComputableGraph.edges := build_topo_edges dims |}.
