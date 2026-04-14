From Stdlib Require Import List ZArith Lia String.
From DatalogRocq Require Import Family EncodeLayout GridGraph SortedListList SortedListPair SortedListNat ComputableGraph.
From coqutil Require Import Map.Interface Map.SortedListString.
Import ListNotations.
Import StringDatalogParams.

Print family_program.

(* Input layout from ILP solver *)

(* Definition generated_layout := 
  [((0,0), []); ((0,1), [7]); ((0,2), [5]); ((1,0), [4]); ((1,1), [1]);
           ((1,2), [2]); ((2,0), [6]); ((2,1), [0]); ((2,2), [3])]. *)

Definition generated_layout := 
  [((0,0), [0])].

(* ── Map instances *)
Definition list_nat_map T := @SortedListList.map nat Nat.ltb SortedListNat.Nat_strict_order T.
Lemma list_nat_map_ok T : map.ok (list_nat_map T).
  exact (@SortedListList.ok nat Nat.ltb SortedListNat.Nat_strict_order T).
Qed.

(* Make the graph *)
Definition grid_node_set := list_nat_map unit.
Instance grid_node_set_ok : map.ok grid_node_set := list_nat_map_ok unit.

Definition grid_edge_set := list_nat_map grid_node_set.
Instance grid_edge_set_ok : map.ok grid_edge_set := list_nat_map_ok grid_node_set.

Definition build_node_set (dims : GridGraph.Dimensions) : grid_node_set :=
  List.fold_left (fun acc n => map.put acc n tt)
    (GridGraph.all_nodes dims) map.empty.

Definition build_edge_set (dims : GridGraph.Dimensions) : grid_edge_set :=
  let nodes := GridGraph.all_nodes dims in
  List.fold_left (fun acc n =>
    let neighbors := List.filter (fun n2 => GridGraph.is_neighbor dims n n2) nodes in
    let neighbor_map := List.fold_left (fun m nb => map.put m nb tt) neighbors map.empty in
    map.put acc n neighbor_map
  ) nodes map.empty.

Definition make_grid_computable_graph (dims : GridGraph.Dimensions)
    : @ComputableGraph GridGraph.Node grid_node_set grid_edge_set :=
  {|
    nodes := build_node_set dims;
    edges := build_edge_set dims
  |}.

(* Nat * Nat map *)
Definition node_id_map T := @SortedListPair.map nat nat 
  Nat.ltb SortedListNat.Nat_strict_order 
  Nat.ltb SortedListNat.Nat_strict_order T.
Lemma node_id_map_ok T : map.ok (node_id_map T).
  exact (@SortedListPair.ok nat nat 
    Nat.ltb SortedListNat.Nat_strict_order 
    Nat.ltb SortedListNat.Nat_strict_order T).
Qed.

(* Convert Layout to Map*)
Definition generated_layout_map : node_id_map (list rule) :=
  List.fold_left (fun acc '(nid, idxs) =>
    let rules := List.map (fun i => List.nth i family_program (List.hd r_ancestor1 family_program)) idxs in
    map.put acc nid rules
  ) generated_layout map.empty.


(* Topology *)

Definition topo_dims : GridGraph.Dimensions := [3; 3].

Definition topo_node_set := node_id_map unit.
Definition topo_edge_set := node_id_map (node_id_map unit).

Definition build_topo_node_set (dims : GridGraph.Dimensions) : topo_node_set :=
  List.fold_left (fun acc n =>
    match n with
    | [r; c] => map.put acc (r, c) tt
    | _ => acc
    end) (GridGraph.all_nodes dims) map.empty.

Definition build_topo_edge_set (dims : GridGraph.Dimensions) : topo_edge_set :=
  let nodes := GridGraph.all_nodes dims in
  List.fold_left (fun acc n =>
    match n with
    | [r; c] =>
      let neighbors := List.filter (fun n2 => GridGraph.is_neighbor dims n n2) nodes in
      let neighbor_map := List.fold_left (fun m nb =>
        match nb with
        | [r'; c'] => map.put m (r', c') tt
        | _ => m
        end) neighbors map.empty in
      map.put acc (r, c) neighbor_map
    | _ => acc
    end) nodes map.empty.

Definition topo_graph : @ComputableGraph node_id topo_node_set topo_edge_set :=
  {|
    nodes := build_topo_node_set topo_dims;
    edges := build_topo_edge_set topo_dims
  |}.

Definition compiled_family := compile 
  (Node := node_id)
  (var_eqb := var_eqb)
  (node_id_set := node_id_map unit)
  (node_id_edge_set := node_id_map (node_id_map unit))
  (var_node_set := SortedListString.map unit)
  (var_edge_set := SortedListString.map (SortedListString.map unit))
  (forwarding_table := SortedListNat.map (list destination))
  (rel_dependency_map := SortedListNat.map (node_id_map unit))
  (fn_id_map := SortedListString.map fn_id)
  (rel_relid_map := SortedListString.map rel_id)
  (layout_map := node_id_map (list rule))
  (lowered_layout_map := node_id_map (list lowered_rule))
  (var_idx_map := SortedListString.map nat)
  (node_ftable_map := node_id_map (SortedListNat.map (list destination)))
  generated_layout_map topo_graph 100.

Compute collect_global_names_layout generated_layout_map initial_global_context
        (Node := (nat * nat))
        (node_id_set := node_id_map unit)
        (rel_dependency_map := SortedListNat.map (node_id_map unit)).
Compute global_rename_rule_layout generated_layout_map (collect_global_names_layout generated_layout_map initial_global_context)
        (lowered_layout_map := node_id_map (list lowered_rule)).