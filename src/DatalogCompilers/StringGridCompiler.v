(* StringGridCompiler: a concrete compiler for string-datalog programs laid out on a 2D grid.
   It is just the composition of two independent backends:
     - StringDatalog  : the datalog program representation (string relations/variables/functions),
     - GridTopology   : the node-id type and grid topology graph.
   Given a program and an (indexed) layout it compiles end to end. *)

From Stdlib Require Import List ZArith.
From Datalog Require Import Datalog.
From DatalogRocq Require Import EncodeLayout GridTopology StringDatalog StringDatalogParams
  GridGraph SortedListNat DistributedHardwareProgram.
From coqutil Require Import Map.Interface Result.
Import ListNotations.
Import StringDatalogParams.

Notation node_id     := GridTopology.node_id.
Notation node_id_map := GridTopology.node_id_map.
Notation destination := (@DistributedHardwareProgram.destination node_id).

(* [make_layout_map program layout] : a [node -> rules] map from an indexed layout
   (a list of [(node_id, rule_index_list)] pairs over the [program]). *)
Definition make_layout_map
    (program : list rule)
    (layout  : list (node_id * list nat))
    : node_id_map (list rule) :=
  List.fold_left
    (fun acc '(nid, idxs) =>
      let empty_rule := normal_rule [] [] in
      let rules := List.map (fun i => List.nth i program empty_rule) idxs in
      map.put acc nid rules)
    layout map.empty.

(* The end-to-end compiler: wire the string datalog backend and the grid topology into [compile]. *)
Definition compile_program
    (program        : list rule)
    (layout         : list (node_id * list nat))
    (fact_producers : fact_locations (node_id := node_id))
    (fact_consumers : fact_locations (node_id := node_id))
    (topo_dims      : GridGraph.Dimensions)
    (fuel           : nat)
    : _ :=
  compile
    (Node               := node_id)
    (node_id            := node_id)
    (node_id_eqb        := GridTopology.node_id_eqb)
    (node_id_set        := node_id_map unit)
    (node_id_edge_set   := node_id_map (node_id_map unit))
    (var_node_set       := StringDatalog.var_node_set)
    (var_edge_set       := StringDatalog.var_edge_set)
    (forwarding_table   := SortedListNat.map (list destination))
    (rel_dependency_map := SortedListNat.map (node_id_map unit))
    (fn_id_map          := StringDatalog.fn_id_map)
    (rel_relid_map      := StringDatalog.rel_relid_map)
    (layout_map         := node_id_map (list rule))
    (lowered_layout_map := node_id_map (list HardwareProgram.lowered_rule))
    (var_idx_map        := StringDatalog.var_idx_map)
    (node_ftable_map    := node_id_map (SortedListNat.map (list destination)))
    (make_layout_map program layout) fact_producers fact_consumers
    (GridTopology.make_topo_graph topo_dims) fuel.
