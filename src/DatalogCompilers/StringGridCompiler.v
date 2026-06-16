(* StringGridCompiler: a concrete compiler for string-datalog programs laid out on a 2D grid.
   It is just the composition of two independent backends:
     - StringDatalog  : the datalog program representation (string relations/variables/functions),
     - GridTopology   : the node-id type and grid topology graph.
   Given a program and an (indexed) layout it compiles end to end. *)

From Stdlib Require Import List ZArith String.
From Datalog Require Import Datalog.
From DatalogRocq Require Import DistributedDatalogToHardwareCompiler GridTopology StringDatalog StringDatalogParams
  GridGraph SortedListNat DistributedHardwareProgram.
From coqutil Require Import Map.Interface Map.SortedListString Result.
Import ListNotations.
Import StringDatalogParams.

Notation node_id     := GridTopology.node_id.
Notation node_id_map := GridTopology.node_id_map.
Notation destination := (@DistributedHardwareProgram.destination node_id).
Notation lowered_rule := (@HardwareProgram.lowered_rule var).

(* concrete fact-location tables: [rel]/[rel_id]-keyed maps to node lists. *)
Notation rel_locs_map   := (SortedListString.map (list node_id)).
Notation relid_locs_map  := (SortedListNat.map (list node_id)).

(* [make_layout_map program layout] : a [node -> rules] map from an indexed layout
   (a list of [(node_id, rule_index_list)] pairs over the [program]). *)
Definition make_layout_map
    (program : list rule)
    (layout  : list (node_id * list nat))
    : node_id_map (list rule) :=
  List.fold_left
    (fun acc '(nid, idxs) =>
      let empty_rule := Datalog.normal_rule [] [] in
      let rules := List.map (fun i => List.nth i program empty_rule) idxs in
      map.put acc nid rules)
    layout map.empty.

(* The end-to-end compiler: wire the string datalog backend and the grid topology into [compile]. *)
Definition compile_program
    (program        : list rule)
    (layout         : list (node_id * list nat))
    (fact_producers : rel_locs_map)
    (fact_consumers : rel_locs_map)
    (topo_dims      : GridGraph.Dimensions)
    (fuel           : nat)
    : _ :=
  compile
    (Node               := node_id)
    (node_id            := node_id)
    (node_id_eqb        := GridTopology.node_id_eqb)
    (var_eqb            := var_eqb)
    (node_id_set        := node_id_map unit)
    (node_id_edge_set   := node_id_map (node_id_map unit))
    (var_node_set       := StringDatalog.var_node_set)
    (var_edge_set       := StringDatalog.var_edge_set)
    (forwarding_table   := SortedListNat.map (list destination))
    (rel_dependency_map := SortedListNat.map (node_id_map unit))
    (fn_id_map          := StringDatalog.fn_id_map)
    (rel_relid_map      := StringDatalog.rel_relid_map)
    (layout_map         := node_id_map (list rule))
    (lowered_layout_map := node_id_map (list lowered_rule))
    (fact_locations_map         := rel_locs_map)
    (lowered_fact_locations_map := relid_locs_map)
    (var_idx_map        := StringDatalog.var_idx_map)
    (node_ftable_map    := node_id_map (SortedListNat.map (list destination)))
    (make_layout_map program layout) fact_producers fact_consumers
    (GridTopology.make_topo_graph topo_dims) fuel.

(* A computed routing fuel, to replace the hand-tuned magic constant. The only thing [fuel] bounds
   is the BFS path search [get_path] over the topology; BFS visits each node at most once, so the
   number of grid nodes is always enough. (Sufficiency theorem forthcoming -- this computes the
   value now; the proof that it always suffices follows.) *)
Definition grid_fuel (topo_dims : GridGraph.Dimensions) : nat :=
  List.length (GridGraph.all_nodes_h topo_dims).

(* PLACEHOLDER fact-locations: make EVERY grid node an input AND output node for EVERY relation
   appearing in [program].  Useful for examples that have not (yet) designated real input/output
   nodes, so they still satisfy the compiler's input/output routing gates.
   TODO: replace with the real input (fact-producer) and output (fact-consumer) nodes for the
   program -- only the genuine EDB sources and result sinks, not every node. *)
Definition all_io_locations (program : list rule) (layout : list (node_id * list nat))
    (topo_dims : GridGraph.Dimensions) : rel_locs_map :=
  let nodes := GridGraph.all_nodes_h topo_dims in
  (* only relations of the rules the layout actually assigns are in the global context *)
  let assigned := List.flat_map (fun '(_, idxs) =>
                    List.map (fun i => List.nth i program (Datalog.normal_rule [] [])) idxs) layout in
  map.of_list (List.map (fun R => (R, nodes))
           (List.nodup String.string_dec (List.flat_map Datalog.all_rels assigned))).
