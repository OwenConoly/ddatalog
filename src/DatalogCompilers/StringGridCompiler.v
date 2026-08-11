(* StringGridCompiler: a concrete compiler for string-datalog programs laid out on a 2D grid.
   It is just the composition of two independent backends:
     - StringDatalog  : the datalog program representation (string relations/variables/functions),
     - GridTopology   : the node-id type and grid topology graph.
   Given a program and an (indexed) layout it compiles end to end. *)

From Stdlib Require Import List ZArith String.
From Datalog Require Import Datalog NattifyRel RelMap.
From DatalogRocq Require Import DistributedDatalogToHardwareCompiler GridTopology StringDatalog StringDatalogParams
  GridGraph SortedListNat SortedListList SortedListPair DistributedHardwareProgram.
From coqutil Require Import Map.Interface Map.SortedListString Result.
Import ListNotations.
Import StringDatalogParams.

Notation node_id     := GridGraph.Node.
Notation node_id_map := GridTopology.node_id_map.


(* the compiled forwarding table is keyed on (relation, original source) *)
Notation ftable_map :=
  (@SortedListPair.map rel_id node_id
     Nat.ltb SortedListNat.Nat_strict_order
     (@SortedListList.list_order nat Nat.ltb)
     (@SortedListList.list_strict_order nat Nat.ltb SortedListNat.Nat_strict_order)
     (list node_id)).

Lemma ftable_map_ok : map.ok ftable_map.
Proof. apply SortedListPair.ok. Qed.

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
      let empty_rule := normal_rule [] [] in
      let rules := List.map (fun i => List.nth i program empty_rule) idxs in
      map.put acc nid rules)
    layout map.empty.

(* [compile] now consumes an already-numbered ([rel_id]) program, so the string relations are
   nattified here first (via [NattifyRel.encode_rel] over the program's own relations -- matching
   [nattify_and_compile_correct]'s [input_rels := program_rels p]). *)
Definition rel_ids (program : list rule) : string -> rel_id :=
  encode_rel (List.flat_map Datalog.all_rels program) program.

Definition nattify_layout (enc : string -> rel_id)
    (slayout : node_id_map (list rule)) : node_id_map (list HardwareProgram.lowered_rule) :=
  map.fold (fun acc nid rules => map.put acc nid (List.map (map_rule_rels enc) rules)) map.empty slayout.

Definition nattify_fact_locs (enc : string -> rel_id) (fl : rel_locs_map) : relid_locs_map :=
  map.fold (fun acc R locs => map.put acc (enc R) locs) map.empty fl.

(* UNTRUSTED stand-in for the external forwarding-table generator: flood every relation along
   every grid edge.  [compile] re-checks whatever it is given ([ftables_in_graphb] for the hops,
   [check_layout_routable] for producer->consumer reachability), so nothing here is trusted.
   TODO: replace with the table the external router actually produces. *)
Definition flood_ftables (rels : list rel_id) (topo_dims : GridGraph.Dimensions)
    : node_id_map ftable_map :=
  let nodes := GridGraph.all_nodes_h topo_dims in
  List.fold_left
    (fun fts n =>
      let nbrs := List.filter (fun m => GridGraph.is_neighbor topo_dims n m) nodes in
      map.put fts n
        (List.fold_left
           (fun ft R => List.fold_left (fun ft s => map.put ft (R, s) nbrs) nodes ft)
           rels map.empty))
    nodes map.empty.

(* The end-to-end compiler: nattify the string layout / fact-locations, then wire the numbered
   program and the grid topology into the fuel-free [compile] (which computes the routing fuel
   = #grid-nodes itself). *)
Definition compile_program
    (program        : list rule)
    (layout         : list (node_id * list nat))
    (fact_producers : rel_locs_map)
    (fact_consumers : rel_locs_map)
    (topo_dims      : GridGraph.Dimensions)
    : _ :=
  let enc := rel_ids program in
  let rels := List.map enc (rel_table (List.flat_map Datalog.all_rels program) program) in
  compile
    (nattify_layout enc (make_layout_map program layout))
    (nattify_fact_locs enc fact_producers) (nattify_fact_locs enc fact_consumers)
    (flood_ftables rels topo_dims)
    (GridTopology.make_topo_graph topo_dims).

(* The rel-name <-> rel-id table the frontend assigns (via [NattifyRel]'s [rel_table] / [encode_rel]),
   exposed for tooling that needs to relate a fact keyed by relation name to the compiled program's
   numeric [output_rel]/[trel] ids -- e.g. a human-authored/random input-fact workload. *)
Definition compile_program_rel_ids (program : list rule) : list (string * rel_id) :=
  let enc := rel_ids program in
  List.map (fun R => (R, enc R)) (rel_table (List.flat_map Datalog.all_rels program) program).

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
