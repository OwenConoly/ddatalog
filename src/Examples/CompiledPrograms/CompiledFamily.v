From Stdlib Require Import List ZArith Lia String.
From DatalogRocq Require Import Family EncodeLayout GridGraph SortedListList SortedListPair SortedListNat ComputableGraph.
From coqutil Require Import Map.Interface Map.SortedListString Result.
Import ListNotations.
Import StringDatalogParams.

Print family_program.

(* Input layout from ILP solver *)

Definition generated_layout := 
  [((0,0), []); ((0,1), [7]); ((0,2), [5]); ((1,0), [4]); ((1,1), [1]);
           ((1,2), [2]); ((2,0), [6]); ((2,1), [0]); ((2,2), [3])].


(* ── Map creation ── *)

Definition list_nat_map T := @SortedListList.map nat Nat.ltb SortedListNat.Nat_strict_order T.
Lemma list_nat_map_ok T : map.ok (list_nat_map T).
  exact (@SortedListList.ok nat Nat.ltb SortedListNat.Nat_strict_order T).
Qed.

Definition node_id_map T := @SortedListPair.map nat nat
  Nat.ltb SortedListNat.Nat_strict_order
  Nat.ltb SortedListNat.Nat_strict_order T.

(* Definition generated_layout := [((0,0), [1])]. *)

Definition generated_layout_map : node_id_map (list rule) :=
  List.fold_left (fun acc '(nid, idxs) =>
    let rules := List.map (fun i => List.nth i family_program (List.hd r_ancestor1 family_program)) idxs in
    map.put acc nid rules
  ) generated_layout map.empty.

(* ── Abbreviations for the map instances we keep threading ── *)

Notation gctx := (global_context
  (fn_id_map := SortedListString.map fn_id)
  (rel_relid_map := SortedListString.map rel_id)
  (Node := (nat * nat))
  (node_id_set := node_id_map unit)
  (rel_dependency_map := SortedListNat.map (node_id_map unit))).

Notation ll_map := (node_id_map (list lowered_rule)).

(* ═══════════════════════════════════════════════
   Step 0: What rule are we compiling?
   ═══════════════════════════════════════════════ *)

Eval vm_compute in r_ancestor1.
(* ancestor(x,y) :- parent(x,y) *)

(* ═══════════════════════════════════════════════
   Step 1: collect_global_names_layout
   Assigns numeric IDs to every rel and fn name.
   ═══════════════════════════════════════════════ *)

Definition gctx1 : gctx :=
  collect_global_names_layout generated_layout_map initial_global_context.

Eval vm_compute in gctx1.(rel_map).
(* Expect: "parent" -> 0, "ancestor" -> 1  (or similar) *)

Eval vm_compute in gctx1.(fn_map).
(* Expect: empty — no function symbols in ancestor rules *)

Eval vm_compute in gctx1.(last_rel_id).
Eval vm_compute in gctx1.(last_fn_id).

(* ═══════════════════════════════════════════════
   Step 2: global_rename_rule_layout
   Replaces string names with numeric IDs.
   ═══════════════════════════════════════════════ *)

Definition llayout : result ll_map :=
  global_rename_rule_layout generated_layout_map gctx1.

Eval vm_compute in llayout.
(* Expect: Success { (0,0) -> [ {lhyps=[{lf_R=0; args=[LVar "x"; LVar "y"]}];
                                  lconcls=[{lf_R=1; args=[LVar "x"; LVar "y"]}]} ] } *)

(* ═══════════════════════════════════════════════
   Step 3: Zoom into the single lowered rule
   ═══════════════════════════════════════════════ *)

(* Pull out the lowered program for node (0,0) *)
Definition lprog : result (list lowered_rule) :=
  match llayout with
  | Success m => match map.get m (0,0) with
                 | Some p => Success p
                 | None => error:("no program at (0,0)")
                 end
  | Failure e => Failure e
  end.

Eval vm_compute in lprog.

(* Pull out just the first rule's hyps *)
Definition lrule0_hyps : result (list lowered_fact) :=
  match lprog with
  | Success (r :: _) => Success r.(lhyps)
  | Success [] => error:("empty program")
  | Failure e => Failure e
  end.

Eval vm_compute in lrule0_hyps.
(* Expect: [{lf_R = 0; lf_args = [LVar "x"; LVar "y"]}] *)

(* ═══════════════════════════════════════════════
   Step 4: create_dependency_graph
   Build the var co-occurrence graph from hyps.
   ═══════════════════════════════════════════════ *)

Definition test_hyps : list lowered_fact :=
  match lrule0_hyps with Success h => h | _ => [] end.

Definition dep_g := create_dependency_graph
  (var_node_set := SortedListString.map unit)
  (var_edge_set := SortedListString.map (SortedListString.map unit))
  test_hyps.

(* What nodes are in the graph? *)
Eval vm_compute in map.keys dep_g.(nodes).
(* Expect: ["x"; "y"] *)

(* What are x's neighbors? *)
Eval vm_compute in map.keys (vg_neighbors dep_g "x"%string).

(* What are y's neighbors? *)
Eval vm_compute in map.keys (vg_neighbors dep_g "y"%string).


   (* ═══════════════════════════════════════════════
   Step 4a: Check degrees explicitly
   ═══════════════════════════════════════════════ *)

Definition degree_x := compute_degree
  (var_node_set := SortedListString.map unit)
  (var_edge_set := SortedListString.map (SortedListString.map unit))
  dep_g "x"%string.

Definition degree_y := compute_degree
  (var_node_set := SortedListString.map unit)
  (var_edge_set := SortedListString.map (SortedListString.map unit))
  dep_g "y"%string.

Eval vm_compute in degree_x.
Eval vm_compute in degree_y.
(* If symmetric fix applied: both 1. If not: x=0, y=1 *)

(* ═══════════════════════════════════════════════
   Step 4b: Check degree-to-visited with empty visited
   (This is what the first iteration actually uses)
   ═══════════════════════════════════════════════ *)

Definition empty_visited : SortedListString.map unit := map.empty.

Definition deg_to_vis_x := compute_degree_to_visited_set
  (var_node_set := SortedListString.map unit)
  (var_edge_set := SortedListString.map (SortedListString.map unit))
  dep_g empty_visited "x"%string.

Definition deg_to_vis_y := compute_degree_to_visited_set
  (var_node_set := SortedListString.map unit)
  (var_edge_set := SortedListString.map (SortedListString.map unit))
  dep_g empty_visited "y"%string.

Eval vm_compute in deg_to_vis_x.
Eval vm_compute in deg_to_vis_y.
(* Both should be 0 — no neighbors are in the visited set yet *)

(* ═══════════════════════════════════════════════
   Step 4c: What does compute_max_degree_var_to_visited_set return?
   ═══════════════════════════════════════════════ *)

Definition max_deg_to_vis := compute_max_degree_var_to_visited_set
  (var_node_set := SortedListString.map unit)
  (var_edge_set := SortedListString.map (SortedListString.map unit))
  dep_g empty_visited.

Eval vm_compute in max_deg_to_vis.

(* ═══════════════════════════════════════════════
   Step 4d: What does compute_max_degree_var return?
   (Fallback when degree-to-visited is None)
   ═══════════════════════════════════════════════ *)

Definition max_deg := compute_max_degree_var
  (var_node_set := SortedListString.map unit)
  (var_edge_set := SortedListString.map (SortedListString.map unit))
  dep_g.

Eval vm_compute in max_deg.

(* ═══════════════════════════════════════════════
   Step 4e: What does choose_next_var return for initial context?
   ═══════════════════════════════════════════════ *)

Definition init_ctx := initial_ordering_context
  (var_node_set := SortedListString.map unit)
  (var_edge_set := SortedListString.map (SortedListString.map unit))
  dep_g.

Definition first_choice := choose_next_var
  (var_node_set := SortedListString.map unit)
  (var_edge_set := SortedListString.map (SortedListString.map unit))
  init_ctx.

Eval vm_compute in first_choice.

(* ═══════════════════════════════════════════════
   Step 4f: Simulate one step manually
   ═══════════════════════════════════════════════ *)

(* After visiting whatever first_choice returns *)
Definition ctx_after_1 :=
  match first_choice with
  | Some v => visit_node
      (var_node_set := SortedListString.map unit)
      (var_edge_set := SortedListString.map (SortedListString.map unit))
      v init_ctx
  | None => init_ctx
  end.

Eval vm_compute in ctx_after_1.(order).

Eval vm_compute in map.keys ctx_after_1.(dep_graph).(nodes).

Eval vm_compute in map.keys ctx_after_1.(visited).

Definition second_choice := choose_next_var
  (var_node_set := SortedListString.map unit)
  (var_edge_set := SortedListString.map (SortedListString.map unit))
  ctx_after_1.

Eval vm_compute in second_choice.

(* ═══════════════════════════════════════════════
   Step 4g: Check map.fold order directly
   This tells us if SortedListString folds alphabetically
   ═══════════════════════════════════════════════ *)

Definition fold_order : list string :=
  map.fold (fun acc k (_:unit) => k :: acc) [] dep_g.(nodes).

Eval vm_compute in fold_order.

Definition fold_order_rev : list string :=
  List.rev (map.fold (fun acc k (_:unit) => k :: acc) [] dep_g.(nodes)).

Eval vm_compute in fold_order_rev.

(* ═══════════════════════════════════════════════
   Step 5: compute_variable_ordering
   Greedy max-degree-first ordering.
   ═══════════════════════════════════════════════ *)

Definition var_order := compute_variable_ordering
  (var_node_set := SortedListString.map unit)
  (var_edge_set := SortedListString.map (SortedListString.map unit))
  dep_g.

Eval vm_compute in var_order.

(* ═══════════════════════════════════════════════
   Step 6: compute_var_order (column order of the hyp)
   ═══════════════════════════════════════════════ *)

Definition hyp0 := List.hd {| lf_R := 0; lf_args := [LVar "x"; LVar "x"] |} test_hyps.

Definition col_order := compute_var_order hyp0.

Eval vm_compute in col_order.

(* ═══════════════════════════════════════════════
   Step 7: compute_permutation
   Maps column order -> variable ordering.
   ═══════════════════════════════════════════════ *)

Definition perm := compute_permutation
  (var_eqb := var_eqb)
  (var_idx_map := SortedListString.map nat)
  col_order var_order.

Eval vm_compute in perm.

(* ═══════════════════════════════════════════════
   Step 8: generate_trie
   Creates a trie with that permutation.
   ═══════════════════════════════════════════════ *)

Definition gctx_for_trie : gctx := gctx1.

Definition nctx0 := initial_node_context (0, 0).

Definition trie_and_nctx := generate_trie
  (var_eqb := var_eqb)
  (var_idx_map := SortedListString.map nat)
  hyp0 var_order [] gctx_for_trie nctx0.

Eval vm_compute in (fst trie_and_nctx).
(* Expect: {tid=0; trel=0; tperm=[0;1]} if fixed, [1;0] if buggy *)

(* ═══════════════════════════════════════════════
   Step 9: generate_join for variable "x"
   Which tries/levels does "x" touch?
   ═══════════════════════════════════════════════ *)

Definition test_trie := fst trie_and_nctx.

Definition join_x := generate_join
  (var_eqb := var_eqb)
  [test_trie] "x"%string test_hyps.

Eval vm_compute in join_x.
(* tries=[0], trie_levels=[perm[0]], clauses=[0] *)

Definition join_y := generate_join
  (var_eqb := var_eqb)
  [test_trie] "y"%string test_hyps.

Eval vm_compute in join_y.

(* ═══════════════════════════════════════════════
   Step 10: Full compile — end to end
   ═══════════════════════════════════════════════ *)

Definition topo_dims : GridGraph.Dimensions := [3; 3].

Definition build_topo_node_set (dims : GridGraph.Dimensions) : node_id_map unit :=
  List.fold_left (fun acc n =>
    match n with [r; c] => map.put acc (r, c) tt | _ => acc end)
    (GridGraph.all_nodes dims) map.empty.

Definition build_topo_edge_set (dims : GridGraph.Dimensions) : node_id_map (node_id_map unit) :=
  let nodes := GridGraph.all_nodes dims in
  List.fold_left (fun acc n =>
    match n with
    | [r; c] =>
      let neighbors := List.filter (fun n2 => GridGraph.is_neighbor dims n n2) nodes in
      let neighbor_map := List.fold_left (fun m nb =>
        match nb with [r'; c'] => map.put m (r', c') tt | _ => m end)
        neighbors map.empty in
      map.put acc (r, c) neighbor_map
    | _ => acc end) nodes map.empty.

Definition topo_graph : @ComputableGraph node_id (node_id_map unit) (node_id_map (node_id_map unit)) :=
  {| nodes := build_topo_node_set topo_dims;
     edges := build_topo_edge_set topo_dims |}.

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

Eval vm_compute in compiled_family.