From Stdlib Require Import String List Bool ZArith.
From coqutil Require Import Datatypes.List Datatypes.ListSet Map.Interface Map.Properties Result Eqb Tactics.fwd.
From Datalog Require Import Datalog Interpreter.
From Datalog.Util Require Import List Map Default.
From DatalogRocq Require Import Topologies.Graph DependencyGenerator SortedListNat ComputableGraph.
From GraphSearch Require Import GraphInterface Examples.
From DatalogRocq Require Export HardwareProgram DistributedHardwareProgram.

Open Scope result_monad_scope.
Open Scope error_scope.
Open Scope bool_scope.
Import ListNotations.

Module Import RM := ResultMonadNotations.
Section DistributedDatalogToHardwareCompiler.
Context `{params : datalog_params}.
Context {node_id : node_idT} {node_id_eqb : Eqb node_id}.

Context {node_id_set : map.map node_id unit}.
Context {layout_map : map.map node_id lowered_program}.
Context {fact_locations : map.map rel_id (list node_id)}.
Context {_fwd_tbl : map.map (rel_id * fwd_from) (list fwd_to)}.

Record node_context := {
  nctries : list trie;
  last_trie_id : trie_id;
}.

(*---- var_graph as ComputableGraph over var ----*)
Context {var_node_set : map.map exprvar unit}.
Context {var_node_set_ok : map.ok var_node_set}.
Context {var_graph_impl : graph.graph exprvar} {var_graph_impl_ok : graph.ok var_graph_impl}.

(*---- node_graph as ComputableGraph over node_id ----*)
Context {node_id_set_ok : map.ok node_id_set}.
Context {node_id_graph : graph.graph node_id} {node_id_graph_ok : graph.ok node_id_graph}.

Definition node_graph := ComputableGraph node_id.

(*----The program a layout represents, and a checker that a layout distributes a given program----*)

(* the reference program a layout induces: every rule placed on any node, unioned. *)
Definition source_program (layout : layout_map) : list lowered_rule :=
  concat (values layout).

(* the layout is a valid DISTRIBUTION of program [P] when their rule SETS coincide.  ([program.interp] of a
   bare program depends only on its rule set, so the compiled network then implements [P].) *)
Definition layout_distributes_program (P : list lowered_rule) (layout : layout_map) : Prop :=
  incl (source_program layout) P /\ incl P (source_program layout).

Context {rule_eqb : Eqb rule} {rule_eqb_ok : Eqb_ok rule_eqb}.
Definition layout_distributes_programb
    (P : list lowered_rule) (layout : layout_map) : bool :=
  inclb (source_program layout) P && inclb P (source_program layout).
Lemma layout_distributes_programb_spec (P : list lowered_rule) (layout : layout_map) :
  layout_distributes_programb P layout = true -> layout_distributes_program P layout.
Proof. intros. fwd. cbv [layout_distributes_program]. auto. Qed.

(*----Stuff to keep default ordering (if desired) ----*)

Definition hyp_var_order (hyps : list lowered_fact) : list exprvar :=
  dedup (flat_map clause.vars hyps).

(*----Variable ordering----*)

Definition vg_neighbors (g : ComputableGraph exprvar) (v : exprvar) : list exprvar :=
  graph.edges g.(edges) v.

Fixpoint add_arg_edges (arg : lowered_expr) (g : ComputableGraph exprvar) (clause_vars : var_node_set) : ComputableGraph exprvar :=
  match arg with
  | expr.var v =>
    let g' := {| nodes := map.put g.(nodes) v tt;
                 edges := graph.put_edges g.(edges) v (map.keys clause_vars) |} in
    (* Add reverse edges: for each u in clause_vars, add edge u -> v *)
    map.fold (fun acc u _ =>
      {| nodes := acc.(nodes); edges := graph.put acc.(edges) u v |})
      g' clause_vars
  | expr.app _ args =>
    fold_left (fun acc arg => add_arg_edges arg acc clause_vars) args g
  end.

Fixpoint add_args_edges (args : list lowered_expr) (g : ComputableGraph exprvar) (seen : var_node_set) : ComputableGraph exprvar :=
  match args with
  | [] => g
  | arg :: rest =>
    let g' := add_arg_edges arg g seen in
    let seen' := match arg with
                 | expr.var v => map.put seen v tt
                 | expr.app _ _ => seen
                 end in
    add_args_edges rest g' seen'
  end.

Definition add_hyp_edges (hyp : lowered_fact) (g : ComputableGraph exprvar) : ComputableGraph exprvar :=
  add_args_edges hyp.(clause.args) g map.empty.

Definition empty_ComputableGraph : ComputableGraph exprvar :=
  {| nodes := map.empty; edges := graph.empty |}.

Definition create_dependency_graph (hyps : list lowered_fact) : ComputableGraph exprvar :=
  fold_left (fun acc hyp => add_hyp_edges hyp acc) hyps empty_ComputableGraph.

Definition compute_degree (g : ComputableGraph exprvar) (v : exprvar) : nat :=
  length (vg_neighbors g v).

Definition compute_degree_to_visited_set (g : ComputableGraph exprvar) (visited : var_node_set) (v : exprvar) : nat :=
  fold_left (fun acc neighbor =>
    match map.get visited neighbor with
    | Some _ => S acc
    | None => acc
    end) (vg_neighbors g v) 0.

Definition compute_max_degree_var_to_visited_set (g : ComputableGraph exprvar) (visited : var_node_set)
    : option (exprvar * nat) :=
  map.fold (fun acc v _ =>
    let degree := compute_degree_to_visited_set g visited v in
    match acc with
    | None => Some (v, degree)
    | Some (_, max_degree) => if Nat.ltb max_degree degree then Some (v, degree) else acc
    end) None g.(nodes).

Definition compute_max_degree_var (g : ComputableGraph exprvar) : option (exprvar * nat) :=
  map.fold (fun acc v _ =>
    let degree := compute_degree g v in
    match acc with
    | None => Some (v, degree)
    | Some (_, max_degree) => if Nat.ltb max_degree degree then Some (v, degree) else acc
    end) None g.(nodes).

(* If we want to enforce a specific order for tie breaks *)
Definition compute_max_degree_var_to_visited_set_ordered
    (g : ComputableGraph exprvar) (visited : var_node_set) (candidates : list exprvar)
    : option (exprvar * nat) :=
  fold_left (fun acc v =>
    (* Only consider vars still in the dep_graph *)
    match map.get g.(nodes) v with
    | None => acc
    | Some _ =>
      let degree := compute_degree_to_visited_set g visited v in
      match acc with
      | None => Some (v, degree)
      | Some (_, max_degree) =>
        if Nat.ltb max_degree degree then Some (v, degree) else acc
      end
    end) candidates None.

Definition compute_max_degree_var_ordered
    (g : ComputableGraph exprvar) (candidates : list exprvar) : option (exprvar * nat) :=
  fold_left (fun acc v =>
    match map.get g.(nodes) v with
    | None => acc
    | Some _ =>
      let degree := compute_degree g v in
      match acc with
      | None => Some (v, degree)
      | Some (_, max_degree) =>
        if Nat.ltb max_degree degree then Some (v, degree) else acc
      end
    end) candidates None.

Definition remove_edge_from_graph (g : ComputableGraph exprvar) (v1 v2 : exprvar) : ComputableGraph exprvar :=
  {| nodes := g.(nodes);
     edges := graph.remove (graph.remove g.(edges) v1 v2) v2 v1 |}.

Definition remove_edges_touching_var (g : ComputableGraph exprvar) (v : exprvar) : ComputableGraph exprvar :=
  fold_left (fun acc neighbor => remove_edge_from_graph acc v neighbor) (vg_neighbors g v) g.

Record ordering_context := {
  dep_graph : ComputableGraph exprvar;
  order : list exprvar;
  visited : var_node_set;
}.

Definition visit_node (v : exprvar) (ctx : ordering_context) : ordering_context :=
  {| dep_graph := {| nodes := map.remove ctx.(dep_graph).(nodes) v;
                     edges := (remove_edges_touching_var ctx.(dep_graph) v).(edges) |};
     order := v :: ctx.(order);
     visited := map.put ctx.(visited) v tt |}.

Definition initial_ordering_context (g : ComputableGraph exprvar) : ordering_context :=
  {| dep_graph := g; order := []; visited := map.empty |}.

Definition choose_next_var (ctx : ordering_context) : option exprvar :=
  match compute_max_degree_var_to_visited_set ctx.(dep_graph) ctx.(visited) with
  | Some (v, _) => Some v
  | None =>
    match compute_max_degree_var ctx.(dep_graph) with
    | Some (v, _) => Some v
    | None => None
    end
  end.

Definition choose_next_var_ordered (ctx : ordering_context) (candidates : list exprvar) : option exprvar :=
  match compute_max_degree_var_to_visited_set_ordered ctx.(dep_graph) ctx.(visited) candidates with
  | Some (v, _) => Some v
  | None =>
    match compute_max_degree_var_ordered ctx.(dep_graph) candidates with
    | Some (v, _) => Some v
    | None => None
    end
  end.

Fixpoint compute_variable_ordering_h (ctx : ordering_context) (fuel : nat) : ordering_context :=
  match fuel with
  | O => ctx
  | S fuel' =>
    match choose_next_var ctx with
    | Some v => compute_variable_ordering_h (visit_node v ctx) fuel'
    | None => ctx
    end
  end.

Fixpoint compute_variable_ordering_ordered_h (ctx : ordering_context)
  (candidates : list exprvar) (fuel : nat) : ordering_context :=
  match fuel with
  | O => ctx
  | S fuel' =>
    match choose_next_var_ordered ctx candidates with
    | Some v => compute_variable_ordering_ordered_h (visit_node v ctx) candidates fuel'
    | None => ctx
    end
  end.

Definition compute_variable_ordering_ordered (g : ComputableGraph exprvar) (hyps : list lowered_fact) : list exprvar :=
  let candidates := hyp_var_order hyps in
  rev
    (compute_variable_ordering_ordered_h (initial_ordering_context g)
       candidates (length candidates)).(order).

(*----Trie Allocation----*)

Definition vars_of_arg (arg : lowered_expr) : list exprvar :=
  match arg with
  | expr.var v => [v]
  | expr.app _ _ => []
  end.

Definition compute_var_order (lf : lowered_fact) : list exprvar :=
  flat_map vars_of_arg lf.(clause.args).

Context {var_idx_map : map.map exprvar nat}.

Fixpoint build_base_map (desired_order : list exprvar) (original_order : list exprvar)
    (offset : nat) (m : var_idx_map) : var_idx_map :=
  match desired_order with
  | [] => m
  | v :: vs =>
    build_base_map vs original_order
      (offset + count_occ v original_order)
      (map.put m v offset)
  end.

Fixpoint compute_perm_aux (original_order : list exprvar) (base_map occ_map : var_idx_map) : list nat :=
  match original_order with
  | [] => []
  | v :: vs =>
    let base := get_or_default base_map v in
    let occ  := get_or_default occ_map v in
    (base + occ) :: compute_perm_aux vs base_map (map.put occ_map v (occ + 1))
  end.

Definition compute_permutation (original_order desired_order : list exprvar) : permutation :=
  compute_perm_aux original_order
    (build_base_map desired_order original_order 0 map.empty) map.empty.

(*----Trie Generation----*)

Definition update_node_context_with_trie (t : trie) (ncontext : node_context) : node_context :=
  {| nctries := t :: ncontext.(nctries);
     last_trie_id := S ncontext.(last_trie_id) |}.

Definition generate_trie (hyp : lowered_fact) (rule_var_order : list exprvar)
    (existing_tries : list trie)
    (ncontext : node_context) : trie * node_context :=
  let perm := compute_permutation (compute_var_order hyp) rule_var_order in
  let rel_id := hyp.(clause.rel) in
  match find (fun t =>
    eqb t.(trel) rel_id && eqb t.(tperm) perm) existing_tries with
  | Some t => (t, ncontext)
  | None =>
    let new_trie := {| tid := ncontext.(last_trie_id); trel := rel_id; tperm := perm |} in
    (new_trie, update_node_context_with_trie new_trie ncontext)
  end.

Definition get_rule_var_index (rule_var_order : list exprvar) (v : exprvar) : Result.result nat :=
  match index_of v rule_var_order with
  | Some idx => Success idx
  | None => error:("get_rule_var_index: variable not found in rule_var_order")
  end.

Definition generate_join (tries_by_hyp : list trie) (v : exprvar) (hyps : list lowered_fact) : join :=
  let entries :=
    flat_map (fun '(clause, t, hyp) =>
                List.map (fun arg_idx => (t.(tid), nth arg_idx t.(tperm) 0, clause))
                         (indexes_of (expr.var v) hyp.(clause.args)))
             (combine3 (seq 0 (length hyps)) tries_by_hyp hyps) in
  {| tries := List.map fst3 entries;
     trie_levels := List.map snd3 entries;
     clauses := List.map thd3 entries |}.

Definition generate_query (tries : list trie) (rule_var_order : list exprvar)
    (hyps : list lowered_fact) : query :=
  List.map (fun v => generate_join tries v hyps) rule_var_order.

Definition compile_hyps (hyps : list lowered_fact) (rule_var_order : list exprvar)
    (existing_tries : list trie) (ncontext : node_context)
    : query * node_context :=
  (* [pool] is the dedup pool threaded into [generate_trie] (existing tries followed by
     the ones we generate, newest first).  [per_hyp_rev] is the trie chosen for each
     hypothesis, in reverse hypothesis order.  These must be kept distinct: [generate_join]
     pairs its trie list with [hyps] positionally, so the list handed to [generate_query]
     must be the *per-hypothesis* tries in forward order — not the reversed pool. *)
  let '(pool, per_hyp_rev, ncontext) :=
    fold_left (fun '(pool, per_hyp_rev, ncontext) hyp =>
      let (t, ncontext) := generate_trie hyp rule_var_order pool ncontext in
      (t :: pool, t :: per_hyp_rev, ncontext)) hyps (existing_tries, [], ncontext) in
  (generate_query (rev per_hyp_rev) rule_var_order hyps, ncontext).

Definition initial_node_context : node_context :=
  {| nctries := []; last_trie_id := 0 |}.

Definition compile_concl (concl : lowered_fact)
    (rule_var_order : list exprvar) : Result.result join_output :=
  var_indices <- List.all_success (List.map (fun arg =>
    match arg with
    | expr.var v => get_rule_var_index rule_var_order v
    | expr.app _ _ => Success 0
    end) concl.(clause.args)) ;;
  Success {| output_rel := concl.(clause.rel);
             output_var_indices := var_indices |}.

Definition compile_concls (concls : list lowered_fact)
    (rule_var_order : list exprvar) : Result.result (list join_output) :=
  List.all_success (List.map (fun concl => compile_concl concl rule_var_order) concls).

(* Version that tries to keep original ordering.  Bare fragment: only
   [rule.impl]s are compiled. *)
Definition compile_rule (rule : lowered_rule)
    (ncontext : node_context) : Result.result (hardware_rule * node_context) :=
  match rule with
  | rule.impl rconcls rhyps =>
    let dep_g := create_dependency_graph rhyps in
    let rule_var_order := compute_variable_ordering_ordered dep_g rhyps in  (* pass hyps for ordering *)
    let '(query, ncontext) :=
      compile_hyps rhyps rule_var_order ncontext.(nctries) ncontext in
    concls <- compile_concls rconcls rule_var_order ;;
    Success ({| hhyps := query; hconcls := concls;
                hsig := List.map (fun h => (h.(clause.rel), length h.(clause.args))) rhyps |}, ncontext)
  | _ => error:("compile_rule: aggregation/meta rules are not supported")
  end.

(*----Forwarding Tables----*)

Context {node_ftable_map : map.map node_id forwarding_table}.

Context {rels_at_node : map.map node_id (list rel_id)}.

Definition get_internal_producers_of (layout : layout_map) :=
  let internally_produced_at_node :=
    (*maps node n to set of rels which may be (internally) produced at n*)
    map.map_values (fun p => dedup (flat_map rule.concl_rels p)) layout in
  (*maps rel R to set of nodes which may (internally) produce R*)
  invert internally_produced_at_node.

Definition get_internal_consumers_of (layout : layout_map) :=
  let internally_consumed_at_node :=
    (*maps node n to set of rels which may be (internally) consumed at n*)
    map.map_values (fun p => dedup (flat_map rule.hyp_rels p)) layout in
  (*maps rel R to set of nodes which may (internally) consume R*)
  invert internally_consumed_at_node.

(*all rule_producers(R) -> all internal rule_consumers(R)*)
Definition all_rules_fed_for_relation (g : node_graph)
  (all_producers : list node_id) (internal_consumers : list node_id) :=
  forallb (fun '(p, ic) => graph.reachesb g.(edges) p ic) (list_prod all_producers internal_consumers).

Definition all_rules_fed (g : node_graph)
  (all_producers_of : fact_locations) (internal_consumers_of : fact_locations) :=
  map.forallb (fun R internal_consumers =>
                 let all_producers := get_or_default all_producers_of R in
                 all_rules_fed_for_relation g all_producers internal_consumers)
    internal_consumers_of.

(*all rule_producers(R) -> some external rule_consumer(R)*)
Definition producers_go_out_for_relation (g : node_graph)
  (all_producers : list node_id) (external_consumers : list node_id) :=
  forallb
    (fun producer => existsb (graph.reachesb g.(edges) producer) external_consumers)
    all_producers.

(*assumption: the rels that we're supposed to output are precisely the rels that we have some place to output---i.e., the rels that are keys of external_consumers.*)
Definition producers_go_out (g : node_graph)
  (all_producers_of : fact_locations) (external_consumers_of : fact_locations) :=
  map.forallb (fun R external_consumers =>
                 let all_producers := get_or_default all_producers_of R in
                 producers_go_out_for_relation g all_producers external_consumers)
    external_consumers_of.

Definition check_layout_routable (g : node_graph)
  (external_consumers_of internal_consumers_of all_producers_of : fact_locations) : Result.result unit :=
  (if all_rules_fed g all_producers_of internal_consumers_of
   then Success tt
   else error:("compile: bad layout---some producer cannot reach some internal consumer")) ;;
  (if producers_go_out g all_producers_of external_consumers_of
   then Success tt
   else error:("compile: bad layout---some producer of an output relation cannot reach any external sink")).

(*----Final Compilation----*)

Definition compile_node (node : node_id) (program : lowered_program) : Result.result node_info :=
  '(compiled_rules, ncontext) <-
    fold_left (fun acc rule =>
      '(rules, ncontext) <- acc ;;
      '(hr, ncontext) <- compile_rule rule ncontext ;;
      Success (hr :: rules, ncontext)%list
    ) program (Success ([], initial_node_context)) ;;
  Success {| nid := node;
             nprogram := rev compiled_rules;
             nforwarding := map.empty;
             ntries := rev ncontext.(nctries) |}.

Definition compile_all_nodes (llayout : layout_map) : Result.result (list node_info) :=
  List.all_success (List.map (fun '(node, program) => compile_node node program) (map.tuples llayout)).

(* Attach the compiled forwarding tables to node_infos -- now for EVERY node that forwards, not
   just the layout nodes: layout nodes keep their compiled program/tries, and any extra node that
   appears as a forwarding source (a key of [ftables], e.g. a fact-only input node) gets an empty
   program/tries with its forwarding table.  This makes the returned [ninfos] self-contained: the
   whole distributed network (programs, tries AND forwarding) can be read back off it. *)
Definition attach_forwarding_tables (ninfos : list node_info)
    (ftables : node_ftable_map) : list node_info :=
  List.map (fun ninfo =>
    {| nid := ninfo.(nid);
       nprogram := ninfo.(nprogram);
       nforwarding := get_or_default ftables ninfo.(nid);
       ntries := ninfo.(ntries) |}
  ) ninfos
  ++ List.map (fun n =>
       {| nid := n;
          nprogram := [];
          nforwarding := get_or_default ftables n ;
          ntries := [] |})
     (filter
        (fun n => negb (existsb (fun ninfo => eqb ninfo.(nid) n) ninfos))
        (map.keys ftables)).

(* every node the layout assigns to is a real graph node. *)
Definition layout_in_graphb (g : node_graph) (llayout : layout_map) : bool :=
  map.forallb (fun n _ => check_node_valid n (ComputableGraph.nodes g)) llayout.

Definition compile (layout : layout_map)
  (external_producers_of external_consumers_of : fact_locations)
  (ftables : node_ftable_map)
  (g : node_graph) : Result.result (list node_info) :=
  (if check_graph_valid g
   then Success tt
   else error:("compile: the topology graph is not valid (edges reference missing nodes)")) ;;
  (if layout_in_graphb g layout
   then Success tt
   else error:("compile: a node the layout assigns rules to is not in the topology graph")) ;;
  let internal_consumers_of := get_internal_consumers_of layout in
  let internal_producers_of := get_internal_producers_of layout in
  let all_producers_of := union_with (list_union eqb) internal_producers_of external_producers_of in
  let all_consumers_of := union_with (list_union eqb) internal_consumers_of external_consumers_of in
  check_layout_routable g external_consumers_of internal_consumers_of all_producers_of ;;
  ninfos <- compile_all_nodes layout ;;
  Success (attach_forwarding_tables ninfos ftables).
End DistributedDatalogToHardwareCompiler.

Compute compute_permutation [2;3;1;1] [1;2;3].
Compute generate_join
  [ {| tid := 0; trel := 0; tperm := [0; 1] |} ;
    {| tid := 1; trel := 0; tperm := [1; 0] |} ]
  1
  [ {| clause.rel := 0; clause.args := [expr.var 0; expr.var 1] |} ;
    {| clause.rel := 0; clause.args := [expr.var 1; expr.var 2] |} ].
