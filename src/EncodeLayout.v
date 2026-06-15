From Datalog Require Import Datalog.
From Stdlib Require Import List String Bool ZArith.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Result Eqb.
From DatalogRocq Require Import DependencyGenerator SortedListNat Topologies.Graph ComputableGraph.
From DatalogRocq Require Export HardwareProgram DistributedHardwareProgram.

Open Scope result_monad_scope.
Open Scope error_scope.
Open Scope bool_scope.
Import ListNotations.

Module Import RM := ResultMonadNotations.

Section EncodeLayout.

Context {rel : relT} {var : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
Context {var_eqb : Eqb var}.
Context {Node : Type}.
Context {node_id : Type}
        {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.

Notation destination := (@DistributedHardwareProgram.destination node_id).
Notation destination_eqb := (@DistributedHardwareProgram.destination_eqb node_id node_id_eqb).

Context {node_id_set : map.map node_id unit}.
Context {destination_set : map.map destination unit}.
Context {forwarding_table : map.map rel_id (list destination)}.
Context {rel_dependency_map : map.map rel_id (node_id_set)}.
Context {fn_id_map : map.map fn fn_id}.
Context {rel_relid_map : map.map rel rel_id}.
Context {relid_rel_map : map.map rel_id rel}.
Context {var_id_map : map.map var var_id}.
Context {layout_map : map.map node_id program}.
Context {lowered_layout_map : map.map node_id lowered_program}.

Definition fact_locations := list (rel * list node_id)%type.
Definition lowered_fact_locations := list (rel_id * list node_id)%type.

(* [node_info] now lives in [DistributedHardwareProgram] (the distributed AST); this is the
   compiler's view of it, with the topology's [node_id] and forwarding-table map fixed. *)
Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).

Context {node_info_map : map.map node_id node_info}.

Definition rule_layout := list (node_id * list rule).
Definition lowered_rule_layout := list (node_id * list lowered_rule).
Definition topology := Graph (Node := Node).

Record global_context := {
  fn_map : fn_id_map;
  rel_map : rel_relid_map;
  topo : topology;
  rel_node_consumers : rel_dependency_map;
  rel_node_producers : rel_dependency_map;
  last_fn_id : fn_id;
  last_rel_id : rel_id;
}.

Record rule_context := {
  var_map : var_id_map;
  last_var_id : var_id;
}.

Record node_context := {
  ncid : node_id;
  nctries : list trie;
  last_trie_id : trie_id;
}.

(*---- var_graph as ComputableGraph over var ----*)
Context {var_node_set : map.map var unit}.
Context {var_node_set_ok : map.ok var_node_set}.
Context {var_edge_set : map.map var var_node_set}.
Context {var_edge_set_ok : map.ok var_edge_set}.

Definition var_graph := @ComputableGraph var var_node_set var_edge_set.

(*---- node_graph as ComputableGraph over node_id ----*)
Context {node_id_set_ok : map.ok node_id_set}.
Context {node_id_edge_set : map.map node_id node_id_set}.
Context {node_id_edge_set_ok : map.ok node_id_edge_set}.

Definition node_graph := @ComputableGraph node_id node_id_set node_id_edge_set.

(*----Collecting Global Info----*)

Definition update_global_context_with_fn (f : fn) (gcontext : global_context) : global_context :=
  match map.get gcontext.(fn_map) f with
  | Some _ => gcontext
  | None =>
    {|
      fn_map := map.put gcontext.(fn_map) f gcontext.(last_fn_id);
      rel_map := gcontext.(rel_map);
      topo := gcontext.(topo);
      rel_node_consumers := gcontext.(rel_node_consumers);
      rel_node_producers := gcontext.(rel_node_producers);
      last_fn_id := S gcontext.(last_fn_id);
      last_rel_id := gcontext.(last_rel_id)
    |}
  end.

Fixpoint collect_global_names_expr (e : expr) (gcontext : global_context) : global_context :=
  match e with
  | var_expr _ => gcontext
  | fun_expr f args =>
    fold_left (fun acc arg => collect_global_names_expr arg acc) args
      (update_global_context_with_fn f gcontext)
  end.

Definition update_global_context_with_rel (r : rel) (gcontext : global_context) : global_context :=
  match map.get gcontext.(rel_map) r with
  | Some _ => gcontext
  | None =>
    {|
      fn_map := gcontext.(fn_map);
      rel_map := map.put gcontext.(rel_map) r gcontext.(last_rel_id);
      topo := gcontext.(topo);
      rel_node_consumers := gcontext.(rel_node_consumers);
      rel_node_producers := gcontext.(rel_node_producers);
      last_fn_id := gcontext.(last_fn_id);
      last_rel_id := S gcontext.(last_rel_id)
    |}
  end.

Definition collect_global_names_fact (f : clause) (gcontext : global_context) : global_context :=
  fold_left (fun acc arg => collect_global_names_expr arg acc)
    f.(clause_args) (update_global_context_with_rel f.(clause_rel) gcontext).

Definition collect_global_names_rule (r : rule) (gcontext : global_context) : global_context :=
  match r with
  | normal_rule rconcls rhyps =>
    let info := fold_left (fun acc f => collect_global_names_fact f acc) rhyps gcontext in
    fold_left (fun acc f => collect_global_names_fact f acc) rconcls info
  | _ => gcontext
  end.

Definition collect_global_names_program (p : program) (gcontext : global_context) : global_context :=
  fold_left (fun acc r => collect_global_names_rule r acc) p gcontext.

Definition collect_global_names_layout (layout : layout_map) (gcontext : global_context) : global_context :=
  map.fold (fun acc _ program => collect_global_names_program program acc) gcontext layout.

(*----Rename — now returns result to catch missing names----*)

Definition rename_fn (f : fn) (gcontext : global_context) : result fn_id :=
  match map.get gcontext.(fn_map) f with
  | Some id => Success id
  | None => error:("rename_fn: function not found in global context")
  end.

Fixpoint global_rename_expr (e : expr) (gcontext : global_context) : result lowered_expr :=
  match e with
  | var_expr v => Success (var_expr v)
  | fun_expr f args =>
    f_id <- rename_fn f gcontext ;;
    rargs <- fold_left (fun acc arg =>
      rargs <- acc ;;
      rarg <- global_rename_expr arg gcontext ;;
      Success (rarg :: rargs)%list
    ) args (Success []) ;;
    Success (fun_expr f_id (List.rev rargs))
  end.

Definition global_rename_rel (r : rel) (gcontext : global_context) : result rel_id :=
  match map.get gcontext.(rel_map) r with
  | Some id => Success id
  | None => error:("global_rename_rel: relation not found in global context")
  end.

Definition global_rename_fact (f : clause) (gcontext : global_context) : result lowered_fact :=
  r_id <- global_rename_rel f.(clause_rel) gcontext ;;
  rargs <- fold_left (fun acc arg =>
    rargs <- acc ;;
    rarg <- global_rename_expr arg gcontext ;;
    Success (rarg :: rargs)
  ) f.(clause_args) (Success []) ;;
  Success {| clause_rel := r_id; clause_args := List.rev rargs |}.

(* the compiler only handles the bare fragment: rename the concls/hyps of a
   [normal_rule] (meta/agg rules are rejected). *)
Definition global_rename_rule (r : rule) (gcontext : global_context) : result lowered_rule :=
  match r with
  | normal_rule rconcls rhyps =>
    hyps <- fold_left (fun acc f =>
      rfs <- acc ;;
      rf <- global_rename_fact f gcontext ;;
      Success (rf :: rfs)
    ) rhyps (Success []) ;;
    concls <- fold_left (fun acc f =>
      rfs <- acc ;;
      rf <- global_rename_fact f gcontext ;;
      Success (rf :: rfs)
    ) rconcls (Success []) ;;
    Success (normal_rule (List.rev concls) (List.rev hyps))
  | _ => error:("global_rename_rule: aggregation/meta rules are not supported")
  end.

Definition global_rename_program (p : program) (gcontext : global_context) : result lowered_program :=
  rs <- fold_left (fun acc r =>
    rs <- acc ;;
    lr <- global_rename_rule r gcontext ;;
    Success (lr :: rs)
  ) p (Success []) ;;
  Success (List.rev rs).

Definition global_rename_rule_layout (layout : layout_map) (gcontext : global_context)
    : result lowered_layout_map :=
  map.fold (fun acc node program =>
    llayout <- acc ;;
    lp <- global_rename_program program gcontext ;;
    Success (map.put llayout node lp)
  ) (Success map.empty) layout.

Definition global_rename_fact_locations (fact_locations : fact_locations) (gcontext : global_context) : result lowered_fact_locations :=
  fold_left (fun acc '(r, locations) =>
    acc' <- acc ;;
    r_id <- global_rename_rel r gcontext ;;
    Success ((r_id, locations) :: acc')
  ) fact_locations (Success []).

(*----Collecting Info About Layout----*)

Definition lowered_fact_contains_rel (f : lowered_fact) (r_id : rel_id) : bool :=
  Nat.eqb r_id f.(clause_rel).

Definition lowered_facts_contains_rel (facts : list lowered_fact) (r_id : rel_id) : bool :=
  List.existsb (fun f => lowered_fact_contains_rel f r_id) facts.

Definition lowered_program_produces_rel (program : lowered_program) (r_id : rel_id) : bool :=
  List.existsb (fun rule =>
    match rule with
    | normal_rule concls _ => lowered_facts_contains_rel concls r_id
    | _ => false
    end) program.

Definition lowered_program_consumes_rel (program : lowered_program) (r_id : rel_id) : bool :=
  List.existsb (fun rule =>
    match rule with
    | normal_rule _ hyps => lowered_facts_contains_rel hyps r_id
    | _ => false
    end) program.

Definition node_produces_rel (r_id : rel_id) (llayout : lowered_layout_map) (node_id : node_id) : bool :=
  match map.get llayout node_id with
  | Some program => lowered_program_produces_rel program r_id
  | None => false
  end.

Definition node_consumes_rel (r_id : rel_id) (llayout : lowered_layout_map) (node_id : node_id) : bool :=
  match map.get llayout node_id with
  | Some program => lowered_program_consumes_rel program r_id
  | None => false
  end.

Definition get_node_producers (r_id : rel_id) (llayout : lowered_layout_map) (lfact_locations : lowered_fact_locations) (gcontext : global_context) : list node_id :=
  let layout_producers :=
    List.filter (node_produces_rel r_id llayout) (map.keys llayout) in
  let fact_locations :=
    match List.find (fun '(rid, _) => Nat.eqb rid r_id) lfact_locations with
    | Some (_, locations) => locations
    | None => []
    end in
  layout_producers ++ fact_locations.

Definition get_node_consumers (r_id : rel_id) (llayout : lowered_layout_map)
    (lfact_locations : lowered_fact_locations) (gcontext : global_context) : list node_id :=
  let layout_consumers :=
    List.filter (node_consumes_rel r_id llayout) (map.keys llayout) in
  let fact_locations :=
    match List.find (fun '(rid, _) => Nat.eqb rid r_id) lfact_locations with
    | Some (_, locations) => locations
    | None => []
    end in
  layout_consumers ++ fact_locations.

Definition collect_global_dependencies_for_rel_id (r_id : rel_id) (llayout : lowered_layout_map) (lfact_producers : lowered_fact_locations) (lfact_consumers : lowered_fact_locations)
    (gcontext : global_context) : (list node_id * list node_id) :=
  (get_node_producers r_id llayout lfact_producers gcontext,
   get_node_consumers r_id llayout lfact_consumers gcontext).

Definition add_producer_to_context (r_id : rel_id) (producer : node_id)
    (gcontext : global_context) : global_context :=
  let rel_node_producers :=
    match map.get gcontext.(rel_node_producers) r_id with
    | Some producers => map.put gcontext.(rel_node_producers) r_id (map.put producers producer tt)
    | None => map.put gcontext.(rel_node_producers) r_id (map.put map.empty producer tt)
    end in
  {|
    fn_map := gcontext.(fn_map);
    rel_map := gcontext.(rel_map);
    topo := gcontext.(topo);
    rel_node_consumers := gcontext.(rel_node_consumers);
    rel_node_producers := rel_node_producers;
    last_fn_id := gcontext.(last_fn_id);
    last_rel_id := gcontext.(last_rel_id)
  |}.

Definition add_producers_to_context (r_id : rel_id) (producers : list node_id)
    (gcontext : global_context) : global_context :=
  fold_left (fun acc p => add_producer_to_context r_id p acc) producers gcontext.

Definition add_consumer_to_context (r_id : rel_id) (consumer : node_id)
    (gcontext : global_context) : global_context :=
  let rel_node_consumers :=
    match map.get gcontext.(rel_node_consumers) r_id with
    | Some consumers => map.put gcontext.(rel_node_consumers) r_id (map.put consumers consumer tt)
    | None => map.put gcontext.(rel_node_consumers) r_id (map.put map.empty consumer tt)
    end in
  {|
    fn_map := gcontext.(fn_map);
    rel_map := gcontext.(rel_map);
    topo := gcontext.(topo);
    rel_node_consumers := rel_node_consumers;
    rel_node_producers := gcontext.(rel_node_producers);
    last_fn_id := gcontext.(last_fn_id);
    last_rel_id := gcontext.(last_rel_id)
  |}.

Definition add_consumers_to_context (r_id : rel_id) (consumers : list node_id)
    (gcontext : global_context) : global_context :=
  fold_left (fun acc c => add_consumer_to_context r_id c acc) consumers gcontext.

Definition get_rel_ids (gcontext : global_context) : list rel_id :=
  map.fold (fun acc _ rel_id => rel_id :: acc) [] gcontext.(rel_map).

Definition collect_global_dependencies (llayout : lowered_layout_map) (lfact_producers : lowered_fact_locations) (lfact_consumers : lowered_fact_locations)
    (gcontext : global_context) : global_context :=
  fold_left (fun acc rel_id =>
    let (producers, consumers) :=
      collect_global_dependencies_for_rel_id rel_id llayout lfact_producers lfact_consumers gcontext in
    add_consumers_to_context rel_id consumers
      (add_producers_to_context rel_id producers acc)
  ) (get_rel_ids gcontext) gcontext.

(*----Stuff to keep default ordering (if desired) ----*)

(* Collect vars in order of first appearance in hypotheses *)
Fixpoint collect_vars_expr (e : lowered_expr) : list var :=
  match e with
  | var_expr v => [v]
  | fun_expr _ args => List.flat_map collect_vars_expr args
  end.

Definition collect_vars_fact (f : lowered_fact) : list var :=
  List.flat_map collect_vars_expr f.(clause_args).

Definition collect_vars_hyps (hyps : list lowered_fact) : list var :=
  List.flat_map collect_vars_fact hyps.

(* Deduplicate keeping first occurrence *)
Fixpoint dedup (seen : var_node_set) (l : list var) : list var :=
  match l with
  | [] => []
  | v :: rest =>
    match map.get seen v with
    | Some _ => dedup seen rest
    | None => v :: dedup (map.put seen v tt) rest
    end
  end.

Definition hyp_var_order (hyps : list lowered_fact) : list var :=
  dedup map.empty (collect_vars_hyps hyps).

(*----Variable ordering----*)

Context {var_set : map.map var unit}.

Definition vg_neighbors (g : var_graph) (v : var) : var_node_set :=
  match map.get g.(edges) v with
  | Some ns => ns
  | None => map.empty
  end.

Fixpoint add_arg_edges (arg : lowered_expr) (g : var_graph) (clause_vars : var_node_set) : var_graph :=
  match arg with
  | var_expr v =>
    let new_neighbors := map.putmany (vg_neighbors g v) clause_vars in
    let g' := {| nodes := map.put g.(nodes) v tt;
                 edges := map.put g.(edges) v new_neighbors |} in
    (* Add reverse edges: for each u in clause_vars, add edge u -> v *)
    map.fold (fun acc u _ =>
      {| nodes := acc.(nodes);
         edges := map.put acc.(edges) u (map.put (vg_neighbors acc u) v tt) |})
      g' clause_vars
  | fun_expr _ args =>
    fold_left (fun acc arg => add_arg_edges arg acc clause_vars) args g
  end.

Fixpoint add_args_edges (args : list lowered_expr) (g : var_graph) (seen : var_node_set) : var_graph :=
  match args with
  | [] => g
  | arg :: rest =>
    let g' := add_arg_edges arg g seen in
    let seen' := match arg with
                 | var_expr v => map.put seen v tt
                 | fun_expr _ _ => seen
                 end in
    add_args_edges rest g' seen'
  end.

Definition add_hyp_edges (hyp : lowered_fact) (g : var_graph) : var_graph :=
  add_args_edges hyp.(clause_args) g map.empty.

Definition empty_var_graph : var_graph :=
  {| nodes := map.empty; edges := map.empty |}.

Definition create_dependency_graph (hyps : list lowered_fact) : var_graph :=
  fold_left (fun acc hyp => add_hyp_edges hyp acc) hyps empty_var_graph.

Definition compute_degree (g : var_graph) (v : var) : nat :=
  map.fold (fun acc _ _ => S acc) 0 (vg_neighbors g v).

Definition compute_degree_to_visited_set (g : var_graph) (visited : var_node_set) (v : var) : nat :=
  map.fold (fun acc neighbor _ =>
    match map.get visited neighbor with
    | Some _ => S acc
    | None => acc
    end) 0 (vg_neighbors g v).

Definition compute_max_degree_var_to_visited_set (g : var_graph) (visited : var_node_set)
    : option (var * nat) :=
  map.fold (fun acc v _ =>
    let degree := compute_degree_to_visited_set g visited v in
    match acc with
    | None => Some (v, degree)
    | Some (_, max_degree) => if Nat.ltb max_degree degree then Some (v, degree) else acc
    end) None g.(nodes).

Definition compute_max_degree_var (g : var_graph) : option (var * nat) :=
  map.fold (fun acc v _ =>
    let degree := compute_degree g v in
    match acc with
    | None => Some (v, degree)
    | Some (_, max_degree) => if Nat.ltb max_degree degree then Some (v, degree) else acc
    end) None g.(nodes).

(* If we want to enforce a specific order for tie breaks *)
Definition compute_max_degree_var_to_visited_set_ordered
    (g : var_graph) (visited : var_node_set) (candidates : list var)
    : option (var * nat) :=
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
    (g : var_graph) (candidates : list var) : option (var * nat) :=
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

Definition remove_edge_from_graph (g : var_graph) (v1 v2 : var) : var_graph :=
  {| nodes := g.(nodes);
     edges := map.put (map.put g.(edges) v1 (map.remove (vg_neighbors g v1) v2))
                                           v2 (map.remove (vg_neighbors g v2) v1) |}.

Definition remove_edges_touching_var (g : var_graph) (v : var) : var_graph :=
  map.fold (fun acc neighbor _ => remove_edge_from_graph acc v neighbor) g (vg_neighbors g v).

Record ordering_context := {
  dep_graph : var_graph;
  order : list var;
  visited : var_node_set;
}.

Definition visit_node (v : var) (ctx : ordering_context) : ordering_context :=
  {| dep_graph := {| nodes := map.remove ctx.(dep_graph).(nodes) v;
                     edges := (remove_edges_touching_var ctx.(dep_graph) v).(edges) |};
     order := v :: ctx.(order);
     visited := map.put ctx.(visited) v tt |}.

Definition initial_ordering_context (g : var_graph) : ordering_context :=
  {| dep_graph := g; order := []; visited := map.empty |}.

Definition choose_next_var (ctx : ordering_context) : option var :=
  match compute_max_degree_var_to_visited_set ctx.(dep_graph) ctx.(visited) with
  | Some (v, _) => Some v
  | None =>
    match compute_max_degree_var ctx.(dep_graph) with
    | Some (v, _) => Some v
    | None => None
    end
  end.

Definition choose_next_var_ordered (ctx : ordering_context) (candidates : list var) : option var :=
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
  (candidates : list var) (fuel : nat) : ordering_context :=
  match fuel with
  | O => ctx
  | S fuel' =>
    match choose_next_var_ordered ctx candidates with
    | Some v => compute_variable_ordering_ordered_h (visit_node v ctx) candidates fuel'
    | None => ctx
    end
  end.

Definition compute_variable_ordering (g : var_graph) : list var :=
  List.rev
    (compute_variable_ordering_h (initial_ordering_context g)
       (List.length (map.keys g.(nodes)))).(order).

Definition compute_variable_ordering_ordered (g : var_graph) (hyps : list lowered_fact) : list var :=
  let candidates := hyp_var_order hyps in
  List.rev
    (compute_variable_ordering_ordered_h (initial_ordering_context g)
       candidates (List.length candidates)).(order).

(*----Trie Allocation----*)

Definition vars_of_arg (arg : lowered_expr) : list var :=
  match arg with
  | var_expr v => [v]
  | fun_expr _ _ => []
  end.

Definition compute_var_order (lf : lowered_fact) : list var :=
  List.flat_map vars_of_arg lf.(clause_args).

Context {var_idx_map : map.map var nat}.

Fixpoint index_of_var_aux (v : var) (vars : list var) (i : nat) : option nat :=
  match vars with
  | [] => None
  | v' :: rest => if var_eqb v v' then Some i else index_of_var_aux v rest (S i)
  end.

Definition index_of_var (v : var) (vars : list var) : option nat :=
  index_of_var_aux v vars 0.

Fixpoint count_occ (v : var) (l : list var) : nat :=
  match l with
  | [] => 0
  | x :: xs => (if var_eqb x v then 1 else 0) + count_occ v xs
  end.

Fixpoint build_base_map (desired_order : list var) (original_order : list var)
    (offset : nat) (m : var_idx_map) : var_idx_map :=
  match desired_order with
  | [] => m
  | v :: vs =>
    build_base_map vs original_order
      (offset + count_occ v original_order)
      (map.put m v offset)
  end.

Fixpoint compute_perm_aux (original_order : list var) (base_map occ_map : var_idx_map) : list nat :=
  match original_order with
  | [] => []
  | v :: vs =>
    let base := match map.get base_map v with Some n => n | None => 0 end in
    let occ  := match map.get occ_map  v with Some n => n | None => 0 end in
    (base + occ) :: compute_perm_aux vs base_map (map.put occ_map v (occ + 1))
  end.

Definition compute_permutation (original_order desired_order : list var) : permutation :=
  compute_perm_aux original_order
    (build_base_map desired_order original_order 0 map.empty) map.empty.

(*----Trie Generation----*)

Definition permutation_eqb (p1 p2 : permutation) : bool :=
  if Nat.eqb (List.length p1) (List.length p2) then
    List.forallb (fun '(x, y) => Nat.eqb x y) (List.combine p1 p2)
  else false.

Definition update_node_context_with_trie (t : trie) (ncontext : node_context) : node_context :=
  {| ncid := ncontext.(ncid);
     nctries := t :: ncontext.(nctries);
     last_trie_id := S ncontext.(last_trie_id) |}.

Definition generate_trie (hyp : lowered_fact) (rule_var_order : list var)
    (existing_tries : list trie) (gcontext : global_context)
    (ncontext : node_context) : trie * node_context :=
  let perm := compute_permutation (compute_var_order hyp) rule_var_order in
  let rel_id := hyp.(clause_rel) in
  match List.find (fun t =>
    Nat.eqb t.(trel) rel_id && permutation_eqb t.(tperm) perm) existing_tries with
  | Some t => (t, ncontext)
  | None =>
    let new_trie := {| tid := ncontext.(last_trie_id); trel := rel_id; tperm := perm |} in
    (new_trie, update_node_context_with_trie new_trie ncontext)
  end.

Definition get_rule_var_index (rule_var_order : list var) (v : var) : result nat :=
  match index_of_var v rule_var_order with
  | Some idx => Success idx
  | None => error:("get_rule_var_index: variable not found in rule_var_order")
  end.

Fixpoint get_hyp_arg_indices (args : list lowered_expr) (v : var) (i : nat) : list nat :=
  match args with
  | [] => []
  | arg :: rest =>
    let acc := get_hyp_arg_indices rest v (S i) in
    match arg with
    | var_expr v' => if var_eqb v v' then i :: acc else acc
    | fun_expr _ _ => acc
    end
  end.

Definition generate_join (tries_by_hyp : list trie) (v : var) (hyps : list lowered_fact) : join :=
  let '(ts, levels, cs, _) :=
    fold_left (fun acc pair =>
      let '(ts, levels, cs, clause) := acc in
      let '(t, hyp) := pair in
      let '(ts', levels', cs') :=
        fold_left (fun inner_acc arg_idx =>
          let '(ts', levels', cs') := inner_acc in
          (t.(tid) :: ts', List.nth arg_idx t.(tperm) 0 :: levels', clause :: cs'))
          (get_hyp_arg_indices hyp.(clause_args) v 0) (ts, levels, cs)
      in
      (ts', levels', cs', S clause))
      (List.combine tries_by_hyp hyps) ([], [], [], 0)
  in
  {| tries := List.rev ts;
     trie_levels := List.rev levels;
     clauses := List.rev cs |}.

Definition generate_query (tries : list trie) (rule_var_order : list var)
    (hyps : list lowered_fact) : query :=
  List.map (fun v => generate_join tries v hyps) rule_var_order.

Definition compile_hyps (hyps : list lowered_fact) (rule_var_order : list var)
    (existing_tries : list trie) (gcontext : global_context) (ncontext : node_context)
    : query * node_context :=
  (* [pool] is the dedup pool threaded into [generate_trie] (existing tries followed by
     the ones we generate, newest first).  [per_hyp_rev] is the trie chosen for each
     hypothesis, in reverse hypothesis order.  These must be kept distinct: [generate_join]
     pairs its trie list with [hyps] positionally, so the list handed to [generate_query]
     must be the *per-hypothesis* tries in forward order — not the reversed pool. *)
  let '(pool, per_hyp_rev, ncontext) :=
    fold_left (fun '(pool, per_hyp_rev, ncontext) hyp =>
      let (t, ncontext) := generate_trie hyp rule_var_order pool gcontext ncontext in
      (t :: pool, t :: per_hyp_rev, ncontext)) hyps (existing_tries, [], ncontext) in
  (generate_query (List.rev per_hyp_rev) rule_var_order hyps, ncontext).

Definition initial_node_context (nid : node_id) : node_context :=
  {| ncid := nid; nctries := []; last_trie_id := 0 |}.

Definition compile_concl (concl : lowered_fact) (gcontext : global_context)
    (rule_var_order : list var) : result join_output :=
  var_indices <- fold_left (fun acc arg =>
    idxs <- acc ;;
    match arg with
    | var_expr v =>
      idx <- get_rule_var_index rule_var_order v ;;
      Success (idx :: idxs)
    | fun_expr _ _ => Success (0 :: idxs)
    end
  ) concl.(clause_args) (Success []) ;;
  Success {| output_rel := concl.(clause_rel);
             output_var_indices := List.rev var_indices |}.

Definition compile_concls (concls : list lowered_fact) (gcontext : global_context)
    (rule_var_order : list var) : result (list join_output) :=
  jos <- fold_left (fun acc concl =>
    jos <- acc ;;
    jo <- compile_concl concl gcontext rule_var_order ;;
    Success (jo :: jos)
  ) concls (Success []) ;;
  Success (List.rev jos).

(* Version that tries to keep original ordering.  Bare fragment: only
   [normal_rule]s are compiled. *)
Definition compile_rule (rule : lowered_rule) (gcontext : global_context)
    (ncontext : node_context) : result (hardware_rule * node_context) :=
  match rule with
  | normal_rule rconcls rhyps =>
    let dep_g := create_dependency_graph rhyps in
    let rule_var_order := compute_variable_ordering_ordered dep_g rhyps in  (* pass hyps for ordering *)
    let '(query, ncontext) :=
      compile_hyps rhyps rule_var_order ncontext.(nctries) gcontext ncontext in
    concls <- compile_concls rconcls gcontext rule_var_order ;;
    Success ({| hhyps := query; hconcls := concls;
                hsig := List.map (fun h => (h.(clause_rel), List.length h.(clause_args))) rhyps |}, ncontext)
  | _ => error:("compile_rule: aggregation/meta rules are not supported")
  end.

(*----Forwarding Tables----*)

Context {node_ftable_map : map.map node_id forwarding_table}.

Definition get_node_ftable (node : node_id) (ftables : node_ftable_map) : forwarding_table :=
  match map.get ftables node with
  | Some ft => ft
  | None => map.empty
  end.

Definition add_dest_if_absent (d : destination) (ds : list destination) : list destination :=
  if List.existsb (destination_eqb d) ds then ds else d :: ds.

Definition add_trie_dest_to_forwarding_table (node : node_id) (rel : rel_id)
    (ftables : node_ftable_map) (ninfos : list node_info) : node_ftable_map :=
  let ft := get_node_ftable node ftables in
  let matching_tries :=
    match List.find (fun n => node_id_eqb n.(nid) node) ninfos with
    | None => []
    | Some ninfo => List.filter (fun t => Nat.eqb t.(trel) rel) ninfo.(ntries)
    end in
  let existing := match map.get ft rel with Some ds => ds | None => [] end in
  let updated_ft :=
    map.put ft rel
      (fold_left (fun acc t => add_dest_if_absent (DestTrie t.(tid)) acc)
        matching_tries existing) in
  map.put ftables node updated_ft.

(* TODO later maybe do edges by which node it connects to instead of direction? *)
Fixpoint add_path_to_forwarding_table (rel : rel_id) (path : list node_id)
    (ftables : node_ftable_map) (ninfos : list node_info) : node_ftable_map :=
  match path with
  | [] => ftables
  | [node] => add_trie_dest_to_forwarding_table node rel ftables ninfos
  | node :: ((next :: _) as rest) =>
    let ft := get_node_ftable node ftables in
    let existing := match map.get ft rel with
                    | Some ds => ds | None => [] end in
    let ft' := map.put ft rel (add_dest_if_absent (DestEdge next) existing) in
    add_path_to_forwarding_table rel rest (map.put ftables node ft') ninfos
  end.

Definition update_forwarding_table_for_rel (rel : rel_id) (gcontext : global_context)
    (ninfos : list node_info) (ftables : node_ftable_map) (fuel : nat)
    (g : node_graph) : node_ftable_map :=
  let producers :=
    match map.get gcontext.(rel_node_producers) rel with
    | Some ps => ps
    | None => map.empty
    end in
  let consumers :=
    match map.get gcontext.(rel_node_consumers) rel with
    | Some cs => cs
    | None => map.empty
    end in
  map.fold (fun ftables producer _ =>
    map.fold (fun ftables consumer _ =>
      if node_id_eqb producer consumer then
        add_trie_dest_to_forwarding_table consumer rel ftables ninfos
      else
        match get_path (node_eqb := node_id_eqb)
                       (node_set := node_id_set)
                       (edge_set := node_id_edge_set)
                       g producer consumer fuel with
        | None => ftables
        | Some path => add_path_to_forwarding_table rel path ftables ninfos
        end
    ) ftables consumers
  ) ftables producers.

Definition generate_forwarding_table (gcontext : global_context) (ninfos : list node_info)
    (g : node_graph) (fuel : nat) : node_ftable_map :=
  fold_left (fun ftables rel =>
    update_forwarding_table_for_rel rel gcontext ninfos ftables fuel g
  ) (get_rel_ids gcontext) map.empty.

(*----Final Compilation----*)

Definition initial_global_context : global_context :=
  {| fn_map := map.empty;
     rel_map := map.empty;
     topo := {| Graph.nodes := fun _ => False; Graph.edge := fun _ _ => False |};
     rel_node_consumers := map.empty;
     rel_node_producers := map.empty;
     last_fn_id := 0;
     last_rel_id := 0 |}.

Definition compile_node (node : node_id) (program : lowered_program)
    (gcontext : global_context) : result node_info :=
  '(compiled_rules, ncontext) <-
    fold_left (fun acc rule =>
      '(rules, ncontext) <- acc ;;
      '(hr, ncontext) <- compile_rule rule gcontext ncontext ;;
      Success (hr :: rules, ncontext)%list
    ) program (Success ([], initial_node_context node)) ;;
  Success {| nid := node;
             nprogram := List.rev compiled_rules;
             nforwarding := map.empty;
             ntries := List.rev ncontext.(nctries) |}.

Definition compile_all_nodes (llayout : lowered_layout_map)
    (gcontext : global_context) : result (list node_info) :=
  ninfos <- map.fold (fun acc node program =>
    ninfos <- acc ;;
    ninfo <- compile_node node program gcontext ;;
    Success (ninfo :: ninfos)
  ) (Success []) llayout ;;
  Success (ninfos).

Definition attach_forwarding_tables (ninfos : list node_info)
    (ftables : node_ftable_map) : list node_info :=
  List.map (fun ninfo =>
    let ft := match map.get ftables ninfo.(nid) with
              | Some ft => ft | None => map.empty end in
    {| nid := ninfo.(nid);
       nprogram := ninfo.(nprogram);
       nforwarding := ft;
       ntries := ninfo.(ntries) |}
  ) ninfos.

(* The renamed (numeric-id) layout that [compile] works on internally, exposed as a standalone
   computable definition so correctness statements can name it (and run the bareness / node-validity
   checks on it).  When [compile] succeeds these are exactly the [llayout]/[gcontext] it uses. *)
Definition compile_renamed_layout (layout : layout_map) : lowered_layout_map :=
  match global_rename_rule_layout layout (collect_global_names_layout layout initial_global_context) with
  | Success ll => ll
  | Failure _ => map.empty
  end.

Definition compile_global_context (layout : layout_map)
    (fact_producers fact_consumers : fact_locations) : global_context :=
  let gcontext := collect_global_names_layout layout initial_global_context in
  match global_rename_fact_locations fact_producers gcontext with
  | Success lfp =>
      match global_rename_fact_locations fact_consumers gcontext with
      | Success lfc => collect_global_dependencies (compile_renamed_layout layout) lfp lfc gcontext
      | Failure _ => gcontext
      end
  | Failure _ => gcontext
  end.

Definition compile (layout : layout_map) (fact_producers : fact_locations) (fact_consumers : fact_locations) (g : node_graph) (fuel : nat)
    : result (list node_info) :=
  let gcontext := collect_global_names_layout layout initial_global_context in
  llayout <- global_rename_rule_layout layout gcontext ;;
  lfact_producers <- global_rename_fact_locations fact_producers gcontext ;;
  lfact_consumers <- global_rename_fact_locations fact_consumers gcontext ;;
  let gcontext := collect_global_dependencies llayout lfact_producers lfact_consumers gcontext in
  ninfos <- compile_all_nodes llayout gcontext ;;
  let ftables := generate_forwarding_table gcontext ninfos g fuel in
  Success (attach_forwarding_tables ninfos ftables).

End EncodeLayout.

Existing Instance SortedListNat.map.
From coqutil Require Import SortedListString.
Existing Instance SortedListString.map.

Compute compute_permutation (var := nat) (var_eqb := Nat.eqb) [2;3;1;1] [1;2;3].
Compute generate_join
  (var := nat) (var_eqb := Nat.eqb)
  [ {| tid := 0; trel := 0; tperm := [0; 1] |} ;
    {| tid := 1; trel := 0; tperm := [1; 0] |} ]
  1
  [ {| clause_rel := 0; clause_args := [var_expr 0; var_expr 1] |} ;
    {| clause_rel := 0; clause_args := [var_expr 1; var_expr 2] |} ].