From Stdlib Require Import String List Bool ZArith.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Result Eqb.
From Datalog Require Import Datalog List Map.
From DatalogRocq Require Import DependencyGenerator SortedListNat ComputableGraph.
From DatalogRocq Require Export HardwareProgram DistributedHardwareProgram.

Open Scope result_monad_scope.
Open Scope error_scope.
Open Scope bool_scope.
Import ListNotations.

Module Import RM := ResultMonadNotations.
Section DistributedDatalogToHardwareCompiler.

Context {rel : relT} {var : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
Context {var_eqb : Eqb var}.
Context {node_id : Type} {node_id_eqb : Eqb node_id}.

Notation destination := (@DistributedHardwareProgram.destination node_id).
Notation destination_eqb := (@DistributedHardwareProgram.destination_eqb node_id node_id_eqb).

Context {node_id_set : map.map node_id unit}.
Context {destination_set : map.map destination unit}.
Context {forwarding_table : map.map rel_id (list destination)}.
Context {rel_relid_map : map.map rel rel_id}.
Context {relid_rel_map : map.map rel_id rel}.
Context {var_id_map : map.map var var_id}.
Context {layout_map : map.map node_id program}.
Context {lowered_layout_map : map.map node_id lowered_program}.
Context {fact_locations : map.map rel (list node_id)}.
Context {lowered_fact_locations : map.map rel_id (list node_id)}.

(* [node_info] now lives in [DistributedHardwareProgram] (the distributed AST); this is the
   compiler's view of it, with the topology's [node_id] and forwarding-table map fixed. *)
Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).

Context {node_info_map : map.map node_id node_info}.

Record global_context := {
  rel_map : rel_relid_map;
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

Definition update_global_context_with_rel (r : rel) (gcontext : global_context) : global_context :=
  match map.get gcontext.(rel_map) r with
  | Some _ => gcontext
  | None =>
    {|
      rel_map := map.put gcontext.(rel_map) r gcontext.(last_rel_id);
      last_rel_id := S gcontext.(last_rel_id)
    |}
  end.

Definition collect_global_names_fact (f : clause) (gcontext : global_context) : global_context :=
  update_global_context_with_rel f.(clause_rel) gcontext.

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
Context (fn_to_id : fn -> fn_id).

Fixpoint global_rename_expr (e : expr) : lowered_expr :=
  match e with
  | var_expr v => var_expr v
  | fun_expr f args => fun_expr (fn_to_id f) (List.map global_rename_expr args)
  end.

Definition global_rename_rel (r : rel) (gcontext : global_context) : result rel_id :=
  match map.get gcontext.(rel_map) r with
  | Some id => Success id
  | None => error:("global_rename_rel: relation not found in global context")
  end.

Definition global_rename_fact (f : clause) (gcontext : global_context) : result lowered_fact :=
  r_id <- global_rename_rel f.(clause_rel) gcontext ;;
  let rargs := List.map global_rename_expr f.(clause_args) in
  Success {| clause_rel := r_id; clause_args := rargs |}.

(* the compiler only handles the bare fragment: rename the concls/hyps of a
   [normal_rule] (meta/agg rules are rejected). *)
Definition global_rename_rule (r : rule) (gcontext : global_context) : result lowered_rule :=
  match r with
  | normal_rule rconcls rhyps =>
    hyps <- List.all_success (List.map (fun f => global_rename_fact f gcontext) rhyps) ;;
    concls <- List.all_success (List.map (fun f => global_rename_fact f gcontext) rconcls) ;;
    Success (normal_rule concls hyps)
  | _ => error:("global_rename_rule: aggregation/meta rules are not supported")
  end.

Definition global_rename_program (p : program) (gcontext : global_context) : result lowered_program :=
  List.all_success (List.map (fun r => global_rename_rule r gcontext) p).

Definition global_rename_rule_layout (layout : layout_map) (gcontext : global_context)
    : result lowered_layout_map :=
  map.try_map_values (fun program => global_rename_program program gcontext) layout.

Definition global_rename_fact_locations (fact_locations : fact_locations) (gcontext : global_context) : result lowered_fact_locations :=
  map.fold (fun acc r locations =>
    acc' <- acc ;;
    r_id <- global_rename_rel r gcontext ;;
    Success (map.put acc' r_id locations)
  ) (Success map.empty) fact_locations.

(*----The program a layout represents, and a checker that a layout distributes a given program----*)

(* the reference program a layout induces: every rule placed on any node, unioned. *)
Definition source_program (layout : layout_map) : program :=
  concat (values layout).

(* the layout is a valid DISTRIBUTION of program [P] when their rule SETS coincide.  ([prog_impl] of a
   bare program depends only on its rule set, so the compiled network then implements [P].) *)
Definition layout_distributes_program (P : program) (layout : layout_map) : Prop :=
  incl (source_program layout) P /\ incl P (source_program layout).

Context {rule_eqb : Eqb rule} {rule_eqb_ok : Eqb_ok rule_eqb}.
Definition layout_distributes_programb
    (P : program) (layout : layout_map) : bool :=
  inclb (source_program layout) P && inclb P (source_program layout).
Lemma layout_distributes_programb_spec (P : program) (layout : layout_map) :
  layout_distributes_programb P layout = true -> layout_distributes_program P layout.
Proof.
  unfold layout_distributes_programb, layout_distributes_program. intros H.
  apply andb_true_iff in H. destruct H as [H1 H2].
  split; [exact (proj1 (inclb_incl _ _) H1) | exact (proj1 (inclb_incl _ _) H2)].
Qed.

(*----Collecting Info About Layout----*)

Definition lowered_fact_contains_rel (f : lowered_fact) (r_id : rel_id) : bool :=
  eqb r_id f.(clause_rel).

Definition lowered_facts_contains_rel (facts : list lowered_fact) (r_id : rel_id) : bool :=
  existsb (fun f => lowered_fact_contains_rel f r_id) facts.

Definition get_rel_ids (gcontext : global_context) : list rel_id :=
  values gcontext.(rel_map).

(*----Stuff to keep default ordering (if desired) ----*)

Definition hyp_var_order (hyps : list lowered_fact) : list var :=
  dedup (flat_map vars_of_clause hyps).

(*----Variable ordering----*)

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

Definition compute_variable_ordering_ordered (g : var_graph) (hyps : list lowered_fact) : list var :=
  let candidates := hyp_var_order hyps in
  rev
    (compute_variable_ordering_ordered_h (initial_ordering_context g)
       candidates (length candidates)).(order).

(*----Trie Allocation----*)

Definition vars_of_arg (arg : lowered_expr) : list var :=
  match arg with
  | var_expr v => [v]
  | fun_expr _ _ => []
  end.

Definition compute_var_order (lf : lowered_fact) : list var :=
  flat_map vars_of_arg lf.(clause_args).

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
  if eqb (length p1) (length p2) then
    forallb (fun '(x, y) => Nat.eqb x y) (combine p1 p2)
  else false.

Definition update_node_context_with_trie (t : trie) (ncontext : node_context) : node_context :=
  {| ncid := ncontext.(ncid);
     nctries := t :: ncontext.(nctries);
     last_trie_id := S ncontext.(last_trie_id) |}.

Definition generate_trie (hyp : lowered_fact) (rule_var_order : list var)
    (existing_tries : list trie)
    (ncontext : node_context) : trie * node_context :=
  let perm := compute_permutation (compute_var_order hyp) rule_var_order in
  let rel_id := hyp.(clause_rel) in
  match find (fun t =>
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
          (t.(tid) :: ts', nth arg_idx t.(tperm) 0 :: levels', clause :: cs'))
          (get_hyp_arg_indices hyp.(clause_args) v 0) (ts, levels, cs)
      in
      (ts', levels', cs', S clause))
      (combine tries_by_hyp hyps) ([], [], [], 0)
  in
  {| tries := rev ts;
     trie_levels := rev levels;
     clauses := rev cs |}.

Definition generate_query (tries : list trie) (rule_var_order : list var)
    (hyps : list lowered_fact) : query :=
  List.map (fun v => generate_join tries v hyps) rule_var_order.

Definition compile_hyps (hyps : list lowered_fact) (rule_var_order : list var)
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

Definition initial_node_context (nid : node_id) : node_context :=
  {| ncid := nid; nctries := []; last_trie_id := 0 |}.

Definition compile_concl (concl : lowered_fact)
    (rule_var_order : list var) : result join_output :=
  var_indices <- List.all_success (List.map (fun arg =>
    match arg with
    | var_expr v => get_rule_var_index rule_var_order v
    | fun_expr _ _ => Success 0
    end) concl.(clause_args)) ;;
  Success {| output_rel := concl.(clause_rel);
             output_var_indices := var_indices |}.

Definition compile_concls (concls : list lowered_fact)
    (rule_var_order : list var) : result (list join_output) :=
  List.all_success (List.map (fun concl => compile_concl concl rule_var_order) concls).

(* Version that tries to keep original ordering.  Bare fragment: only
   [normal_rule]s are compiled. *)
Definition compile_rule (rule : lowered_rule)
    (ncontext : node_context) : result (hardware_rule * node_context) :=
  match rule with
  | normal_rule rconcls rhyps =>
    let dep_g := create_dependency_graph rhyps in
    let rule_var_order := compute_variable_ordering_ordered dep_g rhyps in  (* pass hyps for ordering *)
    let '(query, ncontext) :=
      compile_hyps rhyps rule_var_order ncontext.(nctries) ncontext in
    concls <- compile_concls rconcls rule_var_order ;;
    Success ({| hhyps := query; hconcls := concls;
                hsig := List.map (fun h => (h.(clause_rel), length h.(clause_args))) rhyps |}, ncontext)
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
  if existsb (destination_eqb d) ds then ds else d :: ds.

Definition add_trie_dest_to_forwarding_table (node : node_id) (rel : rel_id)
    (ftables : node_ftable_map) (ninfos : list node_info) : node_ftable_map :=
  let ft := get_node_ftable node ftables in
  let matching_tries :=
    match find (fun n => eqb n.(nid) node) ninfos with
    | None => []
    | Some ninfo => filter (fun t => Nat.eqb t.(trel) rel) ninfo.(ntries)
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

Definition update_forwarding_table_for_rel (rel : rel_id)
    (ninfos : list node_info) (ftables : node_ftable_map)
    (g : node_graph) lfc lfp : node_ftable_map :=
  let producers := get_default [] lfp rel in
  let consumers := get_default [] lfc rel in
  fold_left (fun ftables producer =>
    fold_left (fun ftables consumer =>
      if eqb producer consumer then
        add_trie_dest_to_forwarding_table consumer rel ftables ninfos
      else
        match get_path g producer consumer with
        | None => ftables
        | Some path => add_path_to_forwarding_table rel path ftables ninfos
        end
    ) consumers ftables
  ) producers ftables .

Definition generate_forwarding_table (gcontext : global_context) (ninfos : list node_info)
    (g : node_graph) lfc lfp : node_ftable_map :=
  fold_left (fun ftables rel =>
    update_forwarding_table_for_rel rel ninfos ftables g lfc lfp
    ) (get_rel_ids gcontext) map.empty.

(* FORWARDING-COMPLETENESS gate: for every node [np] that concludes relation [R], [R] is a
   registered relation and [np] is a recorded producer; and for every node [nc] that hypothesizes
   [R], [nc] is a recorded consumer AND the compiler's search [get_path] found a route [np ~> nc]
   (or [np = nc]).  When this is [false] the compiler cannot certify that every produced fact
   reaches every consumer. *)
Definition routes_validb (gcontext : global_context) (g : node_graph)
    (llayout : lowered_layout_map) (lfc lfp : lowered_fact_locations) : bool :=
  forallb (fun np =>
    forallb (fun rule_np =>
      forallb (fun R =>
        existsb (Nat.eqb R) (get_rel_ids gcontext)
        && existsb (eqb np) (get_default [] lfp R)
        && forallb (fun nc =>
             if existsb (fun rule_nc => existsb (Nat.eqb R) (Datalog.hyp_rels rule_nc))
                        (get_default [] llayout nc)
             then existsb (eqb nc) (get_default [] lfc R)
                  && is_Some (get_path g np nc)
             else true)
           (map.keys llayout))
      (Datalog.concl_rels rule_np))
    (get_default [] llayout np))
  (map.keys llayout).

(* The forwarding table, THREADED THROUGH THE RESULT MONAD: emitted only when the routing is
   complete.  On success it is exactly [generate_forwarding_table]; on a missing producer->consumer
   route compilation FAILS.  This is the "correct by construction" gate -- [Success] witnesses that
   the forwarding is right, so no separate route checker is needed downstream. *)
Definition generate_forwarding_table_checked (gcontext : global_context) (ninfos : list node_info)
    (g : node_graph) (llayout : lowered_layout_map) lfc lfp : result node_ftable_map :=
  if routes_validb gcontext g llayout lfc lfp
  then Success (generate_forwarding_table gcontext ninfos g lfc lfp)
  else error:("generate_forwarding_table: some producer cannot reach some consumer (incomplete forwarding)").

(* INPUT-COMPLETENESS gate: every declared input/EDB location [ni] of relation [R] (from
   [lfact_producers]) is a recorded producer of [R] and routes to every consumer of [R].  So once
   compilation succeeds, the nodes where base facts are injected provably reach every consumer --
   the input side is correct by construction, no input route checker needed downstream. *)
Definition input_routes_validb (gcontext : global_context) (g : node_graph)
    (llayout : lowered_layout_map) (lfc lfp : lowered_fact_locations) : bool :=
  map.forallb (fun R locs =>
    forallb (fun ni =>
      existsb (eqb R) (get_rel_ids gcontext)
      && existsb (eqb ni) (get_default [] lfp R)
      && forallb (fun nc =>
           if existsb (fun rule_nc => existsb (Nat.eqb R) (Datalog.hyp_rels rule_nc))
                      (get_default [] llayout nc)
           then existsb (eqb nc) (get_default [] lfc R)
                && is_Some (get_path g ni nc)
           else true)
         (map.keys llayout))
    locs)
  lfp.

(* OUTPUT-COMPLETENESS gate (producers): every node [np] that concludes [R] forwards to some
   declared output/sink node of [R] (a fact-consumer location).  This is what makes a producer a
   "good source" on the output side, and forces every produced relation to have a sink. *)
Definition output_routesb (gcontext : global_context) (g : node_graph)
    (llayout : lowered_layout_map) (lfc lfp : lowered_fact_locations) : bool :=
  forallb (fun np =>
    forallb (fun rule_np =>
      forallb (fun R =>
                 existsb (Nat.eqb R) (get_rel_ids gcontext)
                 && existsb (eqb np) (get_default [] lfp R)
                 && existsb (fun no => is_Some (get_path g np no)) (get_default [] lfc R))
      (Datalog.concl_rels rule_np))
    (get_default [] llayout np))
  (map.keys llayout).

(* OUTPUT-COMPLETENESS gate (input nodes): every declared input/EDB location of [R] forwards to some
   declared output/sink node of [R]. *)
Definition input_output_routesb (gcontext : global_context) (g : node_graph)
    (lfc lfp : lowered_fact_locations) : bool :=
  map.forallb (fun R locs =>
    forallb (fun ni =>
      existsb (Nat.eqb R) (get_rel_ids gcontext)
      && existsb (eqb ni) (get_default [] lfp R)
      && existsb (fun no => is_Some (get_path g ni no)) (get_default [] lfc R))
      locs)
  lfp.

(*----Final Compilation----*)

Definition initial_global_context : global_context :=
  {| rel_map := map.empty;
     last_rel_id := 0 |}.

Definition compile_node (node : node_id) (program : lowered_program) : result node_info :=
  '(compiled_rules, ncontext) <-
    fold_left (fun acc rule =>
      '(rules, ncontext) <- acc ;;
      '(hr, ncontext) <- compile_rule rule ncontext ;;
      Success (hr :: rules, ncontext)%list
    ) program (Success ([], initial_node_context node)) ;;
  Success {| nid := node;
             nprogram := rev compiled_rules;
             nforwarding := map.empty;
             ntries := rev ncontext.(nctries) |}.

Definition compile_all_nodes (llayout : lowered_layout_map) : result (list node_info) :=
  ninfos <- map.fold (fun acc node program =>
    ninfos <- acc ;;
    ninfo <- compile_node node program ;;
    Success (ninfo :: ninfos)
  ) (Success []) llayout ;;
  Success (ninfos).

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
       nforwarding := get_node_ftable ninfo.(nid) ftables;
       ntries := ninfo.(ntries) |}
  ) ninfos
  ++ List.map (fun n =>
       {| nid := n;
          nprogram := [];
          nforwarding := get_node_ftable n ftables;
          ntries := [] |})
     (filter
        (fun n => negb (existsb (fun ninfo => eqb ninfo.(nid) n) ninfos))
        (map.keys ftables)).

(* every node the layout assigns to is a real graph node. *)
Definition layout_in_graphb (g : node_graph) (llayout : lowered_layout_map) : bool :=
  map.forallb (fun n _ => check_node_valid n (ComputableGraph.nodes g)) llayout.

(* THE RELABEL PASS: rename the source layout/fact-locations (over [rel]/[fn]) to numeric ids,
   producing the lowered inputs + the name-collected [global_context].  This is the ONLY place that
   touches relation/function names. *)
Definition lower_inputs (layout : layout_map) (fact_producers fact_consumers : fact_locations)
    : result (lowered_layout_map * lowered_fact_locations * lowered_fact_locations * global_context) :=
  let gcontext := collect_global_names_layout layout initial_global_context in
  llayout <- global_rename_rule_layout layout gcontext ;;
  lfact_producers <- global_rename_fact_locations fact_producers gcontext ;;
  lfact_consumers <- global_rename_fact_locations fact_consumers gcontext ;;
  Success (llayout, lfact_producers, lfact_consumers, gcontext).

(* The rel-name <-> rel-id table [lower_inputs] assigned (first-seen order over the layout).
   Reuses [lower_inputs] itself -- the ONLY place relation names are ever numbered -- so this is
   GUARANTEED to agree with the ids baked into the compiled hardware program's [output_rel]/[trel];
   no separate/duplicated numbering logic. For tooling that needs to relate a fact keyed by
   relation name (e.g. a human-authored input workload) to the compiled program's numeric ids. *)
Definition compile_rel_ids (layout : layout_map) (fact_producers fact_consumers : fact_locations)
    : result (list (rel * rel_id)) :=
  '(_, _, _, gcontext) <- lower_inputs layout fact_producers fact_consumers ;;
  Success (map.tuples gcontext.(rel_map)).

(* THE NUMERIC CORE: compile an ALREADY-LOWERED layout/fact-locations -- NO relabeling.  Computes
   the dependency context, the per-node programs, the forwarding tables, and the routing gates. *)
Definition compile_lowered (llayout : lowered_layout_map)
    (lfact_producers lfact_consumers : lowered_fact_locations) (gcontext : global_context)
    (g : node_graph) : result (list node_info) :=
  _ <- (if check_graph_valid g
        then Success tt
        else error:("compile: the topology graph is not valid (edges reference missing nodes)")) ;;
  _ <- (if layout_in_graphb g llayout
        then Success tt
        else error:("compile: a node the layout assigns rules to is not in the topology graph")) ;;
  ninfos <- compile_all_nodes llayout ;;
  ftables <- generate_forwarding_table_checked gcontext ninfos g llayout lfact_consumers lfact_producers ;;
  _ <- (if input_routes_validb gcontext g llayout lfact_consumers lfact_producers
        then Success tt
        else error:("compile: a declared input/EDB location cannot reach some consumer (incomplete input forwarding)")) ;;
  _ <- (if output_routesb gcontext g llayout lfact_consumers lfact_producers
        then Success tt
        else error:("compile: a producer cannot reach an output/sink node (incomplete output forwarding)")) ;;
  _ <- (if input_output_routesb gcontext g lfact_consumers lfact_producers
        then Success tt
        else error:("compile: an input/EDB location cannot reach an output/sink node")) ;;
  Success (attach_forwarding_tables ninfos ftables).

Definition compile (layout : layout_map) (fact_producers : fact_locations) (fact_consumers : fact_locations) (g : node_graph)
    : result (list node_info) :=
  '(llayout, lfact_producers, lfact_consumers, gcontext) <- lower_inputs layout fact_producers fact_consumers ;;
  compile_lowered llayout lfact_producers lfact_consumers gcontext g.
End DistributedDatalogToHardwareCompiler.

Existing Instance SortedListNat.map.
From coqutil Require Import SortedListString.
Existing Instance SortedListString.map.

Compute compute_permutation [2;3;1;1] [1;2;3].
Compute generate_join
  [ {| tid := 0; trel := 0; tperm := [0; 1] |} ;
    {| tid := 1; trel := 0; tperm := [1; 0] |} ]
  1
  [ {| clause_rel := 0; clause_args := [var_expr 0; var_expr 1] |} ;
    {| clause_rel := 0; clause_args := [var_expr 1; var_expr 2] |} ].
