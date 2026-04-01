From Datalog Require Import Datalog.
From Stdlib Require Import List String Bool ZArith.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties.
From DatalogRocq Require Import EqbSpec DependencyGenerator SortedListNat Graph.

Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.

Section EncodeLayout.

Context {rel var fn aggregator T : Type}.
Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.
Context {var_eq_dec : forall x y : var, {x = y} + {x <> y}}.
Context {rel_eqb : rel -> rel -> bool} {rel_eqb_spec : forall r1 r2 : rel, BoolSpec (r1 = r2) (r1 <> r2) (rel_eqb r1 r2)}.
Context {Node : Type}.

(* Map Stuff *)
Definition var_id := nat.
Definition trie_id := nat.
Definition rel_id := nat.
Definition edge_id := (nat * nat)%type.
Definition fn_id := nat.
Definition node_id := (nat * nat)%type.
Definition clause_id := nat.

(* Probably need to do some refactors for this stuff*)

Definition node_id_eqb (n1 n2 : node_id) : bool :=
  Nat.eqb (fst n1) (fst n2) && Nat.eqb (snd n1) (snd n2).

(* TODO make rel_eqbs and other stuff instead of just using Nat.eqb to keep the types well contained.*)

Definition fact := Datalog.fact rel var fn.
Definition rule := Datalog.rule rel var fn aggregator.
Definition expr := Datalog.expr var fn.
Definition program := list rule.

Definition permutation := list nat.

Record trie := {
  tid : trie_id;
  trel : rel_id;
  tperm : permutation;
}.

Inductive lowered_expr := 
| LVar (v : var)
| LFun (f : fn_id) (args : list lowered_expr).

Record lowered_fact := 
{ lf_R : rel_id;
  lf_args : list lowered_expr
}.

Record lowered_rule := 
{ lhyps : list lowered_fact;
  lconcls : list lowered_fact
}.

Definition lowered_program := list lowered_rule.

Record join := 
{
  tries : list trie_id;
  trie_levels : permutation;
  clauses : list clause_id
}.

(* Queries are all the hypothesis level joins that need to occur *)
Definition query := list join.

Record join_output :=
{
  output_rel : rel_id;
  output_var_indices : list nat
}.

Record hardware_rule := 
{ 
  hhyps : query;
  hconcls : list join_output;
}. 

Definition hardware_program := list hardware_rule.

Definition trie_ids := list trie_id.
Definition edge_ids := list edge_id.

Inductive destination :=
| DestEdge (e : edge_id)
| DestTrie (t : trie_id).

(* Maps needed and used by the compiler to generate stuffs *)
Context {forwarding_table : map.map rel_id destination}.
Context {rel_dependency_map : map.map rel_id (list node_id)}.
Context {fn_id_map : map.map fn fn_id}.
Context {rel_relid_map : map.map rel rel_id}.
Context {relid_rel_map : map.map rel_id rel}.
Context {var_id_map : map.map var var_id}.
Context {layout_map : map.map node_id program}.
Context {lowered_layout_map : map.map node_id lowered_program}.

Record node_info :=  {
  nid : node_id;
  nprogram : hardware_program;
  nforwarding : forwarding_table;
  ntries : list trie;
}.

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

(*----Collecting Global Info Used by the Compiler----*)
(* Maybe later I'll figure out if I can refactor this weird reconstruction of all the maps thing it just seems unweildy *)

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
    fold_left (fun acc arg => collect_global_names_expr arg acc) args (update_global_context_with_fn f gcontext)
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
  
Definition collect_global_names_fact (f : fact) (gcontext : global_context) : global_context :=
  fold_left (fun acc arg => collect_global_names_expr arg acc) f.(fact_args) (update_global_context_with_rel f.(fact_R) gcontext).

(* First collect the global names in the hypothesis, then in the conclusion *)
Definition collect_global_names_rule (r : rule) (gcontext : global_context) : global_context :=
  let info := fold_left (fun acc f => collect_global_names_fact f acc) r.(rule_hyps) gcontext in
  fold_left (fun acc f => collect_global_names_fact f acc) r.(rule_concls) info.

Definition collect_global_names_program (p : program) (gcontext : global_context) : global_context :=
  fold_left (fun acc r => collect_global_names_rule r acc) p gcontext.

Definition collect_global_names_layout (layout : layout_map) (gcontext : global_context) : global_context :=
  map.fold (fun acc _ program => collect_global_names_program program acc) gcontext layout.

(*----Rename Stuffs----*)

Definition rename_fn (f : fn) (gcontext : global_context) : fn_id :=
  match map.get gcontext.(fn_map) f with
  | Some id => id
  | None => 0 (* This should never happen since we should have collected all the names already *)
  end.

Fixpoint global_rename_expr (e : expr) (gcontext : global_context) : lowered_expr :=
  match e with
  | var_expr v => LVar v
  | fun_expr f args => 
    let f_id := rename_fn f gcontext in
    let args := List.map (fun arg => global_rename_expr arg gcontext) args in
    LFun f_id args
  end.

Definition global_rename_rel (r : rel) (gcontext : global_context) : rel_id :=
  match map.get gcontext.(rel_map) r with
  | Some id => id
  | None => 0 (* This should never happen since we should have collected all the names already *)
  end.

Definition global_rename_fact (f : fact) (gcontext : global_context) : lowered_fact :=
  let r_id := global_rename_rel f.(fact_R) gcontext in
  let args := List.map (fun arg => global_rename_expr arg gcontext) f.(fact_args) in
  {|
    lf_R := r_id;
    lf_args := args
  |}.

Definition global_rename_rule (r : rule) (gcontext : global_context) : lowered_rule :=
  let hyps := List.map (fun f => global_rename_fact f gcontext) r.(rule_hyps) in
  let concls := List.map (fun f => global_rename_fact f gcontext) r.(rule_concls) in
  {|
    lhyps := hyps;
    lconcls := concls
  |}.

Definition global_rename_program (p : program) (gcontext : global_context) : lowered_program :=
  List.map (fun r => global_rename_rule r gcontext) p.

Definition global_rename_rule_layout (layout : layout_map) (gcontext : global_context) : lowered_layout_map :=
  map.map_values (fun program => global_rename_program program gcontext) layout.

(*----Collecting Info About Layout----*)

Definition lowered_fact_contains_rel (f : lowered_fact) (r_id : rel_id) : bool :=
  Nat.eqb r_id f.(lf_R).

Definition lowered_facts_contains_rel (facts : list lowered_fact) (r_id : rel_id) : bool :=
  List.existsb (fun f => lowered_fact_contains_rel f r_id) facts.

Definition lowered_program_produces_rel (program : lowered_program) (r_id : rel_id) : bool :=
  List.existsb (fun rule => lowered_facts_contains_rel rule.(lconcls) r_id) program.

Definition lowered_program_consumes_rel (program : lowered_program) (r_id : rel_id) : bool :=
  List.existsb (fun rule => lowered_facts_contains_rel rule.(lhyps) r_id) program.

Definition node_produces_rel (r_id : rel_id) (llayout : lowered_layout_map)  (node_id : node_id) : bool :=
  match map.get llayout node_id with
  | Some program => lowered_program_produces_rel program r_id
  | None => false
  end.

Definition node_consumes_rel (r_id : rel_id) (llayout : lowered_layout_map)  (node_id : node_id) : bool :=
  match map.get llayout node_id with
  | Some program => lowered_program_consumes_rel program r_id
  | None => false
  end.

(* This assumes every valid node has a program associated with it. I will probably prove this somewhere TODO*)
Definition get_node_producers (r_id : rel_id) (llayout : lowered_layout_map) (gcontext : global_context) : list node_id :=
  let nodes := map.keys llayout in
  List.filter (node_produces_rel r_id llayout) nodes.

Definition get_node_consumers (r_id : rel_id) (llayout : lowered_layout_map) (gcontext : global_context) : list node_id :=
  let nodes := map.keys llayout in
  List.filter (node_consumes_rel r_id llayout) nodes.

Definition collect_global_dependencies_for_rel_id (r_id : rel_id) (llayout : lowered_layout_map) (gcontext : global_context) : (list node_id * list node_id) :=
  let producers := get_node_producers r_id llayout gcontext in
  let consumers := get_node_consumers r_id llayout gcontext in
  (producers, consumers).

Definition add_producer_to_context (r_id : rel_id) (producer : node_id) (gcontext : global_context) : global_context :=
  let rel_node_producers := match map.get gcontext.(rel_node_producers) r_id with
                            | Some producers => map.put gcontext.(rel_node_producers) r_id (producer :: producers)
                            | None => map.put gcontext.(rel_node_producers) r_id [producer]
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

Definition add_producers_to_context (r_id : rel_id) (producers : list node_id) (gcontext : global_context) : global_context :=
  List.fold_left (fun acc producer => add_producer_to_context r_id producer acc) producers gcontext.

Definition add_consumer_to_context (r_id : rel_id) (consumer : node_id) (gcontext : global_context) : global_context :=
  let rel_node_consumers := match map.get gcontext.(rel_node_consumers) r_id with
                            | Some consumers => map.put gcontext.(rel_node_consumers) r_id (consumer :: consumers)
                            | None => map.put gcontext.(rel_node_consumers) r_id [consumer]
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

Definition add_consumers_to_context (r_id : rel_id) (consumers : list node_id) (gcontext : global_context) : global_context :=
  List.fold_left (fun acc consumer => add_consumer_to_context r_id consumer acc) consumers gcontext.

Definition get_rel_ids (gcontext : global_context) : list rel_id :=
  map.fold (fun acc rel rel_id => rel_id :: acc) [] gcontext.(rel_map).

Definition collect_global_dependencies (llayout : lowered_layout_map) (gcontext : global_context) : global_context :=
  let rel_ids := get_rel_ids gcontext in
  List.fold_left (fun acc rel_id => let (producers, consumers) := collect_global_dependencies_for_rel_id rel_id llayout gcontext in
                                   let acc := add_producers_to_context rel_id producers acc in
                                   add_consumers_to_context rel_id consumers acc) rel_ids gcontext.

(*----Collect local rule context information----*)
Fixpoint collect_rule_context_expr (le : lowered_expr) (rcontext : rule_context) : rule_context :=
  match le with
  | LVar v => match map.get rcontext.(var_map) v with
             | Some _ => rcontext
             | None => 
               {|
                 var_map := map.put rcontext.(var_map) v rcontext.(last_var_id);
                 last_var_id := S rcontext.(last_var_id);
               |}
             end
  | LFun f args =>
    fold_left (fun acc arg => collect_rule_context_expr arg acc) args rcontext
  end.

Definition collect_rule_context_fact (lfact : lowered_fact) (rcontext : rule_context) : rule_context :=
  fold_left (fun acc arg => collect_rule_context_expr arg acc) lfact.(lf_args) rcontext.

Definition collect_rule_context_rule (lrule : lowered_rule) (rcontext : rule_context) : rule_context :=
  let info := fold_left (fun acc f => collect_rule_context_fact f acc) lrule.(lhyps) rcontext in
  fold_left (fun acc f => collect_rule_context_fact f acc) lrule.(lconcls) info.


(*----Dependency Stuff For Picking Variable Ordering----*)

Context {var_set : map.map var unit}.

Definition var_edge := (var * var)%type.
Definition verticies := var_set.
Context {var_edge_map : map.map var (var_set)}.

Record var_graph := {
  vertices : verticies;
  edges : var_edge_map;
}.

Fixpoint add_arg_edges (arg : lowered_expr) (dep_graph : var_graph) (clause_vars : var_set) : var_graph :=
  match arg with
  | LVar v => 
    let new_edges := match map.get dep_graph.(edges) v with
                     | Some neighbors => map.putmany neighbors clause_vars
                     | None => clause_vars
                     end in
    {|
      vertices := dep_graph.(vertices);
      edges := map.put dep_graph.(edges) v new_edges
    |}
  | LFun _ args =>
    fold_left (fun acc arg => add_arg_edges arg acc clause_vars) args dep_graph
  end.

Fixpoint add_args_edges (args : list lowered_expr) (dep_graph : var_graph) (seen : var_set) : var_graph :=
  match args with
  | [] => dep_graph
  | arg :: rest =>
    let dep_graph' := add_arg_edges arg dep_graph seen in
    let seen := match arg with
              | LVar v => map.put seen v tt
              | LFun _ args => seen (* TODO: This is not correct, we should be adding all the variables in the args to the seen set, but this is just a first pass *)
              end in
    add_args_edges rest dep_graph' seen
  end.

Definition add_hyp_edges (hyp : lowered_fact) (dep_graph : var_graph) : var_graph :=
  add_args_edges hyp.(lf_args) dep_graph (map.empty).

Definition create_dependency_graph (hyps : list lowered_fact) : var_graph :=
  fold_left (fun acc hyp => add_hyp_edges hyp acc) hyps {|
    vertices := map.empty;
    edges := map.empty
  |}.

Definition neighbors (g : var_graph) (v : var) : verticies :=
  match map.get g.(edges) v with
  | Some neighbors => neighbors
  | None => map.empty
  end.


Definition add_to_visited (visited : verticies) (v : var) : verticies :=
  map.put visited v tt.

Definition compute_degree (dep_graph : var_graph) (var : var) : nat :=
  let neighbors := neighbors dep_graph var in
  map.fold (fun acc _ _ => S acc) 0 neighbors.

Definition compute_degree_to_visited_set (dep_graph : var_graph) (visited : verticies) (var : var) : nat := 
  let neighbors := neighbors dep_graph var in
  map.fold (fun acc neighbor _ => if map.get visited neighbor then S acc else acc) 0 neighbors.

Definition compute_max_degree_var_to_visited_set (dep_graph : var_graph) (visited : verticies) : option (var * nat):=
  map.fold (fun acc var _ => 
             let degree := compute_degree_to_visited_set dep_graph visited var in
             match acc with
             | None => Some (var, degree)
             | Some (_, max_degree) => if Nat.ltb max_degree degree then Some (var, degree) else acc
             end) None dep_graph.(vertices).

Definition compute_max_degree_var (dep_graph : var_graph) : option (var * nat) :=
  map.fold (fun acc var _ => 
             let degree := compute_degree dep_graph var in
             match acc with
             | None => Some (var, degree)
             | Some (_, max_degree) => if Nat.ltb max_degree degree then Some (var, degree) else acc
             end) None dep_graph.(vertices).

Definition remove_edge_from_graph (dep_graph : var_graph) (v1 : var) (v2 : var) : var_graph := 
  let new_edges_v1 := match map.get dep_graph.(edges) v1 with
                      | Some neighbors => map.remove neighbors v2
                      | None => map.empty
                      end in
  let new_edges_v2 := match map.get dep_graph.(edges) v2 with
                      | Some neighbors => map.remove neighbors v1
                      | None => map.empty
                      end in
  {|
    vertices := dep_graph.(vertices);
    edges :=  map.put (map.put dep_graph.(edges) v1 new_edges_v1) v2 new_edges_v2
  |}.

Definition remove_edges_touching_var (dep_graph : var_graph) (var : var) : var_graph :=
  let neighbors := neighbors dep_graph var in
  map.fold (fun acc neighbor _ => remove_edge_from_graph acc var neighbor) dep_graph neighbors.

Record ordering_context := {
  dep_graph : var_graph;
  order : list var;
  visited : verticies;
}.

Definition visit_node (var : var) (ordering_ctx : ordering_context) : ordering_context :=
  {|
    dep_graph := remove_edges_touching_var ordering_ctx.(dep_graph) var;
    order := ordering_ctx.(order) ++ [var];
    visited := add_to_visited ordering_ctx.(visited) var
  |}.

Definition inital_ordering_context (dep_graph : var_graph) : ordering_context :=
  {|
    dep_graph := dep_graph;
    order := [];
    visited := map.empty
  |}.

Definition choose_next_var (ctx : ordering_context) : option var :=
  match compute_max_degree_var_to_visited_set ctx.(dep_graph) ctx.(visited) with
  | Some (v, _) => Some v
  | None =>
      match compute_max_degree_var ctx.(dep_graph) with
      | Some (v, _) => Some v
      | None => None
      end
  end.

Fixpoint compute_variable_ordering_h (ordering_ctx : ordering_context) (fuel : nat) : ordering_context :=
  match fuel with
  | O => ordering_ctx
  | S fuel' =>
      match choose_next_var ordering_ctx with
      | Some v => compute_variable_ordering_h (visit_node v ordering_ctx) fuel'
      | None => ordering_ctx
      end
  end.

Definition initial_ordering_context (dep_graph : var_graph) : ordering_context :=
  {|
    dep_graph := dep_graph;
    order := [];
    visited := map.empty
  |}.

Definition compute_variable_ordering (dep_graph : var_graph) : list var :=
  let ordering_ctx := compute_variable_ordering_h (initial_ordering_context dep_graph) (List.length (map.keys dep_graph.(vertices))) in
  ordering_ctx.(order).

(*----Trie Allocation Stuff----*)
Definition vars_of_arg (arg : lowered_expr) : list var :=
  match arg with
  | LVar v => [v]
  | LFun _ args => [] (* TODO deal with functions still*)
  end.


Definition compute_var_order (lf : lowered_fact) : list var :=
  List.flat_map vars_of_arg lf.(lf_args).

Context{var_idx_map : map.map var nat}.

Fixpoint index_of_var (v : var) (vars : list var) : option nat :=
  match vars with
  | [] => None
  | v' :: rest => if var_eqb v v' then Some 0 else match index_of_var v rest with
                                                  | Some idx => Some (S idx)
                                                  | None => None
                                                  end
  end.

Fixpoint count_occ (v : var) (l : list var) : nat :=
  match l with
  | [] => 0
  | x :: xs =>
      (if var_eqb x v then 1 else 0) + count_occ v xs
  end.

Fixpoint build_base_map (desired_order : list var) (original_order : list var) (offset : nat) (m : var_idx_map) :=
  match desired_order with
  | [] => m
  | v :: vs =>
      let m' := map.put m v offset in
      let offset' := offset + count_occ v original_order in
      build_base_map vs original_order offset' m'
  end.

Fixpoint compute_perm_aux (original_order : list var) (base_map occ_map : var_idx_map) :=
  match original_order with
  | [] => []
  | v :: vs =>
      let base :=
        match map.get base_map v with
        | Some n => n
        | None => 0
        end
      in
      let occ :=
        match map.get occ_map v with
        | Some n => n
        | None => 0
        end
      in
      let occ_map' := map.put occ_map v (occ + 1) in
      (base + occ) :: compute_perm_aux vs base_map occ_map'
  end.

Definition compute_permutation original_order desired_order :=
  let base_map :=
    build_base_map desired_order original_order 0 (map.empty)
  in
  compute_perm_aux original_order base_map (map.empty).


(*----Trie Generation Time----*)

Definition permutation_eqb (p1 p2 : permutation) : bool :=
  if Nat.eqb (List.length p1) (List.length p2) then
    List.forallb (fun '(x, y) => Nat.eqb x y) (List.combine p1 p2)
  else false.

Definition update_node_context_with_trie (trie : trie) (ncontext : node_context) : node_context :=
  {|
    ncid := ncontext.(ncid);
    nctries := trie :: ncontext.(nctries);
    last_trie_id := S ncontext.(last_trie_id)
  |}.

Definition generate_trie (hyp : lowered_fact) (rule_var_order: list var) (existing_tries : list trie) (gcontext : global_context) (ncontext : node_context): trie * node_context :=
  let original_var_order := compute_var_order hyp in
  let permutation := compute_permutation original_var_order rule_var_order in
  let rel_id := hyp.(lf_R) in
  match List.find (fun t => Nat.eqb t.(trel) rel_id && permutation_eqb t.(tperm) permutation) existing_tries with
  | Some trie => (trie, ncontext)
  | None => 
      let new_trie := {|
        tid := S ncontext.(last_trie_id);
        trel := rel_id;
        tperm := permutation
      |} in
      (new_trie, update_node_context_with_trie new_trie ncontext)
  end.

Definition get_rule_var_index_option (rule_var_order : list var) (v : var) : option nat :=
  index_of_var v rule_var_order.

Definition get_rule_var_index (rule_var_order : list var) (v : var) : nat :=
  match get_rule_var_index_option rule_var_order v with
  | Some idx => idx
  | None => 0 (* This should never happen since we should have collected all the variables already *)
  end.

Fixpoint var_in_arg (v : var) (arg : lowered_expr) : bool :=
  match arg with
  | LVar v' => var_eqb v v'
  | LFun _ args => List.existsb (var_in_arg v) args
  end.

Fixpoint get_hyp_arg_indices (args : list lowered_expr) (v : var) (i : nat) : list nat :=
  match args with
  | [] => []
  | arg :: rest =>
      let acc := get_hyp_arg_indices rest v (S i) in
      match arg with
      | LVar v' => if var_eqb v v' then i :: acc else acc
      | LFun _ _ => acc (* TODO deal with functions still*)
      end
  end.

Definition generate_join (tries_by_hyp : list trie) (v : var) (hyps : list lowered_fact) : join :=
  let '(ts, levels, cs, _) :=
    List.fold_left
      (fun acc pair =>
        let '(ts, levels, cs, clause) := acc in
        let '(t, hyp) := pair in
        let indices := get_hyp_arg_indices hyp.(lf_args) v 0 in
        let '(ts', levels', cs') :=
          List.fold_left
            (fun inner_acc arg_idx =>
              let '(ts', levels', cs') := inner_acc in
              let trie_level := List.nth arg_idx t.(tperm) 0 in
              (t.(tid) :: ts', trie_level :: levels', clause :: cs'))
            indices
            (ts, levels, cs)
        in
        (ts', levels', cs', S clause))
      (List.combine tries_by_hyp hyps)
      ([], [], [], 0)
  in
  {| tries := ts; trie_levels := levels; clauses := cs |}.


Definition generate_query (tries : list trie) (rule_var_order : list var) (hyps : list lowered_fact) : query :=
  List.map (fun var => generate_join tries var hyps) rule_var_order.

Definition compile_hyps (hyps : list lowered_fact) (rule_var_order : list var) (existing_tries : list trie) (gcontext : global_context) (ncontext : node_context) : query :=
  let '(tries, ncontext) := List.fold_left (fun '(tries, ncontext) hyp => 
                                            let (trie, ncontext) := generate_trie hyp rule_var_order tries gcontext ncontext in
                                            (trie :: tries, ncontext)) hyps (existing_tries, ncontext) in
  generate_query tries rule_var_order hyps.

Definition initial_node_context (node_id : node_id): node_context :=
  {|
    ncid := node_id;
    nctries := [];
    last_trie_id := 0
  |}.

Definition compile_concl (concl : lowered_fact) (gcontext : global_context) (rule_var_order : list var): join_output :=
  let rel_id := concl.(lf_R) in
  let var_indices := List.map (fun arg => match arg with
                                        | LVar v => get_rule_var_index rule_var_order v
                                        | LFun _ _ => 0 (* TODO deal with functions still*)
                                        end) concl.(lf_args) in
  {|
    output_rel := rel_id;
    output_var_indices := var_indices
  |}.

Definition compile_concls (concls : list lowered_fact) (gcontext : global_context) (rule_var_order : list var) : list join_output :=
  List.map (fun concl => compile_concl concl gcontext rule_var_order) concls.

Definition compile_rule (rule : lowered_rule) (gcontext : global_context) (node_id : node_id) : hardware_rule :=
  let rule_var_order := compute_variable_ordering (create_dependency_graph rule.(lhyps)) in
  let ncontext := initial_node_context node_id in
  let query := compile_hyps rule.(lhyps) rule_var_order ncontext.(nctries) gcontext ncontext in
  let concls := compile_concls rule.(lconcls) gcontext rule_var_order in
  {|
    hhyps := query;
    hconcls := concls
  |}.


(*----Graph Stuff For Doing BFS Process ----*)

(* TODO make a proper graph library for this cuz I need to stop making rando graph things here *)
Context {node_id_set : map.map node_id unit}.
Context {node_id_edge_map : map.map node_id (list node_id)}.

Record node_graph := {
  nnodes : node_id_set;
  nedges : node_id_edge_map;
}.

Record bfs_state := {
  bs_queue : list (node_id * list node_id);
  bs_visited : node_id_set;
}.

Definition bfs_initial (start : node_id) : bfs_state := {|
  bs_queue := [(start, [start])];
  bs_visited := map.put map.empty start tt;
|}.

Definition node_neighbors (g : node_graph) (n : node_id) : list node_id :=
  match map.get g.(nedges) n with
  | Some neighbors => neighbors
  | None => []
  end.

Definition bfs_step (g : node_graph) (target : node_id) (state : bfs_state) : bfs_state + list node_id :=
  match state.(bs_queue) with
  | [] => inl state
  | (node, path) :: rest =>
      if node_id_eqb node target then inr (List.rev path)
      else
        let neighbors := node_neighbors g node in
        let unvisited := List.filter (fun n => 
          match map.get state.(bs_visited) n with
          | Some _ => false
          | None => true
          end) neighbors in
        let new_visited := List.fold_left (fun acc n => 
          map.put acc n tt) unvisited state.(bs_visited) in
        let new_entries := List.map (fun n => (n, n :: path)) unvisited in
        inl {|
          bs_queue := rest ++ new_entries;
          bs_visited := new_visited;
        |}
  end.

Fixpoint bfs_aux (g : node_graph) (target : node_id) (state : bfs_state) (fuel : nat) 
    : option (list node_id) :=
  match fuel with
  | O => None
  | S fuel' =>
      match bfs_step g target state with
      | inr path => Some path
      | inl state' => 
          match state'.(bs_queue) with
          | [] => None
          | _ => bfs_aux g target state' fuel'
          end
      end
  end.

Definition bfs (g : node_graph) (start target : node_id) (fuel : nat) : option (list node_id) :=
  bfs_aux g target (bfs_initial start) fuel.

Context {node_ftable_map : map.map node_id forwarding_table}.

Definition get_path (g : node_graph) (nstart nend : node_id) (fuel : nat) : option (list node_id) :=
  bfs g nstart nend fuel.

Definition get_node_ftable (node : node_id) (ftables : node_ftable_map) : forwarding_table :=
  match map.get ftables node with
  | Some ft => ft
  | None => map.empty
  end.

Definition get_rel_destinations (rel : rel_id) (ft : forwarding_table) : list destination :=
  match map.get ft rel with
  | Some dst => [dst]
  | None => []
  end.

Definition add_trie_dest_to_forwarding_table 
    (node : node_id) (rel : rel_id) 
    (ftables : node_ftable_map) (ninfos : list node_info) : node_ftable_map :=
  let ft := get_node_ftable node ftables in
  let matching_tries :=
    match List.find (fun n => node_id_eqb n.(nid) node) ninfos with
    | None => []
    | Some ninfo => List.filter (fun t => Nat.eqb t.(trel) rel) ninfo.(ntries)
    end in
  let updated_ft :=
    List.fold_left (fun ft t =>
      map.put ft rel (DestTrie t.(tid))
    ) matching_tries ft in
  map.put ftables node updated_ft.

Fixpoint add_path_to_forwarding_table
    (rel : rel_id) (path : list node_id)
    (ftables : node_ftable_map) (ninfos : list node_info) : node_ftable_map :=
  match path with
  | [] => ftables
  | [node] =>
      add_trie_dest_to_forwarding_table node rel ftables ninfos
  | node :: ((next :: _) as rest) =>
      let ft := get_node_ftable node ftables in
      let ft' := map.put ft rel (DestEdge next) in
      let ftables' := map.put ftables node ft' in
      add_path_to_forwarding_table rel rest ftables' ninfos
  end.

Definition update_forwarding_table_for_rel
    (rel : rel_id) (gcontext : global_context)
    (ninfos : list node_info) (ftables : node_ftable_map) (fuel : nat)
    (g : node_graph) : node_ftable_map :=
  let producers := match map.get gcontext.(rel_node_producers) rel with
                   | Some ps => ps
                   | None => []
                   end in
  let consumers := match map.get gcontext.(rel_node_consumers) rel with
                   | Some cs => cs
                   | None => []
                   end in
  List.fold_left (fun ftables producer =>
    List.fold_left (fun ftables consumer =>
      if node_id_eqb producer consumer then ftables
      else
        match get_path g producer consumer fuel with
        | None => ftables
        | Some path => add_path_to_forwarding_table rel path ftables ninfos
        end
    ) consumers ftables
  ) producers ftables.

Definition generate_forwarding_table
    (gcontext : global_context) (ninfos : list node_info)
    (g : node_graph) (fuel : nat) : node_ftable_map :=
  let rel_ids := get_rel_ids gcontext in
  List.fold_left (fun ftables rel =>
    update_forwarding_table_for_rel rel gcontext ninfos ftables fuel g
  ) rel_ids map.empty.

(*----Final Compilation Stuff----*)

Definition initial_rule_context : rule_context :=
  {|
    var_map := map.empty;
    last_var_id := 0
  |}.

Definition initial_global_context : global_context :=
  {|
    fn_map := map.empty;
    rel_map := map.empty;
    topo := {| Graph.nodes := fun _ => False; Graph.edge := fun _ _ => False |};
    rel_node_consumers := map.empty;
    rel_node_producers := map.empty;
    last_fn_id := 0;
    last_rel_id := 0
  |}.

Definition compile_node (node : node_id) (program : lowered_program) 
    (gcontext : global_context) : node_info :=
  let compiled_rules := List.map (fun rule => compile_rule rule gcontext node) program in
  let ncontext := List.fold_left (fun acc rule =>
    {| ncid := acc.(ncid);
       nctries := acc.(nctries);
       last_trie_id := acc.(last_trie_id) |}
  ) compiled_rules (initial_node_context node) in
  {|
    nid := node;
    nprogram := compiled_rules;
    nforwarding := map.empty;
    ntries := ncontext.(nctries);
  |}.

Definition compile_all_nodes (llayout : lowered_layout_map) 
    (gcontext : global_context) : list node_info :=
  map.fold (fun acc node program =>
    compile_node node program gcontext :: acc
  ) [] llayout.

Definition attach_forwarding_tables 
    (ninfos : list node_info) (ftables : node_ftable_map) : list node_info :=
  List.map (fun ninfo =>
    let ft := match map.get ftables ninfo.(nid) with
              | Some ft => ft
              | None => map.empty
              end in
    {| nid := ninfo.(nid);
       nprogram := ninfo.(nprogram);
       nforwarding := ft;
       ntries := ninfo.(ntries) |}
  ) ninfos.

Definition compile (layout : layout_map) (g : node_graph) (fuel : nat) : list node_info :=
  let gcontext := collect_global_names_layout layout initial_global_context in
  let llayout := global_rename_rule_layout layout gcontext in
  let gcontext := collect_global_dependencies llayout gcontext in
  let ninfos := compile_all_nodes llayout gcontext in
  let ftables := generate_forwarding_table gcontext ninfos g fuel in
  attach_forwarding_tables ninfos ftables.

End EncodeLayout.

(* Just testing out some stuff*)
Existing Instance SortedListNat.map.
Compute compute_permutation (var := nat) (var_eqb := Nat.eqb) [2;3;1;1] [1;2;3].
Compute generate_join
  (var := nat) (var_eqb := Nat.eqb)
  (* tries_by_hyp *)
  [ {| tid := 0; trel := 0; tperm := [0; 1] |} ;   (* trie for edge(x,y) *)
    {| tid := 1; trel := 0; tperm := [1; 0] |} ]   (* trie for edge(y,z) *)
  (* v = y, which is nat 1 *)
  1
  (* hyps *)
  [ {| lf_R := 0; lf_args := [LVar 0; LVar 1] |} ;  (* edge(x,y) *)
    {| lf_R := 0; lf_args := [LVar 1; LVar 2] |} ]  (* edge(y,z) *)
  .