From Datalog Require Import Datalog.
From Stdlib Require Import List String Bool ZArith.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Result.
From DatalogRocq Require Import EqbSpec DependencyGenerator SortedListNat Graph ComputableGraph EqbSpec.

Open Scope result_monad_scope.
Open Scope error_scope.
Open Scope bool_scope.
Import ListNotations.

Module Import RM := ResultMonadNotations.

Section EncodeLayout.

Context {rel var fn aggregator T : Type}.
Context {var_eqb : var -> var -> bool} {var_eqb_spec : forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.
Context {var_eq_dec : forall x y : var, {x = y} + {x <> y}}.
Context {rel_eqb : rel -> rel -> bool} {rel_eqb_spec : forall r1 r2 : rel, BoolSpec (r1 = r2) (r1 <> r2) (rel_eqb r1 r2)}.
Context {Node : Type}.

Definition var_id := nat.
Definition trie_id := nat.
Definition rel_id := nat.
Definition edge_id := (nat * nat)%type.
Definition fn_id := nat.
Definition node_id := (nat * nat)%type.
Definition clause_id := nat.

Definition node_id_eqb (n1 n2 : node_id) : bool :=
  pair_eqb Nat.eqb Nat.eqb n1 n2.

Definition nat_eqb_spec : forall x y : nat, BoolSpec (x = y) (x <> y) (Nat.eqb x y).
Proof.
  intros x y. destruct (Nat.eqb_spec x y); constructor; congruence.
Qed.

Definition node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y).
Proof.
  intros x y. eapply pair_eqb_spec; apply nat_eqb_spec.
Qed.

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

Definition destination_eqb (d1 d2 : destination) : bool :=
  match d1, d2 with
  | DestEdge e1, DestEdge e2 => pair_eqb Nat.eqb Nat.eqb e1 e2
  | DestTrie t1, DestTrie t2 => Nat.eqb t1 t2
  | _, _ => false
  end.

Lemma destination_eqb_spec : forall x y : destination, BoolSpec (x = y) (x <> y) (destination_eqb x y).
Proof.
  intros x y. destruct x, y; try (constructor; congruence).
  - destruct e, e0. admit.
  - admit.
Admitted.

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

Record node_info := {
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

Definition collect_global_names_fact (f : fact) (gcontext : global_context) : global_context :=
  fold_left (fun acc arg => collect_global_names_expr arg acc)
    f.(fact_args) (update_global_context_with_rel f.(fact_R) gcontext).

Definition collect_global_names_rule (r : rule) (gcontext : global_context) : global_context :=
  let info := fold_left (fun acc f => collect_global_names_fact f acc) r.(rule_hyps) gcontext in
  fold_left (fun acc f => collect_global_names_fact f acc) r.(rule_concls) info.

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
  | var_expr v => Success (LVar v)
  | fun_expr f args =>
    f_id <- rename_fn f gcontext ;;
    rargs <- fold_left (fun acc arg =>
      rargs <- acc ;;
      rarg <- global_rename_expr arg gcontext ;;
      Success (rarg :: rargs)%list
    ) args (Success []) ;;
    Success (LFun f_id rargs)
  end.

Definition global_rename_rel (r : rel) (gcontext : global_context) : result rel_id :=
  match map.get gcontext.(rel_map) r with
  | Some id => Success id
  | None => error:("global_rename_rel: relation not found in global context")
  end.

Definition global_rename_fact (f : fact) (gcontext : global_context) : result lowered_fact :=
  r_id <- global_rename_rel f.(fact_R) gcontext ;;
  rargs <- fold_left (fun acc arg =>
    rargs <- acc ;;
    rarg <- global_rename_expr arg gcontext ;;
    Success (rarg :: rargs)
  ) f.(fact_args) (Success []) ;;
  Success {| lf_R := r_id; lf_args := rargs |}.

Definition global_rename_rule (r : rule) (gcontext : global_context) : result lowered_rule :=
  hyps <- fold_left (fun acc f =>
    rfs <- acc ;;
    rf <- global_rename_fact f gcontext ;;
    Success (rf :: rfs)
  ) r.(rule_hyps) (Success []) ;;
  concls <- fold_left (fun acc f =>
    rfs <- acc ;;
    rf <- global_rename_fact f gcontext ;;
    Success (rf :: rfs)
  ) r.(rule_concls) (Success []) ;;
  Success {| lhyps := hyps; lconcls := concls |}.

Definition global_rename_program (p : program) (gcontext : global_context) : result lowered_program :=
  fold_left (fun acc r =>
    rs <- acc ;;
    lr <- global_rename_rule r gcontext ;;
    Success (lr :: rs)
  ) p (Success []).

Definition global_rename_rule_layout (layout : layout_map) (gcontext : global_context)
    : result lowered_layout_map :=
  map.fold (fun acc node program =>
    llayout <- acc ;;
    lp <- global_rename_program program gcontext ;;
    Success (map.put llayout node lp)
  ) (Success map.empty) layout.

(*----Collecting Info About Layout----*)

Definition lowered_fact_contains_rel (f : lowered_fact) (r_id : rel_id) : bool :=
  Nat.eqb r_id f.(lf_R).

Definition lowered_facts_contains_rel (facts : list lowered_fact) (r_id : rel_id) : bool :=
  List.existsb (fun f => lowered_fact_contains_rel f r_id) facts.

Definition lowered_program_produces_rel (program : lowered_program) (r_id : rel_id) : bool :=
  List.existsb (fun rule => lowered_facts_contains_rel rule.(lconcls) r_id) program.

Definition lowered_program_consumes_rel (program : lowered_program) (r_id : rel_id) : bool :=
  List.existsb (fun rule => lowered_facts_contains_rel rule.(lhyps) r_id) program.

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

Definition get_node_producers (r_id : rel_id) (llayout : lowered_layout_map)
    (gcontext : global_context) : list node_id :=
  List.filter (node_produces_rel r_id llayout) (map.keys llayout).

Definition get_node_consumers (r_id : rel_id) (llayout : lowered_layout_map)
    (gcontext : global_context) : list node_id :=
  List.filter (node_consumes_rel r_id llayout) (map.keys llayout).

Definition collect_global_dependencies_for_rel_id (r_id : rel_id) (llayout : lowered_layout_map)
    (gcontext : global_context) : (list node_id * list node_id) :=
  (get_node_producers r_id llayout gcontext,
   get_node_consumers r_id llayout gcontext).

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

Definition collect_global_dependencies (llayout : lowered_layout_map)
    (gcontext : global_context) : global_context :=
  fold_left (fun acc rel_id =>
    let (producers, consumers) :=
      collect_global_dependencies_for_rel_id rel_id llayout gcontext in
    add_consumers_to_context rel_id consumers
      (add_producers_to_context rel_id producers acc)
  ) (get_rel_ids gcontext) gcontext.

(*----Variable ordering----*)

Context {var_set : map.map var unit}.

Definition vg_neighbors (g : var_graph) (v : var) : var_node_set :=
  match map.get g.(edges) v with
  | Some ns => ns
  | None => map.empty
  end.

Fixpoint add_arg_edges (arg : lowered_expr) (g : var_graph) (clause_vars : var_node_set) : var_graph :=
  match arg with
  | LVar v =>
    let new_neighbors := map.putmany (vg_neighbors g v) clause_vars in
    {| nodes := map.put g.(nodes) v tt;
       edges := map.put g.(edges) v new_neighbors |}
  | LFun _ args =>
    fold_left (fun acc arg => add_arg_edges arg acc clause_vars) args g
  end.

Fixpoint add_args_edges (args : list lowered_expr) (g : var_graph) (seen : var_node_set) : var_graph :=
  match args with
  | [] => g
  | arg :: rest =>
    let g' := add_arg_edges arg g seen in
    let seen' := match arg with
                 | LVar v => map.put seen v tt
                 | LFun _ _ => seen
                 end in
    add_args_edges rest g' seen'
  end.

Definition add_hyp_edges (hyp : lowered_fact) (g : var_graph) : var_graph :=
  add_args_edges hyp.(lf_args) g map.empty.

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

Fixpoint compute_variable_ordering_h (ctx : ordering_context) (fuel : nat) : ordering_context :=
  match fuel with
  | O => ctx
  | S fuel' =>
    match choose_next_var ctx with
    | Some v => compute_variable_ordering_h (visit_node v ctx) fuel'
    | None => ctx
    end
  end.

Definition compute_variable_ordering (g : var_graph) : list var :=
  (compute_variable_ordering_h (initial_ordering_context g)
     (List.length (map.keys g.(nodes)))).(order).

(*----Trie Allocation----*)

Definition vars_of_arg (arg : lowered_expr) : list var :=
  match arg with
  | LVar v => [v]
  | LFun _ _ => []
  end.

Definition compute_var_order (lf : lowered_fact) : list var :=
  List.flat_map vars_of_arg lf.(lf_args).

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
  let rel_id := hyp.(lf_R) in
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
    | LVar v' => if var_eqb v v' then i :: acc else acc
    | LFun _ _ => acc
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
          (get_hyp_arg_indices hyp.(lf_args) v 0) (ts, levels, cs)
      in
      (ts', levels', cs', S clause))
      (List.combine tries_by_hyp hyps) ([], [], [], 0)
  in
  {| tries := ts; trie_levels := levels; clauses := cs |}.

Definition generate_query (tries : list trie) (rule_var_order : list var)
    (hyps : list lowered_fact) : query :=
  List.map (fun v => generate_join tries v hyps) rule_var_order.

Definition compile_hyps (hyps : list lowered_fact) (rule_var_order : list var)
    (existing_tries : list trie) (gcontext : global_context) (ncontext : node_context)
    : query * node_context :=
  let '(tries, ncontext) :=
    fold_left (fun '(tries, ncontext) hyp =>
      let (t, ncontext) := generate_trie hyp rule_var_order tries gcontext ncontext in
      (t :: tries, ncontext)) hyps (existing_tries, ncontext) in
  (generate_query tries rule_var_order hyps, ncontext).

Definition initial_node_context (nid : node_id) : node_context :=
  {| ncid := nid; nctries := []; last_trie_id := 0 |}.

Definition compile_concl (concl : lowered_fact) (gcontext : global_context)
    (rule_var_order : list var) : result join_output :=
  var_indices <- fold_left (fun acc arg =>
    idxs <- acc ;;
    match arg with
    | LVar v =>
      idx <- get_rule_var_index rule_var_order v ;;
      Success (idx :: idxs)
    | LFun _ _ => Success (0 :: idxs)
    end
  ) concl.(lf_args) (Success []) ;;
  Success {| output_rel := concl.(lf_R); output_var_indices := var_indices |}.

Definition compile_concls (concls : list lowered_fact) (gcontext : global_context)
    (rule_var_order : list var) : result (list join_output) :=
  fold_left (fun acc concl =>
    jos <- acc ;;
    jo <- compile_concl concl gcontext rule_var_order ;;
    Success (jo :: jos)
  ) concls (Success []).

Definition compile_rule (rule : lowered_rule) (gcontext : global_context)
    (ncontext : node_context) : result (hardware_rule * node_context) :=
  let rule_var_order := compute_variable_ordering (create_dependency_graph rule.(lhyps)) in
  let '(query, ncontext) :=
    compile_hyps rule.(lhyps) rule_var_order ncontext.(nctries) gcontext ncontext in
  concls <- compile_concls rule.(lconcls) gcontext rule_var_order ;;
  Success ({| hhyps := query; hconcls := concls |}, ncontext).

(*----Forwarding Tables----*)

Context {node_ftable_map : map.map node_id forwarding_table}.

Definition get_node_ftable (node : node_id) (ftables : node_ftable_map) : forwarding_table :=
  match map.get ftables node with
  | Some ft => ft
  | None => map.empty
  end.

Definition add_trie_dest_to_forwarding_table (node : node_id) (rel : rel_id)
    (ftables : node_ftable_map) (ninfos : list node_info) : node_ftable_map :=
  let ft := get_node_ftable node ftables in
  let matching_tries :=
    match List.find (fun n => node_id_eqb n.(nid) node) ninfos with
    | None => []
    | Some ninfo => List.filter (fun t => Nat.eqb t.(trel) rel) ninfo.(ntries)
    end in
  let existing := match map.get ft rel with
                  | Some ds => ds | None => [] end in
  let updated_ft :=
    map.put ft rel (fold_left (fun acc t => DestTrie t.(tid) :: acc) matching_tries existing) in
  map.put ftables node updated_ft.

Fixpoint add_path_to_forwarding_table (rel : rel_id) (path : list node_id)
    (ftables : node_ftable_map) (ninfos : list node_info) : node_ftable_map :=
  match path with
  | [] => ftables
  | [node] => add_trie_dest_to_forwarding_table node rel ftables ninfos
  | node :: ((next :: _) as rest) =>
    let ft := get_node_ftable node ftables in
    let existing := match map.get ft rel with
                    | Some ds => ds | None => [] end in
    let ft' := map.put ft rel (DestEdge next :: existing) in
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
             nprogram := compiled_rules;
             nforwarding := map.empty;
             ntries := List.rev ncontext.(nctries) |}.

Definition compile_all_nodes (llayout : lowered_layout_map)
    (gcontext : global_context) : result (list node_info) :=
  map.fold (fun acc node program =>
    ninfos <- acc ;;
    ninfo <- compile_node node program gcontext ;;
    Success (ninfo :: ninfos)
  ) (Success []) llayout.

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

Definition compile (layout : layout_map) (g : node_graph) (fuel : nat)
    : result (list node_info) :=
  let gcontext := collect_global_names_layout layout initial_global_context in
  llayout <- global_rename_rule_layout layout gcontext ;;
  let gcontext := collect_global_dependencies llayout gcontext in
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
  [ {| lf_R := 0; lf_args := [LVar 0; LVar 1] |} ;
    {| lf_R := 0; lf_args := [LVar 1; LVar 2] |} ].