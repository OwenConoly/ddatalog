(* Adequate fuel for the distributed compiler.

   The only way [fuel] enters [compile] is as the bound on the topology path search
   [get_path] (= ComputableGraph.bfs) inside the forwarding-table construction and the
   route-completeness gates.  ComputableGraphComplete proves that bfs is fuel-stable above
   [graph_fuel g = #nodes(g)] -- a quantity computed from an ARBITRARY graph's node set, not a
   grid-specific constant.  Propagating that through the gates shows [compile] is fuel-stable
   above [graph_fuel], so the computed [graph_fuel] is always adequate: whatever a larger fuel
   compiles, [graph_fuel] compiles identically -- and [compile_implements_source] then holds at
   the computed fuel.  (grid_fuel is just the grid instance of [graph_fuel].) *)

From Datalog Require Import Datalog.
From Stdlib Require Import List String Bool ZArith Lia.
From coqutil Require Import Map.Interface Map.Properties Result.
From DatalogRocq Require Import DistributedDatalogToHardwareCompiler ComputableGraph Topologies.ComputableGraphComplete.
From DatalogRocq Require Import Correctness.DistributedDatalogToHardwareCompilerCorrect.
Import ListNotations.

Section AdequateFuel.

(* CompileTop's context (verbatim), PLUS the two map.ok instances the BFS proofs need
   (the grid topology supplies them). *)
Context {rel var fn aggregator T : Type}.
Context {var_eqb : var -> var -> bool}
        {var_eqb_spec : forall x y : var, BoolSpec (x = y) (x <> y) (var_eqb x y)}.
Context `{sig : signature nat aggregator T}.
Context {context : map.map var T} {context_ok : map.ok context}.
Context {var_idx_map : map.map var nat} {var_idx_map_ok : map.ok var_idx_map}.
Context {var_node_set : map.map var unit} {var_node_set_ok : map.ok var_node_set}.
Context {var_edge_set : map.map var var_node_set}.
Context {Node : Type}.
Context {node_id : Type}
        {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.
Context {node_id_set : map.map node_id unit}.
Context {node_id_set_ok : map.ok node_id_set}.
Context {node_id_edge_set : map.map node_id node_id_set}.
Context {node_id_edge_set_ok : map.ok node_id_edge_set}.
Context {forwarding_table : map.map rel_id (list (@DistributedHardwareProgram.destination node_id))}.
Context {rel_dependency_map : map.map rel_id node_id_set}.
Context {fn_id_map : map.map fn fn_id}.
Context {rel_relid_map : map.map rel rel_id}.
Context {layout_map : map.map node_id (@HardwareProgram.program rel var fn aggregator)}
        {layout_map_ok : map.ok layout_map}.
Context {lowered_layout_map : map.map node_id (@HardwareProgram.lowered_program var aggregator)}
        {lowered_layout_map_ok : map.ok lowered_layout_map}.
Context {node_ftable_map : map.map node_id forwarding_table}.
Context {fact_locations_map : map.map rel (list node_id)}
        {fact_locations_map_ok : map.ok fact_locations_map}.
Context {lowered_fact_locations_map : map.map rel_id (list node_id)}
        {lowered_fact_locations_map_ok : map.ok lowered_fact_locations_map}.

Notation node_graph := (@DistributedDatalogToHardwareCompiler.node_graph node_id node_id_set node_id_edge_set).
Notation get_path := (@ComputableGraph.get_path node_id node_id_eqb node_id_set node_id_edge_set).
Notation graph_fuel := (@ComputableGraphComplete.graph_fuel node_id node_id_set node_id_edge_set).

(* fold congruence: map folds with pointwise-equal step functions agree. *)
Lemma map_fold_ext {K V R} {M : map.map K V} {Mok : map.ok M}
    (f1 f2 : R -> K -> V -> R) (r : R) (m : M) :
  (forall acc k v, f1 acc k v = f2 acc k v) ->
  map.fold f1 r m = map.fold f2 r m.
Proof.
  intros Hf. apply (map.fold_two_spec (fun _ a b => a = b) f1 f2 r r); [reflexivity|].
  intros k v m0 r1 r2 _ Heq. subst. apply Hf.
Qed.

(* The topology path search is fuel-stable above graph_fuel = #nodes (any valid, nonempty graph). *)
Lemma get_path_stable (g : node_graph) (a b : node_id) (f f' : nat) :
  ComputableGraph.check_graph_valid g = true ->
  0 < graph_fuel g ->
  graph_fuel g <= f -> graph_fuel g <= f' ->
  get_path g a b f = get_path g a b f'.
Proof.
  intros Hv Hnz Hf Hf'.
  transitivity (get_path g a b (graph_fuel g)).
  - symmetry. unfold ComputableGraph.get_path.
    apply ComputableGraphComplete.bfs_graph_fuel_stable; assumption.
  - unfold ComputableGraph.get_path.
    apply ComputableGraphComplete.bfs_graph_fuel_stable; assumption.
Qed.

Notation global_context :=
  (@DistributedDatalogToHardwareCompiler.global_context rel fn Node node_id node_id_set rel_dependency_map fn_id_map rel_relid_map).
Notation lowered_fact_locations :=
  (@DistributedDatalogToHardwareCompiler.lowered_fact_locations node_id lowered_fact_locations_map).
Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).

(* list-combinator congruences (used to push fuel-stability through the gates) *)
Lemma forallb_ext {A} (f1 f2 : A -> bool) (l : list A) :
  (forall x, f1 x = f2 x) -> forallb f1 l = forallb f2 l.
Proof. intros H. induction l; cbn; [reflexivity | rewrite H, IHl; reflexivity]. Qed.

Lemma existsb_ext {A} (f1 f2 : A -> bool) (l : list A) :
  (forall x, f1 x = f2 x) -> existsb f1 l = existsb f2 l.
Proof. intros H. induction l; cbn; [reflexivity | rewrite H, IHl; reflexivity]. Qed.

Lemma fold_left_ext {A B} (f1 f2 : A -> B -> A) (l : list B) (a : A) :
  (forall acc x, f1 acc x = f2 acc x) -> fold_left f1 l a = fold_left f2 l a.
Proof. intros H. revert a. induction l; cbn; intros; [reflexivity | rewrite H; apply IHl]. Qed.

(* ----- each fuel-using gate of compile only touches fuel inside [get_path], so it is
   fuel-stable above graph_fuel ----- *)

Lemma routes_validb_stable (gcontext : global_context) (g : node_graph)
    (llayout : lowered_layout_map) (f f' : nat) :
  check_graph_valid g = true -> 0 < graph_fuel g -> graph_fuel g <= f -> graph_fuel g <= f' ->
  routes_validb (node_id_eqb := node_id_eqb) gcontext g f llayout = routes_validb (node_id_eqb := node_id_eqb) gcontext g f' llayout.
Proof.
  intros Hv Hnz Hf Hf'. unfold routes_validb.
  apply forallb_ext; intro np. apply forallb_ext; intro rule_np. apply forallb_ext; intro R.
  f_equal. apply forallb_ext; intro nc. destruct (existsb _ _); [|reflexivity].
  rewrite (get_path_stable g np nc f f' Hv Hnz Hf Hf'). reflexivity.
Qed.

Lemma output_routesb_stable (gcontext : global_context) (g : node_graph)
    (llayout : lowered_layout_map) (lfc : lowered_fact_locations) (f f' : nat) :
  check_graph_valid g = true -> 0 < graph_fuel g -> graph_fuel g <= f -> graph_fuel g <= f' ->
  output_routesb (node_id_eqb := node_id_eqb) gcontext g f llayout lfc = output_routesb (node_id_eqb := node_id_eqb) gcontext g f' llayout lfc.
Proof.
  intros Hv Hnz Hf Hf'. unfold output_routesb.
  apply forallb_ext; intro np. apply forallb_ext; intro rule_np. apply forallb_ext; intro R.
  f_equal. apply existsb_ext; intro no.
  rewrite (get_path_stable g np no f f' Hv Hnz Hf Hf'). reflexivity.
Qed.

Lemma input_routes_validb_stable (gcontext : global_context) (g : node_graph)
    (llayout : lowered_layout_map) (lfp : lowered_fact_locations) (f f' : nat) :
  check_graph_valid g = true -> 0 < graph_fuel g -> graph_fuel g <= f -> graph_fuel g <= f' ->
  input_routes_validb (node_id_eqb := node_id_eqb) gcontext g f llayout lfp = input_routes_validb (node_id_eqb := node_id_eqb) gcontext g f' llayout lfp.
Proof.
  intros Hv Hnz Hf Hf'. unfold input_routes_validb.
  apply map_fold_ext. intros acc R locs. f_equal.
  apply forallb_ext; intro ni. f_equal. apply forallb_ext; intro nc.
  destruct (existsb _ _); [|reflexivity].
  rewrite (get_path_stable g ni nc f f' Hv Hnz Hf Hf'). reflexivity.
Qed.

Lemma input_output_routesb_stable (gcontext : global_context) (g : node_graph)
    (lfp lfc : lowered_fact_locations) (f f' : nat) :
  check_graph_valid g = true -> 0 < graph_fuel g -> graph_fuel g <= f -> graph_fuel g <= f' ->
  input_output_routesb (node_id_eqb := node_id_eqb) gcontext g f lfp lfc = input_output_routesb (node_id_eqb := node_id_eqb) gcontext g f' lfp lfc.
Proof.
  intros Hv Hnz Hf Hf'. unfold input_output_routesb.
  apply map_fold_ext. intros acc R locs. f_equal.
  apply forallb_ext; intro ni. f_equal. apply existsb_ext; intro no.
  rewrite (get_path_stable g ni no f f' Hv Hnz Hf Hf'). reflexivity.
Qed.

Notation fact_locations := (@DistributedDatalogToHardwareCompiler.fact_locations rel node_id fact_locations_map).
Notation lower_inputs :=
  (@DistributedDatalogToHardwareCompiler.lower_inputs rel var fn aggregator Node node_id node_id_set
     rel_dependency_map fn_id_map rel_relid_map layout_map lowered_layout_map fact_locations_map lowered_fact_locations_map).
Notation compile_lowered :=
  (@DistributedDatalogToHardwareCompiler.compile_lowered rel var fn aggregator var_eqb Node node_id node_id_eqb
     node_id_set forwarding_table rel_dependency_map fn_id_map rel_relid_map lowered_layout_map lowered_fact_locations_map var_node_set
     var_edge_set node_id_edge_set var_idx_map node_ftable_map).
Notation compile :=
  (@DistributedDatalogToHardwareCompiler.compile rel var fn aggregator var_eqb Node node_id node_id_eqb node_id_set forwarding_table
     rel_dependency_map fn_id_map rel_relid_map layout_map lowered_layout_map fact_locations_map lowered_fact_locations_map var_node_set
     var_edge_set node_id_edge_set var_idx_map node_ftable_map).

(* ----- the forwarding TABLE (the actual map value built into the success result) is fuel-stable ----- *)

Lemma uftfr_stable (rel0 : rel_id) (gcontext : global_context) (ninfos : list node_info)
    (ftables : node_ftable_map) (g : node_graph) (f f' : nat) :
  check_graph_valid g = true -> 0 < graph_fuel g -> graph_fuel g <= f -> graph_fuel g <= f' ->
  update_forwarding_table_for_rel (node_id_eqb := node_id_eqb) rel0 gcontext ninfos ftables f g
  = update_forwarding_table_for_rel (node_id_eqb := node_id_eqb) rel0 gcontext ninfos ftables f' g.
Proof.
  intros Hv Hnz Hf Hf'. unfold update_forwarding_table_for_rel.
  apply map_fold_ext; intros ft producer _.
  apply map_fold_ext; intros ft2 consumer _.
  destruct (node_id_eqb producer consumer); [reflexivity|].
  rewrite (get_path_stable g producer consumer f f' Hv Hnz Hf Hf'). reflexivity.
Qed.

Lemma gft_stable (gcontext : global_context) (ninfos : list node_info) (g : node_graph) (f f' : nat) :
  check_graph_valid g = true -> 0 < graph_fuel g -> graph_fuel g <= f -> graph_fuel g <= f' ->
  generate_forwarding_table (node_id_eqb := node_id_eqb) gcontext ninfos g f
  = generate_forwarding_table (node_id_eqb := node_id_eqb) gcontext ninfos g f'.
Proof.
  intros Hv Hnz Hf Hf'. unfold generate_forwarding_table.
  apply fold_left_ext; intros ftables rel0. apply uftfr_stable; assumption.
Qed.

Lemma gftc_stable (gcontext : global_context) (ninfos : list node_info) (g : node_graph)
    (llayout : lowered_layout_map) (f f' : nat) :
  check_graph_valid g = true -> 0 < graph_fuel g -> graph_fuel g <= f -> graph_fuel g <= f' ->
  generate_forwarding_table_checked (node_id_eqb := node_id_eqb) gcontext ninfos g f llayout
  = generate_forwarding_table_checked (node_id_eqb := node_id_eqb) gcontext ninfos g f' llayout.
Proof.
  intros Hv Hnz Hf Hf'. unfold generate_forwarding_table_checked.
  rewrite (routes_validb_stable gcontext g llayout f f' Hv Hnz Hf Hf').
  rewrite (gft_stable gcontext ninfos g f f' Hv Hnz Hf Hf'). reflexivity.
Qed.

(* ----- compile itself is fuel-stable above graph_fuel ----- *)

Lemma compile_lowered_stable (llayout : lowered_layout_map) (lfp lfc : lowered_fact_locations)
    (gcontext0 : global_context) (g : node_graph) (f f' : nat) :
  check_graph_valid g = true -> 0 < graph_fuel g -> graph_fuel g <= f -> graph_fuel g <= f' ->
  compile_lowered llayout lfp lfc gcontext0 g f = compile_lowered llayout lfp lfc gcontext0 g f'.
Proof.
  intros Hv Hnz Hf Hf'. unfold DistributedDatalogToHardwareCompiler.compile_lowered.
  rewrite Hv. cbn match.
  destruct (layout_in_graphb g llayout); [|reflexivity]. cbn match.
  destruct (compile_all_nodes llayout (collect_global_dependencies llayout lfp lfc gcontext0))
    as [ninfos|e]; [|reflexivity]. cbn match.
  rewrite (gftc_stable (collect_global_dependencies llayout lfp lfc gcontext0) ninfos g llayout f f' Hv Hnz Hf Hf').
  destruct (generate_forwarding_table_checked (node_id_eqb := node_id_eqb)
              (collect_global_dependencies llayout lfp lfc gcontext0) ninfos g f' llayout)
    as [ftables|e]; [|reflexivity]. cbn match.
  rewrite (input_routes_validb_stable (collect_global_dependencies llayout lfp lfc gcontext0) g llayout lfp f f' Hv Hnz Hf Hf').
  rewrite (output_routesb_stable (collect_global_dependencies llayout lfp lfc gcontext0) g llayout lfc f f' Hv Hnz Hf Hf').
  rewrite (input_output_routesb_stable (collect_global_dependencies llayout lfp lfc gcontext0) g lfp lfc f f' Hv Hnz Hf Hf').
  reflexivity.
Qed.

Lemma compile_stable (layout : layout_map) (fps fcs : fact_locations) (g : node_graph) (f f' : nat) :
  check_graph_valid g = true -> 0 < graph_fuel g -> graph_fuel g <= f -> graph_fuel g <= f' ->
  compile layout fps fcs g f = compile layout fps fcs g f'.
Proof.
  intros Hv Hnz Hf Hf'. unfold DistributedDatalogToHardwareCompiler.compile.
  destruct (lower_inputs layout fps fcs) as [[[[llayout lfp] lfc] gcontext0]|e]; [|reflexivity].
  cbn match. apply compile_lowered_stable; assumption.
Qed.

(* ADEQUATE FUEL: whatever any fuel >= graph_fuel compiles, the COMPUTED graph_fuel compiles
   identically.  This discharges the [compile ... fuel = Success ninfos] hypothesis of
   [compile_implements_source] at the computed fuel -- no hand-tuned fuel constant needed. *)
Corollary adequate_fuel (layout : layout_map) (fps fcs : fact_locations) (g : node_graph)
    (f : nat) (ninfos : list node_info) :
  check_graph_valid g = true -> 0 < graph_fuel g -> graph_fuel g <= f ->
  compile layout fps fcs g f = Success ninfos ->
  compile layout fps fcs g (graph_fuel g) = Success ninfos.
Proof.
  intros Hv Hnz Hf Hcomp.
  rewrite (compile_stable layout fps fcs g (graph_fuel g) f Hv Hnz (le_n (graph_fuel g)) Hf).
  exact Hcomp.
Qed.

(* This is the capstone the top-level theorem needs.  [compile_implements_source] is conditioned on
   [compile layout fps fcs g fuel = Success ninfos]; [adequate_fuel] discharges exactly that
   hypothesis at the COMPUTED fuel [graph_fuel g].  So, given a run that compiles at some adequate
   fuel [f] (>= #nodes), the end-to-end correctness theorem holds verbatim at [graph_fuel g] -- with
   no hand-tuned fuel constant -- by:

     apply (compile_implements_source layout fps fcs g (graph_fuel g) ninfos ...);
       [ apply (adequate_fuel layout fps fcs g f ninfos Hv Hnz Hf Hcomp) | assumption.. ].

   (We do not restate it as a standalone theorem here only because [compile_implements_source]'s
   conclusion uses section-Local notations like [run_ninfos] that don't escape [CompileTop].) *)

End AdequateFuel.
