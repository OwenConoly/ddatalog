(* Fuel-stability for the topology path-finder (get_path = bfs).

   ComputableGraph.v proves SOUNDNESS (a returned path is a real edge-walk: [get_path_spec]).
   This file proves the BFS path search is INSENSITIVE to fuel above a computable bound:
   [graph_fuel g = #nodes(g)] is always enough, so raising the fuel never changes the answer.  That
   justifies fixing the routing fuel to #nodes -- both StringGridCompiler.grid_fuel and the fuel-free
   compiler entry point [compile] (see [bfs_graph_fuel_stable]).

   Strategy (potential argument):
     Phi(st) := (#nodes(g) - #visited(st)) + length(queue(st)).
     Each non-terminal bfs_step pops one entry (queue -1) and enqueues the popped node's k UNVISITED
     neighbors, marking them visited (queue +k, visited +k). So Phi changes by (-k) + (k-1) = -1: it
     drops by EXACTLY 1 each step, starts at #nodes (visited={start}, queue=[start]), and is >= 0.
     Hence the queue empties (or the target is found) within #nodes steps -- so with fuel >= #nodes the
     search never stops early for lack of fuel, and any larger fuel yields the same result. *)

From coqutil Require Import Map.Interface Map.Properties Eqb.
From Stdlib Require Import List Lia PeanoNat.
From DatalogRocq Require Import ComputableGraph.
From DatalogRocq Require Topologies.Graph.   (* qualified only: avoid clashing Graph.nodes with ComputableGraph.nodes *)
Import ListNotations.

Section Complete.
Context {Node : Type}.
Context {node_eqb : Eqb Node} {node_eqb_ok : Eqb_ok node_eqb}.
Context {node_set : map.map Node unit}.
Context {node_set_ok : map.ok node_set}.
Context {edge_set : map.map Node node_set}.
Context {edge_set_ok : map.ok edge_set}.

Local Notation ComputableGraph := (@ComputableGraph Node node_set edge_set).
Local Notation bfs_state := (@bfs_state Node node_set).
Local Notation bfs_step := (@bfs_step Node node_eqb node_set edge_set).
Local Notation bfs_aux := (@bfs_aux Node node_eqb node_set edge_set).
Local Notation bfs := (@bfs Node node_eqb node_set edge_set).

(* ----- node-set cardinality (for the potential) ----- *)

(* Cardinality via a counting fold (f ignores keys/values, so f_comm is trivial and fold_put/
   fold_empty apply directly -- unlike length(keys), whose cons-fold isn't commutative). *)
Lemma msize_empty : msize (map.empty : node_set) = 0.
Proof. unfold msize. apply map.fold_empty. Qed.

Lemma msize_put (m : node_set) (k : Node) (v : unit) :
  map.get m k = None -> msize (map.put m k v) = S (msize m).
Proof.
  intros H. unfold msize.
  rewrite (map.fold_put (fun n _ _ => S n) (fun r k1 v1 k2 v2 => eq_refl) 0 m k v H).
  reflexivity.
Qed.

Lemma msize_remove (m : node_set) (k : Node) (v : unit) :
  map.get m k = Some v -> msize m = S (msize (map.remove m k)).
Proof.
  intros H. unfold msize.
  rewrite (map.fold_remove (fun n _ _ => S n) (fun r k1 v1 k2 v2 => eq_refl) 0 m k v H).
  reflexivity.
Qed.

(* Submap cardinality: a key-subset has no more bindings. Drives Phi >= 0 (visited subset of
   nodes => msize visited <= msize nodes). Proved by fold induction on [a], peeling [a]'s key
   off [b] with msize_remove and recursing on [remove b k]. *)
Lemma msize_le_of_subset (a b : node_set) :
  (forall k v, map.get a k = Some v -> map.get b k = Some v) ->
  msize a <= msize b.
Proof.
  revert b. unfold msize at 1.
  apply (map.fold_spec
    (fun a_sub n => forall b,
       (forall k v, map.get a_sub k = Some v -> map.get b k = Some v) -> n <= msize b)).
  - intros b _. apply Nat.le_0_l.
  - intros k v m n Hmk IH b Hsub.
    assert (Hbk : map.get b k = Some v) by (apply (Hsub k v); apply map.get_put_same).
    rewrite (msize_remove b k v Hbk). apply le_n_S. apply IH.
    intros k' v' Hm.
    destruct (eqb_boolspec _ k' k) as [->|Hne].
    + rewrite Hmk in Hm; discriminate.
    + rewrite (map.get_remove_diff b k' k Hne).
      apply (Hsub k' v').
      rewrite (map.get_put_diff m k' v k Hne).
      exact Hm.
Qed.

(* The neighbor-fold in bfs_step grows [visited] by exactly the number of unvisited neighbors
   it returns. (This is the visited-side of the potential argument.) *)
Lemma bfs_fold_visited_size (neighbors visited : node_set) :
  let r := map.fold (fun '(uvs, vis) n _ =>
             match map.get vis n with
             | Some _ => (uvs, vis)
             | None => (n :: uvs, map.put vis n tt)
             end) ([], visited) neighbors in
  msize (snd r) = msize visited + length (fst r).
Proof.
  apply (map.fold_spec (fun _ acc => msize (snd acc) = msize visited + length (fst acc))).
  - cbn. lia.
  - intros k v m [uvs vis] _ IH. cbn [fst snd] in IH |- *.
    destruct (map.get vis k) eqn:E; cbn [fst snd length].
    + exact IH.
    + rewrite (msize_put vis k tt E). cbn [length]. lia.
Qed.

(* ----- invariant: visited stays within the graph's node set (drives Phi >= 0) ----- *)

Definition visited_sub (vis ns : node_set) : Prop :=
  forall k, map.get vis k <> None -> map.get ns k <> None.

Lemma msize_le_visited_sub (vis ns : node_set) :
  visited_sub vis ns -> msize vis <= msize ns.
Proof.
  intros H. apply msize_le_of_subset. intros k v Hv.
  assert (Hne : map.get ns k <> None) by (apply H; rewrite Hv; discriminate).
  destruct (map.get ns k) as [u|] eqn:E; [destruct u, v; reflexivity | congruence].
Qed.

(* every key of the neighbor-fold's new visited set is either old or a neighbor key *)
Lemma fold_new_visited (neighbors vis0 : node_set) (k : Node) :
  map.get (snd (map.fold (fun '(uvs, vis) n _ =>
             match map.get vis n with
             | Some _ => (uvs, vis)
             | None => (n :: uvs, map.put vis n tt)
             end) ([], vis0) neighbors)) k <> None ->
  map.get vis0 k <> None \/ (exists v, map.get neighbors k = Some v).
Proof.
  apply (map.fold_spec
    (fun (m : node_set) (acc : list Node * node_set) =>
       map.get (snd acc) k <> None ->
       map.get vis0 k <> None \/ (exists v, map.get m k = Some v))).
  - cbn. intros H. left. exact H.
  - intros j w m acc Hmj IH. destruct acc as [uvs vis]. cbn [snd] in IH.
    destruct (map.get vis j) eqn:E; cbn [snd]; intros H.
    + destruct (IH H) as [Hl | [v Hv]]; [left; exact Hl | right; exists v].
      destruct (eqb_boolspec _ k j) as [->|Hne].
      * rewrite Hmj in Hv; discriminate.
      * rewrite (map.get_put_diff m k w j Hne); exact Hv.
    + destruct (eqb_boolspec _ k j) as [->|Hne].
      * right; exists w. apply map.get_put_same.
      * rewrite (map.get_put_diff vis k tt j Hne) in H.
        destruct (IH H) as [Hl | [v Hv]]; [left; exact Hl | right; exists v].
        rewrite (map.get_put_diff m k w j Hne); exact Hv.
Qed.

(* graph validity: a neighbor of any node is itself a node *)
Lemma neighbor_in_nodes (g : ComputableGraph) (node k : Node) (v : unit) :
  check_graph_valid g = true ->
  map.get (cg_neighbors g node) k = Some v ->
  map.get g.(nodes) k <> None.
Proof.
  intros Hvalid Hnb.
  pose proof (cg_neighbors_edge g node k v Hnb) as Hedge.
  apply check_graph_correct in Hvalid.
  destruct (Hvalid node k Hedge) as [_ Hkv].
  unfold computable_graph_to_graph, check_node_valid in Hkv. cbn in Hkv.
  destruct (map.get g.(nodes) k) as [u|] eqn:E; congruence.
Qed.

(* the neighbor-fold preserves [visited_sub] (given a valid graph) *)
Lemma visited_sub_step (g : ComputableGraph) (node : Node) (vis0 : node_set) :
  check_graph_valid g = true ->
  visited_sub vis0 g.(nodes) ->
  visited_sub (snd (map.fold (fun '(uvs, vis) n _ =>
             match map.get vis n with
             | Some _ => (uvs, vis)
             | None => (n :: uvs, map.put vis n tt)
             end) ([], vis0) (cg_neighbors g node))) g.(nodes).
Proof.
  intros Hvalid Hsub k Hk.
  destruct (fold_new_visited (cg_neighbors g node) vis0 k Hk) as [Hold | [v Hnb]].
  - apply Hsub; exact Hold.
  - eapply neighbor_in_nodes; eauto.
Qed.

(* A non-terminal bfs_step (head <> target) pops the head and enqueues [U] freshly-visited
   neighbors: visited grows by U (staying within nodes), queue (S (length rest)) -> (length rest + U). *)
Lemma bfs_step_nonterminal (g : ComputableGraph) (target node : Node)
      (p : list Node) (rest : list (Node * list Node)) (st : bfs_state) :
  st.(bs_queue) = (node, p) :: rest ->
  node_eqb node target = false ->
  check_graph_valid g = true ->
  visited_sub st.(bs_visited) g.(nodes) ->
  exists st' U,
    bfs_step g target st = inl st' /\
    msize st'.(bs_visited) = msize st.(bs_visited) + U /\
    length st'.(bs_queue) = length rest + U /\
    visited_sub st'.(bs_visited) g.(nodes).
Proof.
  intros Hq Hne Hvalid Hsub.
  pose proof (bfs_fold_visited_size (cg_neighbors g node) st.(bs_visited)) as Hsz.
  pose proof (visited_sub_step g node st.(bs_visited) Hvalid Hsub) as Hvs.
  destruct (map.fold (fun '(uvs, vis) n _ =>
              match map.get vis n with
              | Some _ => (uvs, vis)
              | None => (n :: uvs, map.put vis n tt)
              end) ([], st.(bs_visited)) (cg_neighbors g node))
    as [unvisited new_visited] eqn:Hfold.
  cbn [fst snd] in Hsz, Hvs.
  exists {| bs_queue := rest ++ List.map (fun n => (n, n :: p)) unvisited;
            bs_visited := new_visited |}, (length unvisited).
  split; [| split; [| split]].
  - unfold bfs_step. rewrite Hq, Hne, Hfold. reflexivity.
  - cbn. exact Hsz.
  - cbn. rewrite length_app, length_map. reflexivity.
  - cbn. exact Hvs.
Qed.

(* ----- fuel-stability: once fuel >= Phi(state), the bfs result is independent of fuel.
   Phi(st) = (#unvisited nodes) + (queue length) drops by exactly 1 each non-terminal step
   and is >= 0, so by Phi(initial) = #nodes steps the search has either found the target or
   emptied the queue -- it never bails out for lack of fuel. Hence grid_fuel = #nodes is enough:
   compiling with it gives the same verified result as with any larger fuel. ----- *)

Definition Phi (g : ComputableGraph) (st : bfs_state) : nat :=
  (msize g.(nodes) - msize st.(bs_visited)) + length st.(bs_queue).

Lemma bfs_step_empty (g : ComputableGraph) (target : Node) (st : bfs_state) :
  st.(bs_queue) = [] -> bfs_step g target st = inl st.
Proof. intros Hq. unfold bfs_step. rewrite Hq. reflexivity. Qed.

Lemma bfs_aux_empty (g : ComputableGraph) (target : Node) (st : bfs_state) (fuel : nat) :
  st.(bs_queue) = [] -> bfs_aux g target st fuel = None.
Proof.
  intros Hq. destruct fuel as [|f]; [reflexivity|].
  cbn [bfs_aux]. rewrite (bfs_step_empty g target st Hq). cbn. rewrite Hq. reflexivity.
Qed.

Lemma bfs_aux_step_empty (g : ComputableGraph) (target : Node) (st st' : bfs_state) (fuel : nat) :
  bfs_step g target st = inl st' -> st'.(bs_queue) = [] ->
  bfs_aux g target st (S fuel) = None.
Proof. intros Hstep Hq'. cbn [bfs_aux]. rewrite Hstep. cbn. rewrite Hq'. reflexivity. Qed.

Lemma bfs_aux_step_cons (g : ComputableGraph) (target : Node) (st st' : bfs_state)
      (e : Node * list Node) (q : list (Node * list Node)) (fuel : nat) :
  bfs_step g target st = inl st' -> st'.(bs_queue) = e :: q ->
  bfs_aux g target st (S fuel) = bfs_aux g target st' fuel.
Proof. intros Hstep Hq'. cbn [bfs_aux]. rewrite Hstep. cbn. rewrite Hq'. reflexivity. Qed.

Lemma bfs_aux_stable (g : ComputableGraph) (target : Node) :
  check_graph_valid g = true ->
  forall fuel st, visited_sub st.(bs_visited) g.(nodes) -> Phi g st <= fuel ->
  forall fuel', Phi g st <= fuel' ->
  bfs_aux g target st fuel = bfs_aux g target st fuel'.
Proof.
  intros Hvalid fuel.
  induction fuel as [|fuel IH]; intros st Hsub Hfuel fuel' Hfuel'.
  - assert (Hq : st.(bs_queue) = []).
    { unfold Phi in Hfuel. destruct (bs_queue st) eqn:E; [reflexivity | cbn in Hfuel; lia]. }
    rewrite (bfs_aux_empty g target st 0 Hq), (bfs_aux_empty g target st fuel' Hq). reflexivity.
  - destruct (bs_queue st) as [|[node p] rest] eqn:Hq.
    + rewrite (bfs_aux_empty g target st (S fuel) Hq), (bfs_aux_empty g target st fuel' Hq). reflexivity.
    + assert (Hpos : fuel' <> 0).
      { intro; subst. unfold Phi in Hfuel'. rewrite Hq in Hfuel'. cbn in Hfuel'. lia. }
      destruct fuel' as [|f']; [exfalso; apply Hpos; reflexivity|].
      destruct (node_eqb node target) eqn:Htgt.
      * assert (Hb : bfs_step g target st = inr (List.rev p))
          by (unfold bfs_step; rewrite Hq, Htgt; reflexivity).
        cbn [bfs_aux]. rewrite Hb. reflexivity.
      * destruct (bfs_step_nonterminal g target node p rest st Hq Htgt Hvalid Hsub)
          as [st' [U [Hstep [Hvis [Hlen Hsub']]]]].
        assert (Hbound : msize st'.(bs_visited) <= msize g.(nodes))
          by (apply msize_le_visited_sub; exact Hsub').
        assert (Hphi : Phi g st' + 1 = Phi g st).
        { unfold Phi. rewrite Hvis, Hlen, Hq. cbn [length]. rewrite Hvis in Hbound. lia. }
        destruct (bs_queue st') as [|e q] eqn:Hq'.
        -- rewrite (bfs_aux_step_empty g target st st' fuel Hstep Hq'),
                   (bfs_aux_step_empty g target st st' f' Hstep Hq'). reflexivity.
        -- rewrite (bfs_aux_step_cons g target st st' e q fuel Hstep Hq'),
                   (bfs_aux_step_cons g target st st' e q f' Hstep Hq').
           apply IH; [exact Hsub' | lia | lia].
Qed.

(* the BFS core is fuel-stable above #nodes: from the initial state, any two fuels >= #nodes
   give [bfs_aux] the same answer. ([bfs] fixes the fuel to [graph_fuel], so this is stated on
   [bfs_aux] directly.) *)
Lemma bfs_fuel_stable (g : ComputableGraph) (start target : Node) :
  check_graph_valid g = true ->
  map.get g.(nodes) start <> None ->
  forall fuel fuel', msize g.(nodes) <= fuel -> msize g.(nodes) <= fuel' ->
  bfs_aux g target (bfs_initial start) fuel = bfs_aux g target (bfs_initial start) fuel'.
Proof.
  intros Hvalid Hstart fuel fuel' Hf Hf'.
  assert (Hnz : 1 <= msize g.(nodes)).
  { destruct (map.get g.(nodes) start) as [v|] eqn:E; [|congruence].
    rewrite (msize_remove g.(nodes) start v E). lia. }
  assert (Hsub0 : visited_sub (bs_visited (bfs_initial start)) g.(nodes)).
  { unfold bfs_initial, visited_sub. cbn [bs_visited]. intros k Hk.
    destruct (eqb_boolspec _ k start) as [->|Hne]; [exact Hstart|].
    rewrite map.get_put_diff in Hk by (intro; subst; congruence).
    rewrite map.get_empty in Hk. congruence. }
  assert (Hphi0 : Phi g (bfs_initial start) <= msize g.(nodes)).
  { unfold Phi, bfs_initial. cbn [bs_visited bs_queue length].
    rewrite msize_put by apply map.get_empty. rewrite msize_empty. lia. }
  apply (bfs_aux_stable g target Hvalid); [exact Hsub0 | lia | lia].
Qed.

Corollary bfs_fuel_canonical (g : ComputableGraph) (start target : Node) (f : nat) :
  check_graph_valid g = true ->
  map.get g.(nodes) start <> None ->
  msize g.(nodes) <= f ->
  bfs_aux g target (bfs_initial start) (msize g.(nodes)) = bfs_aux g target (bfs_initial start) f.
Proof. intros Hvalid Hstart Hf. apply bfs_fuel_stable; auto. Qed.

(* in a valid graph a non-node has no outgoing edges *)
Lemma cg_neighbors_empty_of_not_node (g : ComputableGraph) (a : Node) :
  check_graph_valid g = true -> map.get g.(nodes) a = None ->
  cg_neighbors g a = map.empty.
Proof.
  intros Hvalid Hna. apply map.map_ext. intros k. rewrite map.get_empty.
  destruct (map.get (cg_neighbors g a) k) as [v|] eqn:E; [exfalso | reflexivity].
  pose proof (cg_neighbors_edge g a k v E) as Hedge.
  apply check_graph_correct in Hvalid.
  destruct (Hvalid a k Hedge) as [Hav _].
  unfold computable_graph_to_graph, check_node_valid in Hav. cbn in Hav.
  rewrite Hna in Hav. discriminate.
Qed.

Lemma bfs_initial_step_no_neighbors (g : ComputableGraph) (b a : Node) :
  cg_neighbors g a = map.empty -> node_eqb a b = false ->
  bfs_step g b (bfs_initial a) = inl {| bs_queue := []; bs_visited := map.put map.empty a tt |}.
Proof.
  intros Hemp Hne. unfold bfs_step, bfs_initial. cbn [bs_queue bs_visited].
  rewrite Hne, Hemp, map.fold_empty. reflexivity.
Qed.

(* a non-node start: the search ends in one step, so its result is fuel-independent (fuel >= 1) *)
Lemma bfs_no_node_stable (g : ComputableGraph) (a b : Node) (f : nat) :
  check_graph_valid g = true -> map.get g.(nodes) a = None -> 1 <= f ->
  bfs_aux g b (bfs_initial a) f = (if node_eqb a b then Some [a] else None).
Proof.
  intros Hvalid Hna Hf.
  pose proof (cg_neighbors_empty_of_not_node g a Hvalid Hna) as Hemp.
  destruct f as [|f']; [lia|]. cbn [bfs_aux].
  destruct (node_eqb a b) eqn:Htgt.
  - assert (Hb : bfs_step g b (bfs_initial a) = inr (List.rev [a]))
      by (unfold bfs_step, bfs_initial; cbn [bs_queue]; rewrite Htgt; reflexivity).
    rewrite Hb. reflexivity.
  - rewrite (bfs_initial_step_no_neighbors g b a Hemp Htgt). reflexivity.
Qed.

(* GENERAL fuel-stability: for ANY valid graph, [graph_fuel = #nodes] is enough -- raising fuel
   beyond it never changes a path search.  ([bfs] itself runs at exactly [graph_fuel].) *)
Lemma bfs_graph_fuel_stable (g : ComputableGraph) (a b : Node) (f : nat) :
  check_graph_valid g = true -> 0 < msize g.(nodes) -> graph_fuel g <= f ->
  bfs_aux g b (bfs_initial a) (graph_fuel g) = bfs_aux g b (bfs_initial a) f.
Proof.
  intros Hvalid Hnz Hf. unfold graph_fuel in *.
  destruct (map.get g.(nodes) a) as [v|] eqn:Ha.
  - apply bfs_fuel_canonical; [exact Hvalid | rewrite Ha; discriminate | exact Hf].
  - assert (Hf1 : 1 <= f) by lia.
    rewrite (bfs_no_node_stable g a b (msize g.(nodes)) Hvalid Ha Hnz).
    rewrite (bfs_no_node_stable g a b f Hvalid Ha Hf1). reflexivity.
Qed.

End Complete.
