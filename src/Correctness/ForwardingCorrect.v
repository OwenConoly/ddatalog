(* Phase B of the forwarding-table verification: [add_path_to_forwarding_table] lays down a
   [DestEdge] chain along its path, and the whole construction is monotone (adding never removes
   an existing forwarding edge).  These are the per-step facts Phase C assembles, together with
   [ComputableGraph.get_path_spec] (paths are real edge-walks), into [good_network_streaming] for
   the compiled network's own forwarding tables. *)

From Stdlib Require Import List Bool Lia PeanoNat.
From coqutil Require Import Map.Interface Map.Properties Datatypes.ListSet Eqb Tactics.destr.
From Datalog Require Import Map Default.
From DatalogRocq Require Import DistributedDatalogToHardwareCompiler HardwareProgram DistributedHardwareProgram ComputableGraph.
Import ListNotations.

Section ForwardingCorrect.

Context {node_id : Type}.
Context {node_id_eqb : Eqb node_id} {node_id_eqb_ok : Eqb_ok node_id_eqb}.
Context {node_id_set : map.map node_id unit} {node_id_set_ok : map.ok node_id_set}.
Context {node_id_edge_set : map.map node_id node_id_set} {node_id_edge_set_ok : map.ok node_id_edge_set}.

Notation node_graph := (@ComputableGraph.ComputableGraph node_id node_id_set node_id_edge_set).
Notation cg_edge := (@ComputableGraph.cg_edge node_id node_id_set node_id_edge_set).

Notation destination := (@DistributedHardwareProgram.destination node_id).
Context {forwarding_table : map.map rel_id (list destination)}
        {forwarding_table_ok : map.ok forwarding_table}.
Context {node_ftable_map : map.map node_id forwarding_table}
        {node_ftable_map_ok : map.ok node_ftable_map}.

Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).
Notation get_node_ftable node ftables := (get_or_default ftables node).

(* the [DestEdge] targets among a destination list *)
Definition dest_edges (ds : list destination) : list node_id :=
  flat_map (fun d => match d with
                     | DistributedHardwareProgram.DestEdge n => [n]
                     | DistributedHardwareProgram.DestTrie _ => [] end) ds.

(* [x] is a [DestEdge] target of [ds] iff [DestEdge x] is literally in [ds]. *)
Lemma In_dest_edges (x : node_id) (ds : list destination) :
  In x (dest_edges ds) <-> In (DistributedHardwareProgram.DestEdge x) ds.
Proof.
  unfold dest_edges. rewrite in_flat_map. split.
  - intros [d [Hin Hx]]. destruct d as [n|t]; cbn in Hx; [|destruct Hx].
    destruct Hx as [<-|[]]. exact Hin.
  - intros Hin. exists (DistributedHardwareProgram.DestEdge x). split; [exact Hin | left; reflexivity].
Qed.

(* the forwarding edges node [node] has for relation [rel] in [ftables] *)
Definition node_rel_dests (ftables : node_ftable_map) (node : node_id) (rel : rel_id) : list destination :=
  match map.get (get_node_ftable node ftables) rel with Some ds => ds | None => [] end.

Definition has_fwd_edge (ftables : node_ftable_map) (node : node_id) (rel : rel_id) (m : node_id) : Prop :=
  In m (dest_edges (node_rel_dests ftables node rel)).

(*============================================================================*)
(*  Soundness: every forwarding edge is a real graph edge                      *)
(*============================================================================*)

(* the table is *edge-sound* when every forwarding edge it records is a real graph edge *)
Definition ftable_edges_sound (g : node_graph) (ftables : node_ftable_map) : Prop :=
  forall node rel m, has_fwd_edge ftables node rel m -> cg_edge g node m.


Context {internode_forwarding_table : map.map rel_id (list node_id)}
        {internode_forwarding_table_ok : map.ok internode_forwarding_table}.
Context {internode_forwarding_tables : map.map node_id internode_forwarding_table}
        {internode_forwarding_tables_ok : map.ok internode_forwarding_tables}.

Notation ftables_in_graphb := (@DistributedDatalogToHardwareCompiler.ftables_in_graphb node_id node_id_set node_id_edge_set internode_forwarding_table internode_forwarding_tables).
Notation graph_of_ftables_at_rel := (@DistributedDatalogToHardwareCompiler.graph_of_ftables_at_rel node_id node_id_set node_id_edge_set internode_forwarding_table internode_forwarding_tables).
Notation compute_forwarding_table := (@DistributedDatalogToHardwareCompiler.compute_forwarding_table node_id forwarding_table node_ftable_map internode_forwarding_table internode_forwarding_tables).

(* the hops the external table records for [R] at [n]: the single notion both the induced graph
   and the computed table are built from. *)
Notation next_hops ftables n R := (get_or_default (get_or_default ftables n) R).

Lemma get_map_values {K V1 V2 : Type} {keqb : Eqb K} {keqb_ok : Eqb_ok keqb}
    {M1 : map.map K V1} {M1ok : map.ok M1} {M2 : map.map K V2} {M2ok : map.ok M2}
    (f : V1 -> V2) (m : M1) (k : K) :
  map.get (map.map_values f m : M2) k = option_map f (map.get m k).
Proof.
  unfold map.map_values. revert k.
  eapply (map.fold_spec (fun m acc => forall k, map.get (acc : M2) k = option_map f (map.get m k))).
  - intros k. rewrite !map.get_empty. reflexivity.
  - intros k v m' acc _ IH k0. rewrite !map.get_put_dec. destr (eqb k k0); [reflexivity | apply IH].
Qed.

Lemma get_node_set_of_list (l : list node_id) (m : node_id) :
  map.get (DistributedDatalogToHardwareCompiler.node_set_of_list l : node_id_set) m <> None <-> In m l.
Proof.
  unfold DistributedDatalogToHardwareCompiler.node_set_of_list.
  induction l as [|x l IH]; cbn [List.map map.of_list In].
  - rewrite map.get_empty. split; [congruence | intros []].
  - rewrite map.get_put_dec. destr (eqb x m).
    + split; [intros _; left; reflexivity | congruence].
    + rewrite IH. split; [tauto | intros [Heq|H]; [congruence | exact H]].
Qed.

Lemma dest_edges_app (A B : list destination) :
  dest_edges (A ++ B) = dest_edges A ++ dest_edges B.
Proof. unfold dest_edges. apply flat_map_app. Qed.

Lemma dest_edges_map_edge (l : list node_id) :
  dest_edges (List.map DistributedHardwareProgram.DestEdge l) = l.
Proof. unfold dest_edges. induction l as [|x l IH]; cbn; congruence. Qed.

(* [trie_ftable] only ever stores [DestTrie]s, so it contributes no forwarding edge *)
Lemma trie_ftable_no_edges' (tries : list trie) (R : rel_id) :
  dest_edges (get_or_default (DistributedDatalogToHardwareCompiler.trie_ftable tries : forwarding_table) R) = [].
Proof.
  unfold dest_edges.
  induction tries as [|t tries IH];
    cbn [DistributedDatalogToHardwareCompiler.trie_ftable fold_right].
  - unfold get_or_default, get_or. rewrite map.get_empty. reflexivity.
  - rewrite mupd_with_default_eq_put, get_or_default_put. destr (eqb t.(trel) R).
    + cbn [flat_map app]. exact IH.
    + exact IH.
Qed.

Lemma trie_ftable_no_edges (tries : list trie) (R : rel_id) (ts : list destination) :
  map.get (DistributedDatalogToHardwareCompiler.trie_ftable tries : forwarding_table) R = Some ts ->
  dest_edges ts = [].
Proof.
  intros H. rewrite <- (get_or_default_Some _ _ _ H). apply trie_ftable_no_edges'.
Qed.

Lemma trie_ftables_no_edges (ninfos : list node_info) (n : node_id) (ftt : forwarding_table)
    (R : rel_id) (ts : list destination) :
  map.get (DistributedDatalogToHardwareCompiler.trie_ftables ninfos : node_ftable_map) n = Some ftt ->
  map.get ftt R = Some ts ->
  dest_edges ts = [].
Proof.
  unfold DistributedDatalogToHardwareCompiler.trie_ftables. revert ftt.
  induction ninfos as [|ninfo ninfos IH]; cbn [List.map map.of_list]; intros ftt Hn HR.
  - rewrite map.get_empty in Hn. discriminate.
  - rewrite map.get_put_dec in Hn. destr (eqb ninfo.(nid) n).
    + injection Hn as Hn. subst ftt. exact (trie_ftable_no_edges _ R ts HR).
    + exact (IH ftt Hn HR).
Qed.

(* the computed table forwards [R] out of [n] to exactly the external table's next hops *)
Lemma dest_edges_compute (ftables : internode_forwarding_tables) (ninfos : list node_info)
    (n : node_id) (R : rel_id) :
  dest_edges (node_rel_dests (compute_forwarding_table ftables ninfos) n R) = next_hops ftables n R.
Proof.
  unfold node_rel_dests, DistributedDatalogToHardwareCompiler.compute_forwarding_table,
    get_or_default, get_or, DistributedDatalogToHardwareCompiler.edge_ftables.
  rewrite union_with_get, get_map_values.
  destruct (map.get ftables n) as [ft|] eqn:Hn;
    destruct (map.get (DistributedDatalogToHardwareCompiler.trie_ftables ninfos) n)
      as [ftt|] eqn:Hnt; cbn [option_map default map_default].
  - rewrite union_with_get, get_map_values.
    destruct (map.get ft R) as [hops|] eqn:HR;
      destruct (map.get ftt R) as [ts|] eqn:HtR; cbn [option_map].
    + rewrite dest_edges_app, dest_edges_map_edge, (trie_ftables_no_edges _ _ _ _ _ Hnt HtR).
      apply app_nil_r.
    + apply dest_edges_map_edge.
    + rewrite (trie_ftables_no_edges _ _ _ _ _ Hnt HtR). reflexivity.
    + reflexivity.
  - rewrite get_map_values. destruct (map.get ft R) as [hops|] eqn:HR; cbn [option_map].
    + apply dest_edges_map_edge.
    + reflexivity.
  - cbv [default map_default list_default]. rewrite map.get_empty.
    destruct (map.get ftt R) as [ts|] eqn:HtR.
    + rewrite (trie_ftables_no_edges _ _ _ _ _ Hnt HtR). reflexivity.
    + reflexivity.
  - cbv [default map_default list_default]. rewrite !map.get_empty. reflexivity.
Qed.

Lemma has_fwd_edge_compute (ftables : internode_forwarding_tables) (ninfos : list node_info)
    (n : node_id) (R : rel_id) (m : node_id) :
  has_fwd_edge (compute_forwarding_table ftables ninfos) n R m <-> In m (next_hops ftables n R).
Proof. unfold has_fwd_edge. rewrite dest_edges_compute. reflexivity. Qed.

(* an edge of the graph the table induces for [R] is exactly a recorded next hop *)
Lemma cg_edge_graph_of_ftables (ftables : internode_forwarding_tables) (R : rel_id) (n m : node_id) :
  cg_edge (graph_of_ftables_at_rel ftables R) n m <-> In m (next_hops ftables n R).
Proof.
  unfold ComputableGraph.cg_edge, ComputableGraph.check_edge_exists,
    DistributedDatalogToHardwareCompiler.graph_of_ftables_at_rel,
    DistributedDatalogToHardwareCompiler.edges_of_ftables_at_rel, get_or_default, get_or.
  cbn [ComputableGraph.edges]. rewrite get_map_values.
  destruct (map.get ftables n) as [ft|] eqn:Hn; cbn [option_map].
  - rewrite <- get_node_set_of_list.
    destruct (map.get (DistributedDatalogToHardwareCompiler.node_set_of_list _) m).
    + split; [intros _; congruence | reflexivity].
    + split; [discriminate | intros H; exfalso; apply H; reflexivity].
  - cbv [default map_default list_default]. rewrite map.get_empty.
    split; [discriminate | intros []].
Qed.

(* the decidable check on an externally generated table gives exactly the edge-soundness the
   forwarding proofs used to get from [get_path_spec]. *)
Lemma ftables_in_graphb_sound (g : node_graph) (ftables : internode_forwarding_tables)
    (ninfos : list node_info) :
  ftables_in_graphb g ftables = true ->
  ftable_edges_sound g (compute_forwarding_table ftables ninfos).
Proof.
  intros Hcheck node rel m Hfwd. apply has_fwd_edge_compute in Hfwd.
  unfold get_or_default, get_or in Hfwd.
  destruct (map.get ftables node) as [ft|] eqn:Hnode;
    [| cbv [default map_default list_default] in Hfwd; rewrite map.get_empty in Hfwd; destruct Hfwd].
  pose proof (map.get_forallb _ ftables Hcheck node ft Hnode) as Hft.
  destruct (map.get ft rel) as [hops|] eqn:Hrel; [|destruct Hfwd].
  pose proof (map.get_forallb _ ft Hft rel hops Hrel) as Hhops.
  unfold DistributedDatalogToHardwareCompiler.hops_in_graphb in Hhops.
  rewrite forallb_forall in Hhops. exact (Hhops _ Hfwd).
Qed.

(*============================================================================*)
(*  Phase C2 (completeness engine): a forwarding edge laid down by some step    *)
(*  of the construction survives to the final table.  Generic over an arbitrary *)
(*  monotone table-predicate [P] (instantiated with [fun ft => has_fwd_edge     *)
(*  ft a r b] at the use site), so the same combinators thread both the         *)
(*  [map.fold] over producer/consumer node-sets and the [fold_left] over rels.  *)



End ForwardingCorrect.
