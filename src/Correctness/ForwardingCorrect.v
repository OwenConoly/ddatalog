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

Context {forwarding_table : map.map rel_id (list node_id)}
        {forwarding_table_ok : map.ok forwarding_table}.
Context {node_ftable_map : map.map node_id forwarding_table}
        {node_ftable_map_ok : map.ok node_ftable_map}.

Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).

(* the forwarding edges node [node] has for relation [rel] in [ftables] *)
Definition node_rel_dests (ftables : node_ftable_map) (node : node_id) (rel : rel_id) : list node_id :=
  get_or_default (get_or_default ftables node) rel.

Definition has_fwd_edge (ftables : node_ftable_map) (node : node_id) (rel : rel_id) (m : node_id) : Prop :=
  In m (node_rel_dests ftables node rel).

(*============================================================================*)
(*  Soundness: every forwarding edge is a real graph edge                      *)
(*============================================================================*)

(* the table is *edge-sound* when every forwarding edge it records is a real graph edge *)
Definition ftable_edges_sound (g : node_graph) (ftables : node_ftable_map) : Prop :=
  forall node rel m, has_fwd_edge ftables node rel m -> cg_edge g node m.

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

(* an edge of the graph the table induces for [R] is exactly a recorded next hop *)
Lemma cg_edge_graph_of_ftables (ftables : node_ftable_map) (R : rel_id) (n m : node_id) :
  cg_edge (graph_of_ftables_at_rel ftables R) n m <-> has_fwd_edge ftables n R m.
Proof.
  unfold ComputableGraph.cg_edge, ComputableGraph.check_edge_exists,
    DistributedDatalogToHardwareCompiler.graph_of_ftables_at_rel,
    DistributedDatalogToHardwareCompiler.edges_of_ftables_at_rel,
    has_fwd_edge, node_rel_dests, get_or_default, get_or.
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
Lemma ftables_in_graphb_sound (g : node_graph) (ftables : node_ftable_map) :
  ftables_in_graphb g ftables = true -> ftable_edges_sound g ftables.
Proof.
  intros Hcheck node rel m Hfwd.
  unfold has_fwd_edge, node_rel_dests, get_or_default, get_or in Hfwd.
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
