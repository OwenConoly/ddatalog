(* Phase B of the forwarding-table verification: [add_path_to_forwarding_table] lays down a
   [DestEdge] chain along its path, and the whole construction is monotone (adding never removes
   an existing forwarding edge).  These are the per-step facts Phase C assembles, together with
   [ComputableGraph.get_path_spec] (paths are real edge-walks), into [good_network_streaming] for
   the compiled network's own forwarding tables. *)

From Stdlib Require Import List Bool Lia PeanoNat.
From coqutil Require Import Map.Interface Map.Properties.
From DatalogRocq Require Import EncodeLayout HardwareProgram DistributedHardwareProgram ComputableGraph.
Import ListNotations.

Section ForwardingCorrect.

Context {node_id : Type}.
Context {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.
Context {node_id_set : map.map node_id unit} {node_id_set_ok : map.ok node_id_set}.
Context {node_id_edge_set : map.map node_id node_id_set} {node_id_edge_set_ok : map.ok node_id_edge_set}.

Notation node_graph := (@ComputableGraph.ComputableGraph node_id node_id_set node_id_edge_set).
Notation cg_edge := (@ComputableGraph.cg_edge node_id node_id_set node_id_edge_set).
Notation is_path := (@ComputableGraph.is_path node_id node_id_set node_id_edge_set).

Notation destination := (@DistributedHardwareProgram.destination node_id).
Context {forwarding_table : map.map rel_id (list destination)}
        {forwarding_table_ok : map.ok forwarding_table}.
Context {node_ftable_map : map.map node_id forwarding_table}
        {node_ftable_map_ok : map.ok node_ftable_map}.

Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).
Notation get_node_ftable := (@EncodeLayout.get_node_ftable node_id forwarding_table node_ftable_map).
Notation add_dest_if_absent := (@EncodeLayout.add_dest_if_absent node_id node_id_eqb).
Notation add_trie_dest := (@EncodeLayout.add_trie_dest_to_forwarding_table node_id node_id_eqb forwarding_table node_ftable_map).
Notation add_path := (@EncodeLayout.add_path_to_forwarding_table node_id node_id_eqb forwarding_table node_ftable_map).

(* the [DestEdge] targets among a destination list *)
Definition dest_edges (ds : list destination) : list node_id :=
  flat_map (fun d => match d with
                     | DistributedHardwareProgram.DestEdge n => [n]
                     | DistributedHardwareProgram.DestTrie _ => [] end) ds.

(* the forwarding edges node [node] has for relation [rel] in [ftables] *)
Definition node_rel_dests (ftables : node_ftable_map) (node : node_id) (rel : rel_id) : list destination :=
  match map.get (get_node_ftable node ftables) rel with Some ds => ds | None => [] end.

Definition has_fwd_edge (ftables : node_ftable_map) (node : node_id) (rel : rel_id) (m : node_id) : Prop :=
  In m (dest_edges (node_rel_dests ftables node rel)).

(*----dest_edges facts----*)

Lemma dest_edges_cons_edge (n : node_id) (ds : list destination) :
  dest_edges (DistributedHardwareProgram.DestEdge n :: ds) = n :: dest_edges ds.
Proof. reflexivity. Qed.

Lemma dest_edges_cons_trie (t : trie_id) (ds : list destination) :
  dest_edges (DistributedHardwareProgram.DestTrie t :: ds) = dest_edges ds.
Proof. reflexivity. Qed.

Lemma dest_edges_mono (d : destination) (ds : list destination) (x : node_id) :
  In x (dest_edges ds) -> In x (dest_edges (add_dest_if_absent d ds)).
Proof.
  intros H. unfold EncodeLayout.add_dest_if_absent.
  destruct (existsb _ ds); [exact H|]. destruct d; cbn; [right|]; exact H.
Qed.

Lemma dest_edges_add_edge (m : node_id) (ds : list destination) :
  In m (dest_edges (add_dest_if_absent (DistributedHardwareProgram.DestEdge m) ds)).
Proof.
  unfold EncodeLayout.add_dest_if_absent.
  destruct (existsb _ ds) eqn:E.
  - (* DestEdge m already present *)
    apply existsb_exists in E. destruct E as [d [Hin Heq]].
    destruct d as [n|t]; cbn in Heq; [|discriminate].
    destruct (node_id_eqb_spec m n); [subst|discriminate].
    apply in_flat_map. exists (DistributedHardwareProgram.DestEdge n).
    split; [exact Hin | left; reflexivity].
  - cbn. left. reflexivity.
Qed.

(* adding [DestTrie]s preserves the [DestEdge] set (the fold runs over tries via [tid]) *)
Lemma dest_edges_fold_trie {A : Type} (f : A -> trie_id) (l : list A) (ds : list destination) (x : node_id) :
  In x (dest_edges ds) ->
  In x (dest_edges (fold_left (fun acc t => add_dest_if_absent (DistributedHardwareProgram.DestTrie (f t)) acc) l ds)).
Proof.
  revert ds. induction l as [|t l IH]; intros ds H; cbn; [exact H|].
  apply IH. apply (dest_edges_mono (DistributedHardwareProgram.DestTrie (f t))). exact H.
Qed.

(*----how a map.put changes node_rel_dests----*)

Lemma node_rel_dests_put_diff (ftables : node_ftable_map) (n node : node_id)
    (nf : forwarding_table) (rel : rel_id) :
  n <> node ->
  node_rel_dests (map.put ftables n nf) node rel = node_rel_dests ftables node rel.
Proof.
  intros Hne. unfold node_rel_dests, EncodeLayout.get_node_ftable.
  rewrite map.get_put_diff by (intro; subst; apply Hne; reflexivity). reflexivity.
Qed.

Lemma node_rel_dests_put_same (ftables : node_ftable_map) (node : node_id)
    (nf : forwarding_table) (rel : rel_id) :
  node_rel_dests (map.put ftables node nf) node rel =
  match map.get nf rel with Some ds => ds | None => [] end.
Proof.
  unfold node_rel_dests, EncodeLayout.get_node_ftable. rewrite map.get_put_same. reflexivity.
Qed.

(* the rel-dests at [node0] right after [putting] a fresh value [V] for [rel] there is exactly [V] *)
Lemma node_rel_dests_put_self (ftables : node_ftable_map) (node0 : node_id) (rel : rel_id)
    (V : list destination) :
  node_rel_dests (map.put ftables node0 (map.put (get_node_ftable node0 ftables) rel V)) node0 rel = V.
Proof.
  rewrite node_rel_dests_put_same. rewrite map.get_put_same. reflexivity.
Qed.

(* Replacing node [node0]'s table by a [rel]-update that only grows [rel]'s destination list
   ([upd] preserves [dest_edges]) never removes any forwarding edge. *)
Lemma has_fwd_edge_put_relupdate (ftables : node_ftable_map) (node0 : node_id) (rel : rel_id)
    (upd : list destination -> list destination) (node : node_id) (rel0 : rel_id) (m : node_id) :
  (forall ds x, In x (dest_edges ds) -> In x (dest_edges (upd ds))) ->
  has_fwd_edge ftables node rel0 m ->
  has_fwd_edge (map.put ftables node0
                 (map.put (get_node_ftable node0 ftables) rel (upd (node_rel_dests ftables node0 rel))))
               node rel0 m.
Proof.
  intros Hupd Hhas. unfold has_fwd_edge in *.
  destruct (node_id_eqb_spec node node0) as [->|Hne].
  - rewrite node_rel_dests_put_same.
    destruct (Nat.eqb_spec rel0 rel) as [->|Hrne].
    + rewrite map.get_put_same. apply Hupd. exact Hhas.
    + rewrite map.get_put_diff by (intro; subst; apply Hrne; reflexivity).
      unfold node_rel_dests in Hhas. exact Hhas.
  - rewrite node_rel_dests_put_diff by congruence. exact Hhas.
Qed.

(* [add_trie_dest] (which only adds [DestTrie]s) never removes a forwarding edge *)
Lemma add_trie_mono (node0 : node_id) (rel : rel_id) (ninfos : list node_info)
    (ftables : node_ftable_map) (node : node_id) (rel0 : rel_id) (m : node_id) :
  has_fwd_edge ftables node rel0 m ->
  has_fwd_edge (add_trie_dest node0 rel ftables ninfos) node rel0 m.
Proof.
  intros Hhas. unfold EncodeLayout.add_trie_dest_to_forwarding_table.
  apply (has_fwd_edge_put_relupdate ftables node0 rel
           (fun ds => fold_left (fun acc t => add_dest_if_absent
                        (DistributedHardwareProgram.DestTrie t.(tid)) acc) _ ds)).
  - intros ds x Hx. apply (dest_edges_fold_trie (fun t => t.(tid))). exact Hx.
  - exact Hhas.
Qed.

(* the whole [add_path] construction is monotone: it never removes a forwarding edge *)
Lemma add_path_mono (rel : rel_id) (ninfos : list node_info) :
  forall (path : list node_id) (ftables : node_ftable_map) (node : node_id) (rel0 : rel_id) (m : node_id),
  has_fwd_edge ftables node rel0 m ->
  has_fwd_edge (add_path rel path ftables ninfos) node rel0 m.
Proof.
  induction path as [|node0 [|next rest] IH]; intros ftables node rel0 m Hhas; cbn.
  - exact Hhas.
  - apply add_trie_mono. exact Hhas.
  - apply IH.
    apply (has_fwd_edge_put_relupdate ftables node0 rel
             (fun ds => add_dest_if_absent (DistributedHardwareProgram.DestEdge next) ds)).
    + intros ds x Hx. apply dest_edges_mono. exact Hx.
    + exact Hhas.
Qed.

(* one-step unfolding of [add_path] on a 2+-element path (avoids [cbn] over-unfolding the fix
   into a stuck [match] on the abstract tail) *)
Lemma add_path_cons2 (rel : rel_id) (node0 next : node_id) (rest : list node_id)
    (ftables : node_ftable_map) (ninfos : list node_info) :
  add_path rel (node0 :: next :: rest) ftables ninfos =
  add_path rel (next :: rest)
    (map.put ftables node0
       (map.put (get_node_ftable node0 ftables) rel
          (add_dest_if_absent (DistributedHardwareProgram.DestEdge next)
             (node_rel_dests ftables node0 rel)))) ninfos.
Proof. reflexivity. Qed.

(* MAIN (Phase B): along the laid-out path, each node forwards [rel] to its successor. *)
Lemma add_path_adds (rel : rel_id) (ninfos : list node_info) :
  forall (path : list node_id) (ftables : node_ftable_map) (i : nat) (a b : node_id),
  nth_error path i = Some a -> nth_error path (S i) = Some b ->
  has_fwd_edge (add_path rel path ftables ninfos) a rel b.
Proof.
  induction path as [|node0 [|next rest] IH]; intros ftables i a b Hi Hib.
  - destruct i; discriminate.
  - destruct i; cbn in Hib; [discriminate | destruct i; discriminate].
  - rewrite add_path_cons2. destruct i as [|i'].
    + (* a = node0, b = next: the edge laid at node0, preserved by the rest *)
      cbn in Hi, Hib. injection Hi as <-. injection Hib as <-.
      apply add_path_mono.
      unfold has_fwd_edge. rewrite node_rel_dests_put_self.
      apply (dest_edges_add_edge next).
    + (* recurse into the tail *)
      apply (IH _ i' a b).
      * cbn in Hi. exact Hi.
      * cbn in Hib. exact Hib.
Qed.

(*============================================================================*)
(*  Phase C (soundness): every forwarding edge is a real graph edge            *)
(*============================================================================*)

Lemma node_rel_dests_put_self_diff (ftables : node_ftable_map) (node0 : node_id) (rel : rel_id)
    (V : list destination) (rel0 : rel_id) :
  rel0 <> rel ->
  node_rel_dests (map.put ftables node0 (map.put (get_node_ftable node0 ftables) rel V)) node0 rel0 =
  node_rel_dests ftables node0 rel0.
Proof.
  intros Hne. rewrite node_rel_dests_put_same.
  rewrite map.get_put_diff by (intro; subst; apply Hne; reflexivity).
  reflexivity.
Qed.

Lemma dest_edges_add_edge_inv (next : node_id) (ds : list destination) (m : node_id) :
  In m (dest_edges (add_dest_if_absent (DistributedHardwareProgram.DestEdge next) ds)) ->
  m = next \/ In m (dest_edges ds).
Proof.
  unfold EncodeLayout.add_dest_if_absent. destruct (existsb _ ds).
  - intros H. right. exact H.
  - cbn. intros [<- | H]; [left; reflexivity | right; exact H].
Qed.

Lemma dest_edges_add_trie_eq (t : trie_id) (ds : list destination) :
  dest_edges (add_dest_if_absent (DistributedHardwareProgram.DestTrie t) ds) = dest_edges ds.
Proof. unfold EncodeLayout.add_dest_if_absent. destruct (existsb _ ds); reflexivity. Qed.

Lemma dest_edges_fold_trie_eq {A : Type} (f : A -> trie_id) (l : list A) (ds : list destination) :
  dest_edges (fold_left (fun acc t => add_dest_if_absent (DistributedHardwareProgram.DestTrie (f t)) acc) l ds) = dest_edges ds.
Proof.
  revert ds. induction l as [|t l IH]; intros ds; cbn; [reflexivity|].
  rewrite IH. apply dest_edges_add_trie_eq.
Qed.

(* [add_trie_dest] only adds [DestTrie]s, so it changes no forwarding edge *)
Lemma add_trie_edges (node0 : node_id) (rel : rel_id) (ninfos : list node_info)
    (ftables : node_ftable_map) (node : node_id) (rel0 : rel_id) (m : node_id) :
  has_fwd_edge (add_trie_dest node0 rel ftables ninfos) node rel0 m ->
  has_fwd_edge ftables node rel0 m.
Proof.
  unfold has_fwd_edge, EncodeLayout.add_trie_dest_to_forwarding_table. cbv zeta. intros H.
  destruct (node_id_eqb_spec node node0) as [->|Hne].
  - destruct (Nat.eqb_spec rel0 rel) as [->|Hrne].
    + rewrite node_rel_dests_put_self in H. rewrite dest_edges_fold_trie_eq in H. exact H.
    + rewrite node_rel_dests_put_self_diff in H by exact Hrne. exact H.
  - rewrite node_rel_dests_put_diff in H by congruence. exact H.
Qed.

(* characterization of [add_path]'s edges: each is either pre-existing or a path step *)
Lemma add_path_edges (rel : rel_id) (ninfos : list node_info) :
  forall (path : list node_id) (ftables : node_ftable_map) (node : node_id) (rel0 : rel_id) (m : node_id),
  has_fwd_edge (add_path rel path ftables ninfos) node rel0 m ->
  has_fwd_edge ftables node rel0 m \/
  (rel0 = rel /\ exists i, nth_error path i = Some node /\ nth_error path (S i) = Some m).
Proof.
  induction path as [|node0 [|next rest] IH]; intros ftables node rel0 m H.
  - left. exact H.
  - left. eapply add_trie_edges. exact H.
  - rewrite add_path_cons2 in H.
    destruct (IH _ node rel0 m H) as [H1 | [-> [i [Hi Hib]]]].
    + (* edge in the put: pre-existing, or the (node0 -> next) step *)
      unfold has_fwd_edge in H1.
      destruct (node_id_eqb_spec node node0) as [->|Hne].
      * destruct (Nat.eqb_spec rel0 rel) as [->|Hrne].
        -- rewrite node_rel_dests_put_self in H1.
           apply dest_edges_add_edge_inv in H1. destruct H1 as [-> | H1].
           ++ right. split; [reflexivity|]. exists 0. cbn. split; reflexivity.
           ++ left. exact H1.
        -- left. rewrite node_rel_dests_put_self_diff in H1 by exact Hrne. exact H1.
      * left. rewrite node_rel_dests_put_diff in H1 by congruence. exact H1.
    + (* step inside the tail [next::rest] at index i => index (S i) in the full path *)
      right. split; [reflexivity|]. exists (S i). cbn. split; [exact Hi | exact Hib].
Qed.

(* the table is *edge-sound* when every forwarding edge it records is a real graph edge *)
Definition ftable_edges_sound (g : node_graph) (ftables : node_ftable_map) : Prop :=
  forall node rel m, has_fwd_edge ftables node rel m -> cg_edge g node m.

(* the empty table is edge-sound (it records nothing) *)
Lemma ftable_edges_sound_empty (g : node_graph) : ftable_edges_sound g map.empty.
Proof.
  intros node rel m H. unfold has_fwd_edge, node_rel_dests, EncodeLayout.get_node_ftable in H.
  rewrite map.get_empty in H. rewrite map.get_empty in H. cbn in H. destruct H.
Qed.

(* laying down a real edge-path keeps the table edge-sound *)
Lemma add_path_pres_sound (g : node_graph) (rel : rel_id) (ninfos : list node_info)
    (path : list node_id) (ftables : node_ftable_map) (s e : node_id) :
  is_path g s e path ->
  ftable_edges_sound g ftables ->
  ftable_edges_sound g (add_path rel path ftables ninfos).
Proof.
  intros [_ [_ [_ Hwalk]]] Hsound node rel0 m H.
  apply add_path_edges in H. destruct H as [H | [_ [i [Hi Hib]]]].
  - exact (Hsound node rel0 m H).
  - exact (Hwalk i node m Hi Hib).
Qed.

(* adding trie destinations keeps the table edge-sound *)
Lemma add_trie_pres_sound (g : node_graph) (node0 : node_id) (rel : rel_id) (ninfos : list node_info)
    (ftables : node_ftable_map) :
  ftable_edges_sound g ftables ->
  ftable_edges_sound g (add_trie_dest node0 rel ftables ninfos).
Proof.
  intros Hsound node rel0 m H. apply add_trie_edges in H. exact (Hsound node rel0 m H).
Qed.

(* generic combinators that lift a per-step preservation through the two fold shapes the
   compiler uses to assemble the whole forwarding table: a [map.fold] over producer/consumer
   node-sets, and a [fold_left] over the relation ids. *)
Lemma map_fold_pres_sound {K Vv : Type} {M : map.map K Vv} {Mok : map.ok M}
    (g : node_graph) (f : node_ftable_map -> K -> Vv -> node_ftable_map) (init : node_ftable_map) (mp : M) :
  ftable_edges_sound g init ->
  (forall ft k v, ftable_edges_sound g ft -> ftable_edges_sound g (f ft k v)) ->
  ftable_edges_sound g (map.fold f init mp).
Proof.
  intros Hinit Hstep.
  apply (map.fold_spec (fun _ r => ftable_edges_sound g r)).
  - exact Hinit.
  - intros k v m r _ Hr. apply Hstep. exact Hr.
Qed.

Lemma fold_left_pres_sound {A : Type} (g : node_graph) (f : node_ftable_map -> A -> node_ftable_map)
    (l : list A) (init : node_ftable_map) :
  ftable_edges_sound g init ->
  (forall acc x, ftable_edges_sound g acc -> ftable_edges_sound g (f acc x)) ->
  ftable_edges_sound g (fold_left f l init).
Proof.
  revert init. induction l as [|x l IH]; intros init Hinit Hstep; cbn; [exact Hinit|].
  apply IH; [apply Hstep; exact Hinit | exact Hstep].
Qed.

(*============================================================================*)
(*  Phase C2 (completeness engine): a forwarding edge laid down by some step    *)
(*  of the construction survives to the final table.  Generic over an arbitrary *)
(*  monotone table-predicate [P] (instantiated with [fun ft => has_fwd_edge     *)
(*  ft a r b] at the use site), so the same combinators thread both the         *)
(*  [map.fold] over producer/consumer node-sets and the [fold_left] over rels.  *)
(*============================================================================*)

(* a monotone [P] is preserved through a [map.fold] (dual of [map_fold_pres_sound]) *)
Lemma map_fold_pres {K Vv : Type} {M : map.map K Vv} {Mok : map.ok M}
    (P : node_ftable_map -> Prop) (f : node_ftable_map -> K -> Vv -> node_ftable_map)
    (init : node_ftable_map) (mp : M) :
  P init ->
  (forall ft k v, P ft -> P (f ft k v)) ->
  P (map.fold f init mp).
Proof.
  intros Hinit Hstep.
  apply (map.fold_spec (fun _ r => P r)); [exact Hinit | intros k v m r _ Hr; apply Hstep, Hr].
Qed.

Lemma fold_left_pres {A : Type} (P : node_ftable_map -> Prop) (f : node_ftable_map -> A -> node_ftable_map)
    (l : list A) (init : node_ftable_map) :
  P init ->
  (forall acc x, P acc -> P (f acc x)) ->
  P (fold_left f l init).
Proof.
  revert init. induction l as [|x l IH]; intros init Hinit Hstep; cbn; [exact Hinit|].
  apply IH; [apply Hstep; exact Hinit | exact Hstep].
Qed.

(* if some key [k0] in [mp] has a step that always establishes [P], and every step is
   monotone for [P], then the whole [map.fold] establishes [P] (over [node_id] keys, using
   [node_id_eqb] to locate [k0]). *)
Lemma nid_fold_adds {Vv : Type} {M : map.map node_id Vv} {Mok : map.ok M}
    (P : node_ftable_map -> Prop) (f : node_ftable_map -> node_id -> Vv -> node_ftable_map)
    (init : node_ftable_map) (mp : M) (k0 : node_id) (v0 : Vv) :
  map.get mp k0 = Some v0 ->
  (forall ft k v, P ft -> P (f ft k v)) ->
  (forall ft, P (f ft k0 v0)) ->
  P (map.fold f init mp).
Proof.
  intros Hget Hmono Hk0.
  refine (map.fold_spec (fun (m' : M) (acc : node_ftable_map) => map.get m' k0 = Some v0 -> P acc)
            f init _ _ mp Hget).
  - intros Hc. rewrite map.get_empty in Hc. discriminate.
  - intros k v m r Hmk IH Hget'.
    destruct (node_id_eqb_spec k k0) as [->|Hne].
    + rewrite map.get_put_same in Hget'. injection Hget' as <-. apply Hk0.
    + rewrite map.get_put_diff in Hget' by (intro; subst; apply Hne; reflexivity).
      apply Hmono, IH, Hget'.
Qed.

(* the [fold_left] analogue: some element [x0] of [l] has a step that always establishes [P]. *)
Lemma fold_left_adds {A : Type} (P : node_ftable_map -> Prop) (f : node_ftable_map -> A -> node_ftable_map)
    (l : list A) (init : node_ftable_map) (x0 : A) :
  In x0 l ->
  (forall acc x, P acc -> P (f acc x)) ->
  (forall acc, P (f acc x0)) ->
  P (fold_left f l init).
Proof.
  intros Hin Hmono Hx0. revert init Hin.
  induction l as [|x l IH]; intros init Hin; cbn; [destruct Hin|].
  destruct Hin as [-> | Hin].
  - apply fold_left_pres; [apply Hx0 | exact Hmono].
  - apply (IH (f init x) Hin).
Qed.

End ForwardingCorrect.
