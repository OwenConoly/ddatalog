From coqutil Require Import Map.Interface.
From Stdlib Require Import List Bool.
From DatalogRocq Require Import Graph.
Import ListNotations.
Import BoolNotations.

Section ComputableGraph.
Context {Node : Type}.
Context {node_eqb : Node -> Node -> bool}.
Context {node_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (node_eqb x y)}.
Context {node_set : map.map Node unit}.
Context {node_set_ok : map.ok node_set}.
Context {edge_set : map.map Node node_set}.
Context {edge_set_ok : map.ok edge_set}.

Record ComputableGraph := {
  nodes : node_set;
  edges : edge_set
}.

Definition check_node_valid (n : Node) (ns : node_set) : bool :=
  match map.get ns n with
  | Some _ => true
  | None => false
  end.

Definition check_edge_valid (n1 n2 : Node) (ns : node_set) : bool :=
  check_node_valid n1 ns && check_node_valid n2 ns.

(* Check all edges only use nodes from the node set *)
Definition check_edges_valid (es : edge_set) (ns : node_set) : bool :=
  map.forallb (fun n1 neighbors =>
    map.forallb (fun n2 _ =>
      check_edge_valid n1 n2 ns
    ) neighbors
  ) es.

Definition check_graph_valid (cg : ComputableGraph) : bool :=
  check_edges_valid cg.(edges) cg.(nodes).

Definition cg_nodes_to_g_nodes (ns : node_set) : Node -> Prop :=
  fun n => check_node_valid n ns = true.

Definition check_edge_exists (n1 n2 : Node) (es : edge_set) : bool :=
  match map.get es n1 with
  | Some neighbors => match map.get neighbors n2 with
                      | Some _ => true
                      | None => false
                      end
  | None => false
  end.

Definition cg_edges_to_g_edges (es : edge_set) (ns : node_set) : Node -> Node -> Prop :=
  fun n1 n2 => check_edge_exists n1 n2 es = true.

Definition computable_graph_to_graph (cg : ComputableGraph) : Graph :=
  {|
    Graph.nodes := fun n => check_node_valid n cg.(nodes) = true;
    Graph.edge := fun n1 n2 => check_edge_exists n1 n2 cg.(edges) = true
  |}.

Lemma forallb_spec : forall {key val : Type} {m : map.map key val} {ok : map.ok m}
    (key_eq_dec : forall k1 k2 : key, {k1 = k2} + {k1 <> k2})
    (f : key -> val -> bool) (mp : m),
  map.forallb f mp = true <->
  forall k v, map.get mp k = Some v -> f k v = true.
Proof.
  intros. unfold map.forallb.
  eapply (map.fold_spec (fun mp r => r = true <-> forall k v, map.get mp k = Some v -> f k v = true)).
  - split.
    + intros _ k v. rewrite map.get_empty. discriminate.
    + intros. reflexivity.
  - intros k v m' r Hget [IHf IHb].
    split.
    + intros Handb k' v' Hget'.
      apply andb_prop in Handb. destruct Handb as [Hr Hf].
      destruct (key_eq_dec k' k) as [->|Hne].
      * rewrite map.get_put_same in Hget'. inversion Hget'. subst. exact Hf.
      * rewrite map.get_put_diff in Hget' by exact Hne.
        exact (IHf Hr k' v' Hget').
    + intros Hall.
      apply andb_true_intro. split.
      * apply IHb. intros k' v' Hget'.
        apply Hall. rewrite map.get_put_diff; [exact Hget'|].
        intros ->. rewrite Hget in Hget'. discriminate.
      * apply Hall. rewrite map.get_put_same. reflexivity.
Qed.

Definition node_eq_dec : forall n1 n2 : Node, {n1 = n2} + {n1 <> n2}.
Proof.
  intros n1 n2.
  case_eq (node_eqb n1 n2); intro Heq.
  - left. destruct (node_eqb_spec n1 n2); auto; discriminate.
  - right. destruct (node_eqb_spec n1 n2); auto; discriminate.
Qed.

Lemma check_graph_correct : forall cg,
  check_graph_valid cg = true <-> good_graph (computable_graph_to_graph cg).
Proof.
  intros cg.
  unfold check_graph_valid, check_edges_valid, good_graph, computable_graph_to_graph. simpl.
  unfold check_edges_valid.
  rewrite (forallb_spec node_eq_dec).
  split.
  - intros H n1 n2 Hedge.
    (* Hedge : check_edge_exists n1 n2 cg.(edges) = true *)
    unfold check_edge_exists in Hedge.
    destruct (map.get cg.(edges) n1) eqn:E1; try discriminate.
    destruct (map.get r n2) eqn:E2; try discriminate.
    specialize (H n1 r E1).
    rewrite (forallb_spec node_eq_dec) in H.
    specialize (H n2 u E2).
    unfold check_edge_valid in H.
    apply andb_prop in H. destruct H as [Hn1 Hn2].
    split; assumption.
  - intros H n1 neighbors Hn1.
    rewrite (forallb_spec node_eq_dec).
    intros n2 u Hn2.
    unfold check_edge_valid.
    apply andb_true_intro.
    assert (Hedge : check_edge_exists n1 n2 cg.(edges) = true).
    { unfold check_edge_exists. rewrite Hn1, Hn2. reflexivity. }
    apply H in Hedge.
    destruct Hedge as [Hn1valid Hn2valid].
    split; assumption.
Qed.

End ComputableGraph.