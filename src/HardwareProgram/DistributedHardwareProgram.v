From Stdlib Require Import List String Bool ZArith.
From DatalogRocq Require Import HardwareProgram.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties.

Section DistributedHardwareProgram.

(* The node-identifier type is a parameter: the compiler works over any topology whose nodes are
   identified by [node_id] with a decidable equality. *)
Context {node_id : Type}
        {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.

Inductive destination :=
| DestEdge (e : node_id)
| DestTrie (t : trie_id).

Definition destination_eqb (d1 d2 : destination) : bool :=
  match d1, d2 with
  | DestEdge e1, DestEdge e2 => node_id_eqb e1 e2
  | DestTrie t1, DestTrie t2 => Nat.eqb t1 t2
  | _, _ => false
  end.

Lemma destination_eqb_spec : forall x y : destination, BoolSpec (x = y) (x <> y) (destination_eqb x y).
Proof.
  intros x y. destruct x, y; simpl; try (constructor; congruence).
  - destruct (node_id_eqb_spec e e0); subst; constructor; congruence.
  - destruct (Nat.eqb_spec t t0); subst; constructor; congruence.
Qed.

(* The forwarding table routes each relation's facts to a set of destinations (edges/tries). *)
Context {forwarding_table : map.map rel_id (list destination)}.

(* A compiled node's program: its trie-join rules ([nprogram]), the tries they read ([ntries]),
   and the forwarding table ([nforwarding]).  This is the per-node piece of the *distributed*
   hardware program; the compiler ([EncodeLayout]) is what produces it. *)
Record node_info := {
  nid : node_id;
  nprogram : hardware_program;
  nforwarding : forwarding_table;
  ntries : list trie;
}.

End DistributedHardwareProgram.