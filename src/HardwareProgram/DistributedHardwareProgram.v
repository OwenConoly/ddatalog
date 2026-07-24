From Stdlib Require Import List String Bool ZArith.
From DatalogRocq Require Import HardwareProgram.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Eqb.

Section DistributedHardwareProgram.

Context {node_id : Type}
        {node_id_eqb : Eqb node_id} {node_id_eqb_ok : Eqb_ok node_id_eqb}.

Inductive destination :=
| DestEdge (e : node_id)
| DestTrie (t : trie_id).

#[global] Instance destination_eqb : Eqb destination :=
  fun d1 d2 =>
    match d1, d2 with
    | DestEdge e1, DestEdge e2 => node_id_eqb e1 e2
    | DestTrie t1, DestTrie t2 => Nat.eqb t1 t2
    | _, _ => false
    end.

#[global] Instance destination_eqb_ok : Eqb_ok destination_eqb.
Proof.
  intros [e1|t1] [e2|t2]; cbv [eqb destination_eqb]; try congruence.
  - pose proof (node_id_eqb_ok e1 e2) as H.
    cbv [eqb] in H. destruct (node_id_eqb e1 e2); congruence.
  - destruct (Nat.eqb_spec t1 t2); congruence.
Qed.

(* The forwarding table routes each relation's facts to a set of destinations (edges/tries). *)
Context {forwarding_table : map.map rel_id (list destination)}.

(* A compiled node's program: its trie-join rules ([nprogram]), the tries they read ([ntries]),
   and the forwarding table ([nforwarding]).  This is the per-node piece of the *distributed*
   hardware program; the compiler ([DistributedDatalogToHardwareCompiler]) is what produces it. *)
Record node_info := {
  nid : node_id;
  nprogram : hardware_program;
  nforwarding : forwarding_table;
  ntries : list trie;
}.

End DistributedHardwareProgram.
