From Stdlib Require Import List String Bool ZArith.
From DatalogRocq Require Import HardwareProgram.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Eqb.
From Datalog.Util Require Import Map.

Section DistributedHardwareProgram.

Context {node_id : Type}
        {node_id_eqb : Eqb node_id} {node_id_eqb_ok : Eqb_ok node_id_eqb}.

Variant virtual_node :=
  (*the part of the node that sends facts*)
  | node_src (_ : node_id)
  (*some copies of it, for forwarding-table purposes*)
  | fwd_node (_ : node_id) (src_id : node_id) (src_channel : nat)
  (*the part of the node that receives facts*)
  | node_dst (_ : node_id).

#[export] Instance virtual_node_eqb : Eqb virtual_node. Admitted.

Context {fdjakldfa : map.map (rel_id * virtual_node) (list virtual_node)}.

Definition forwarding_table := partial_map (rel_id * virtual_node) (list virtual_node).
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
