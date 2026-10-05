From Stdlib Require Import List String Bool ZArith.
From DatalogRocq Require Import HardwareProgram Topologies.Graph.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Eqb Tactics.destr Tactics.fwd.
From Datalog.Util Require Import Map.

Ltac eqb_ok :=
  intros a b; destruct a, b; cbn in *;
  repeat Tactics.destruct_one_match; repeat intro; fwd; congruence || tauto.

Module input_port.
  Set Boolean Equality Schemes.
  #[local] Register Scheme Nat.eqb as beq for nat.
  Variant input_port :=
    | self
    | other (port : nat) (channel : nat).
  Unset Boolean Equality Schemes.
  #[export] Instance eqb : Eqb input_port := input_port_beq.
  #[export] Instance eqb_ok : Eqb_ok eqb.
  Proof. eqb_ok. Qed.
End input_port. Export (hints) input_port. Notation input_port := input_port.input_port.

Section DistributedHardwareProgram.
Context {node_id : node_idT}
  {node_id_eqb : Eqb node_id} {node_id_eqb_ok : Eqb_ok node_id_eqb}.

Variant virtual_node :=
  (*the part of the node that sends facts*)
  | node_src (_ : node_id)
  (*input ports, for forwarding-table purposes.  port is a physical thing, channel is virtual/imaginary.*)
  | node_port (_ : node_id) (port : nat) (channel : nat)
  (*the part of the node that receives facts*)
  | node_dst (_ : node_id).

#[export] Instance virtual_node_eqb : Eqb virtual_node :=
  fun a b =>
    match a, b with
    | node_src x, node_src y | node_dst x, node_dst y => eqb x y
    | node_port n1 p1 c1, node_port n2 p2 c2 => eqb n1 n2 && eqb p1 p2 && eqb c1 c2
    | _, _ => false
    end.

#[export] Instance virtual_node_eqb_ok : Eqb_ok virtual_node_eqb.
Proof. eqb_ok. Qed.

Context `{map.map (rel_id * input_port) (list virtual_node)}.

Definition forwarding_table := partial_map (rel_id * input_port) (list virtual_node).

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
