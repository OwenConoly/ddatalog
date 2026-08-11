(* StringDatalog: the *datalog* backend for the compiler -- the program types (relations,
   variables, functions, ... are strings, from StringDatalogParams) together with the sorted-list
   map instances they need.  This is entirely independent of the topology (node ids / graph):
   combine it with a topology backend (e.g. GridTopology) to get a concrete compiler. *)

From DatalogRocq Require Import DistributedDatalogToHardwareCompiler StringDatalogParams.
From coqutil Require Import Map.Interface Map.SortedListString Eqb Decidable.
From GraphSearch Require Import GraphInterface GraphImpl.
Import StringDatalogParams.

(* Variables and functions are strings; these are the variable-keyed maps the compiler needs. *)
#[global] Instance var_node_set : map.map _ _ := SortedListString.map unit.
#[global] Instance var_eqb : Eqb string_var := String.eqb.

#[global] Instance var_eqb_ok : Eqb_ok var_eqb.
Proof. intros a b. unfold eqb, var_eqb. destruct (String.eqb_spec a b); assumption. Qed.

#[global] Instance var_graph_impl : graph.graph string_var :=
  @GraphImpl.graph_map string_var var_eqb var_eqb_ok
    (SortedListString.map unit) (SortedListString.ok unit)
    (SortedListString.map (SortedListString.map unit)) (SortedListString.ok _).

#[global] Instance var_graph_impl_ok : graph.ok var_graph_impl :=
  @GraphImpl.graph_map_ok string_var var_eqb var_eqb_ok
    (SortedListString.map unit) (SortedListString.ok unit)
    (SortedListString.map (SortedListString.map unit)) (SortedListString.ok _).
#[global] Instance var_idx_map : map.map _ _ := SortedListString.map nat.
