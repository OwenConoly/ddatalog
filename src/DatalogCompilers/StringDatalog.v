(* StringDatalog: the *datalog* backend for the compiler -- the program types (relations,
   variables, functions, ... are strings, from StringDatalogParams) together with the sorted-list
   map instances they need.  This is entirely independent of the topology (node ids / graph):
   combine it with a topology backend (e.g. GridTopology) to get a concrete compiler. *)

From DatalogRocq Require Import DistributedDatalogToHardwareCompiler StringDatalogParams.
From coqutil Require Import Map.Interface Map.SortedListString.
Import StringDatalogParams.

(* Variables and functions are strings; these are the variable-keyed maps the compiler needs. *)
#[global] Instance var_node_set : map.map _ _ := SortedListString.map unit.
#[global] Instance var_edge_set : map.map _ _ := SortedListString.map (SortedListString.map unit).
#[global] Instance var_idx_map : map.map _ _ := SortedListString.map nat.
