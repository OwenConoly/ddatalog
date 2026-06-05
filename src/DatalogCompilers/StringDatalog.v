(* StringDatalog: the *datalog* backend for the compiler -- the program types (relations,
   variables, functions, ... are strings, from StringDatalogParams) together with the sorted-list
   map instances they need.  This is entirely independent of the topology (node ids / graph):
   combine it with a topology backend (e.g. GridTopology) to get a concrete compiler. *)

From DatalogRocq Require Import DistributedDatalogToHardwareCompiler StringDatalogParams.
From coqutil Require Import Map.Interface Map.SortedListString.
Import StringDatalogParams.

(* Relation/function names are strings, mapped to numeric ids; variables are strings. *)
Definition fn_id_map     := SortedListString.map fn_id.
Definition rel_relid_map := SortedListString.map rel_id.
Definition var_node_set  := SortedListString.map unit.
Definition var_edge_set  := SortedListString.map (SortedListString.map unit).
Definition var_idx_map   := SortedListString.map nat.
