From Stdlib Require Import List ZArith Lia String.
From DatalogRocq Require Import BasicProgram EncodeLayout StringDatalogParams StringGridCompiler.
Import ListNotations.

(* Compilation *)

Definition program_to_compile : list rule := basic_program.

Definition layout : list (node_id * list nat) :=
  [ ([0;0], [0;1;2]) ].

Definition empty_fact_producers : fact_locations (node_id := node_id) := [].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

Definition compiled_basic_program := compile_program program_to_compile layout empty_fact_producers empty_fact_producers topo_dims 100.

Eval vm_compute in
  compile_program program_to_compile layout empty_fact_producers empty_fact_producers topo_dims 100.