From Stdlib Require Import List.
From DatalogRocq Require Import Examples.Programs.Graph DistributedDatalogToHardwareCompiler StringGridCompiler StringDatalogParams.
Import ListNotations.

(* Compilation *)

Definition program_to_compile : list rule := graph_program.

Definition layout : list (node_id * list nat) :=
  [ ([0;0], [0;1;2;3]) ].

Definition empty_fact_producers : fact_locations (rel := rel) (node_id := node_id) := [].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

Definition compiled_graph := compile_program program_to_compile layout empty_fact_producers empty_fact_producers topo_dims 100.

Eval vm_compute in compiled_graph.