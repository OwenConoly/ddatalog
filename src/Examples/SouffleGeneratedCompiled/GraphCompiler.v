From Stdlib Require Import List ZArith Lia String.
From DatalogRocq Require Import Examples.SouffleGeneratedRocq.Graph DistributedDatalogToHardwareCompiler StringDatalogParams StringGridCompiler.
Import ListNotations.

(* Compilation *)

Definition program_to_compile : list rule := computed_program.

(* Layout from the Gurobi optimizer (core-layout/pipeline): rule 0 (path :- edge) on node (1,1),
   rule 1 (path :- path, edge) on node (2,1). *)
Definition layout : list (node_id * list nat) :=
  [ ([1;1], [0]); ([2;1], [1]) ].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

(* No designated input/output nodes, so this uses [all_io_locations] -- every grid node is an
   input AND output for every relation. *)
Definition compiled_graph := compile_program program_to_compile layout (all_io_locations program_to_compile layout topo_dims) (all_io_locations program_to_compile layout topo_dims) topo_dims (grid_fuel topo_dims).

Eval vm_compute in compiled_graph.
