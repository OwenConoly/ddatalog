From Stdlib Require Import List.
From DatalogRocq Require Import Examples.Programs.Graph DistributedDatalogToHardwareCompiler StringGridCompiler StringDatalogParams.
Import ListNotations.

(* Compilation *)

Definition program_to_compile : list rule := graph_program.

Definition layout : list (node_id * list nat) :=
  [ ([0;0], [0;1;2;3]) ].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

(* TODO: no designated input/output nodes (the declared fact_producers/fact_consumers, if any,
   don't cover every produced relation under the output-sink gate), so this uses
   [all_io_locations] -- every grid node is an input AND output for every relation.
   Replace with the real input/output nodes. *)
Definition compiled_graph := compile_program program_to_compile layout (all_io_locations program_to_compile layout topo_dims) (all_io_locations program_to_compile layout topo_dims) topo_dims 100.

Eval vm_compute in compiled_graph.