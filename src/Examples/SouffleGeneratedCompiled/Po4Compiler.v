From Stdlib Require Import List ZArith Lia String.
From DatalogRocq Require Import Examples.SouffleGeneratedRocq.Po4 DistributedDatalogToHardwareCompiler StringDatalogParams StringGridCompiler.
Import ListNotations.

(* Compilation *)

Definition program_to_compile : list rule := computed_program.

(* No Input Facts *)

(* Definition layout : list (node_id * list nat) :=
  [ ([0;0], [3]); ([0;1], [7]); ([0;2], [4]); ([1;0], [5]); ([1;1], [8]); ([1;2], [2]); ([2;0], [1]); ([2;1], [6]); ([2;2], [0]) ].

Definition empty_fact_producers : fact_locations (rel := rel) (node_id := node_id) := []. *)

(* For purposes of benchmarking this is so we can also compile to a single node *)
Definition one_node_layout : list (node_id * list nat) := [ ([0;0], [0; 1; 2; 3; 4; 5; 6; 7; 8]) ].

Definition layout : list (node_id * list nat) := 
  [ ([0;0], [3]); ([0;1], [7]); ([0;2], [4]); ([1;0], [5]); ([1;1], [8]); ([1;2], [2]); ([2;0], [1]); ([2;1], [6]); ([2;2], [0]) ].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

(* TODO: no designated input/output nodes (the declared fact_producers/fact_consumers, if any,
   don't cover every produced relation under the output-sink gate), so this uses
   [all_io_locations] -- every grid node is an input AND output for every relation.
   Replace with the real input/output nodes. *)
Definition compiled_po4 := compile_program program_to_compile layout (all_io_locations program_to_compile layout topo_dims) (all_io_locations program_to_compile layout topo_dims) topo_dims 100.

Eval vm_compute in compiled_po4.