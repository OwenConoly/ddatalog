From Stdlib Require Import List ZArith Lia String.
From DatalogRocq Require Import BasicProgram DistributedDatalogToHardwareCompiler StringDatalogParams StringGridCompiler.
Import ListNotations.

(* Compilation *)

Definition program_to_compile : list rule := basic_program.

Definition layout : list (node_id * list nat) :=
  [ ([0;0], [0;1;2]) ].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

(* TODO: this example has no designated input/output nodes, so it uses [all_io_locations] (every
   node is an input AND output for every relation).  Replace with the real input (fact-producer)
   and output (fact-consumer) nodes. *)
Definition compiled_basic_program :=
  compile_program program_to_compile layout
    (all_io_locations program_to_compile layout topo_dims)
    (all_io_locations program_to_compile layout topo_dims) topo_dims 100.

Eval vm_compute in compiled_basic_program.