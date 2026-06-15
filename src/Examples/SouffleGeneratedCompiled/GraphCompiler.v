(* From Stdlib Require Import List ZArith Lia String.
From DatalogRocq Require Import Examples.SouffleGeneratedRocq.Graph EncodeLayout StringDatalogParams StringGridCompiler.
Import ListNotations.

(* Compilation *)

Definition program_to_compile : list rule := computed_program.

Definition layout : list (node_id * list nat) :=
  [ ([0;0], [0;1]) ].

Definition empty_fact_producers : fact_locations (node_id := node_id) := [].

Definition fact_producers : fact_locations (node_id := node_id) :=
  [ ("arc", [[2;1]]); ("null", [[2;1]]); ("nullEdge", [[0;0]]) ].

Definition fact_consumers : fact_locations (node_id := node_id) :=
  [ ("null", [[1;2]]) ].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

Definition compiled_graph := compile_program program_to_compile layout fact_producers fact_consumers topo_dims 100.

Eval vm_compute in compiled_graph. *)