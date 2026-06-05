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

Definition one_node_fact_producers : fact_locations (rel := rel) (node_id := node_id) :=
  [ ("Check", [[0;0]]); ("In", [[0;0]]) ].

Definition one_node_fact_consumers : fact_locations (rel := rel) (node_id := node_id) :=
  [ ("A", [[0;0]]) ].

Definition layout : list (node_id * list nat) := 
  [ ([0;0], [3]); ([0;1], [7]); ([0;2], [4]); ([1;0], [5]); ([1;1], [8]); ([1;2], [2]); ([2;0], [1]); ([2;1], [6]); ([2;2], [0]) ].

Definition fact_producers : fact_locations (rel := rel) (node_id := node_id) :=
  [ ("Check", [[2;1]]); ("In", [[2;1]]) ].

Definition fact_consumers : fact_locations (rel := rel) (node_id := node_id) :=
  [ ("A", [[0;0]]) ].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

Definition compiled_po4 := compile_program program_to_compile layout fact_producers fact_consumers topo_dims 100.

Eval vm_compute in compiled_po4.