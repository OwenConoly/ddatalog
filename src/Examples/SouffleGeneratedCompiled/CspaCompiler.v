From Stdlib Require Import List ZArith Lia String.
From DatalogRocq Require Import Examples.SouffleGeneratedRocq.Cspa DistributedHardwareCompiler StringDatalogParams StringGridCompiler.
Import ListNotations.

(* Compilation *)

Definition program_to_compile : list rule := computed_program.

(* No Input Facts*)
(* Definition layout : list (node_id * list nat) :=
  [ ([0;0], [8]); ([0;1], [1]); ([0;2], [2]); ([1;0], [3]); ([1;1], [6;9]); ([1;2], [4]); ([2;0], [7]); ([2;1], [5]); ([2;2], [0]) ].

Definition empty_fact_producers : fact_locations (rel := rel) (node_id := node_id) := []. *)

(* For purposes of benchmarking this is so we can also compile to a single node *)

Definition one_node_layout : list (node_id * list nat) := [ ([0;0], [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]) ].

Definition one_node_fact_producers : fact_locations (rel := rel) (node_id := node_id) :=
  [ ("assign", [[0;0]]); ("dereference", [[0;0]]); ("memoryAlias", [[0;0]]); ("valueAlias", [[0;0]]); ("valueFlow", [[0;0]]) ].

Definition one_node_fact_consumers : fact_locations (rel := rel) (node_id := node_id) :=
  [ ("memoryAlias", [[0;0]]); ("valueAlias", [[0;0]]); ("valueFlow", [[0;0]]) ].

(* Actual compiler assigned layout *)

Definition layout : list (node_id * list nat) :=
  [ ([0;0], [8]); ([0;1], [6]); ([0;2], [2]); ([1;0], [3]); ([1;1], [9]); ([1;2], [5]); ([2;0], [7]); ([2;1], [0]); ([2;2], [1;4]) ].

Definition fact_producers : fact_locations (rel := rel) (node_id := node_id) :=
  [ ("assign", [[2;1]]); ("dereference", [[2;1]]); ("memoryAlias", [[0;0]]); ("valueAlias", [[1;2]]); ("valueFlow", [[2;2]]) ].

Definition fact_consumers : fact_locations (rel := rel) (node_id := node_id) :=
  [ ("memoryAlias", [[2;1]]); ("valueAlias", [[1;2]]); ("valueFlow", [[2;2]]) ].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

Definition compiled_cspa := compile_program program_to_compile layout fact_producers fact_consumers topo_dims 100.

Eval vm_compute in compiled_cspa.