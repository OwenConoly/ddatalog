From Stdlib Require Import List ZArith Lia String.
From DatalogRocq Require Import Examples.SouffleGeneratedRocq.Po1 EncodeLayout StringDatalogParams StringGridCompiler.
Import ListNotations.

(* Compilation *)

Definition program_to_compile : list rule := computed_program.

(* No Input Facts *)
(* Definition layout : list (node_id * list nat) :=
  [ ([0;0], [4;12]); ([0;1], [9;15]); ([0;2], [2;16]); ([1;0], [0;5]); ([1;1], [1;6]); ([1;2], [8;10]); ([2;0], [11;17]); ([2;1], [14;18]); ([2;2], [3;7;13]) ].

Definition empty_fact_producers : fact_locations (node_id := node_id) := [("In", [[0;0]]); ("Check", [[0;1]])]. *)

(* For purposes of benchmarking this is so we can also compile to a single node *)
Definition one_node_layout : list (node_id * list nat) := [ ([0;0], [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]) ].

Definition one_node_fact_producers : fact_locations (node_id := node_id) :=
  [ ("In", [[0;0]]); ("Check", [[0;0]]) ].

Definition one_node_fact_consumers : fact_locations (node_id := node_id) :=
  [ ("A", [[0;0]]) ].

(* Actual compiler assigned layout *)
Definition layout : list (node_id * list nat) :=
  [ ([0;0], [4;14]); ([0;1], [11;15]); ([0;2], [9;18]); ([1;0], [3;12]); ([1;1], [1;5]); ([1;2], [0;16]); ([2;0], [6;10]); ([2;1], [2;8;13]); ([2;2], [7;17]) ].

Definition fact_producers : fact_locations (node_id := node_id) :=
  [ ("Check", [[2;1]]); ("In", [[2;1]]) ].

Definition fact_consumers : fact_locations (node_id := node_id) :=
  [ ("A", [[0;0]]) ].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

Definition compiled_po1 := compile_program program_to_compile layout fact_producers fact_consumers topo_dims 100.

Eval vm_compute in compiled_po1.