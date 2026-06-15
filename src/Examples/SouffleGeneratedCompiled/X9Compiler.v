From Stdlib Require Import List ZArith Lia String.
From DatalogRocq Require Import Examples.SouffleGeneratedRocq.X9 EncodeLayout StringDatalogParams StringGridCompiler.
Import ListNotations.

(* Compilation *)

Definition program_to_compile : list rule := computed_program.

(* No Input Facts *)
(* Definition layout : list (node_id * list nat) := [ ([0;0], [1]); ([0;1], [0]) ].

Definition empty_fact_producers : fact_locations (node_id := node_id) := []. *)

(* For purposes of benchmarking this is so we can also compile to a single node *)
Definition one_node_layout : list (node_id * list nat) := [ ([0;0], [0; 1]) ].

Definition one_node_fact_producers : fact_locations (node_id := node_id) :=
  [ ("X", [[0;0]]); ("Y", [[0;0]]) ].

Definition one_node_fact_consumers : fact_locations (node_id := node_id) :=
  [ ("Y", [[0;0]]) ].

(* Actual compiler assigned layout *)
Definition layout : list (node_id * list nat) := 
  [ ([0;0], [0]); ([1;0], [1]) ].

Definition fact_producers : fact_locations (node_id := node_id) :=
  [ ("X", [[2;1]]); ("Y", [[2;1]]) ].

Definition fact_consumers : fact_locations (node_id := node_id) :=
  [ ("Y", [[0;0]]) ].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

Definition compiled_x9 := compile_program program_to_compile layout fact_producers fact_consumers topo_dims 100.

Eval vm_compute in compiled_x9.