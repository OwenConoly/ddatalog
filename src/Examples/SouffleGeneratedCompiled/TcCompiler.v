From Stdlib Require Import List ZArith Lia String.
From DatalogRocq Require Import Examples.SouffleGeneratedRocq.Tc EncodeLayout StringDatalogParams StringGridCompiler.
Import ListNotations.

(* Compilation *)

Definition program_to_compile : list rule := computed_program.

(* No Input Facts*)
(* Definition layout : list (node_id * list nat) :=
  [ ([0;1], [0]); ([1;1], [1]); ([1;2], [2]); ([2;0], [5]); ([2;1], [4]); ([2;2], [3]) ].

Definition empty_fact_producers : fact_locations (rel := rel) (node_id := node_id) := []. *)

(* For purposes of benchmarking this is so we can also compile to a single node *)
Definition one_node_layout : list (node_id * list nat) := [ ([0;0], [0; 1; 2; 3; 4; 5]) ].

Definition one_node_fact_producers : fact_locations (rel := rel) (node_id := node_id) :=
  [ ("base", [[0;0]]); ("tc", [[0;0]]); ("tcl", [[0;0]]); ("tcr", [[0;0]]) ].

Definition one_node_fact_consumers : fact_locations (rel := rel) (node_id := node_id) :=
  [ ("tc", [[0;0]]); ("tcl", [[0;0]]); ("tcr", [[0;0]]) ].

(* Actual compiler assigned layout *)
Definition layout : list (node_id * list nat) :=
  [ ([1;0], [1]); ([1;1], [2]); ([1;2], [3]); ([2;0], [0]); ([2;1], [5]); ([2;2], [4]) ].

Definition fact_producers : fact_locations (rel := rel) (node_id := node_id) :=
  [ ("base", [[2;1]]); ("tc", [[2;1]]); ("tcl", [[0;0]]); ("tcr", [[1;2]]) ].

Definition fact_consumers : fact_locations (rel := rel) (node_id := node_id) :=
  [ ("tc", [[2;2]]); ("tcl", [[2;1]]); ("tcr", [[1;2]]) ].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

Definition compiled_tc := compile_program program_to_compile layout fact_producers fact_consumers topo_dims 100.

Eval vm_compute in compiled_tc.
