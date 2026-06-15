From Stdlib Require Import List ZArith Lia String.
From DatalogRocq Require Import Examples.SouffleGeneratedRocq.Pointsto EncodeLayout StringDatalogParams StringGridCompiler.
Import ListNotations.

(* Compilation *)

Definition program_to_compile : list rule := computed_program.

(* No Input Facts*)
(* Definition layout : list (node_id * list nat) :=
  [ ([1;1], [4]); ([1;2], [1]); ([2;0], [0]); ([2;1], [3]); ([2;2], [2]) ].

Definition empty_fact_producers : fact_locations (node_id := node_id) := []. *)

(* For purposes of benchmarking this is so we can also compile to a single node *)
Definition one_node_layout : list (node_id * list nat) := [ ([0;0], [0; 1; 2; 3; 4]) ].

Definition one_node_fact_producers : fact_locations (node_id := node_id) :=
  [ ("Alias", [[0;0]]); ("Assign", [[0;0]]); ("AssignAlloc", [[0;0]]); ("Load", [[0;0]]); ("PrimitiveAssign", [[0;0]]); ("Store", [[0;0]]); ("VarPointsTo", [[0;0]]) ].

Definition one_node_fact_consumers : fact_locations (node_id := node_id) :=
  [ ("Alias", [[0;0]]); ("Assign", [[0;0]]); ("VarPointsTo", [[0;0]]) ].

(* Actual compiler assigned layout *)
Definition layout : list (node_id * list nat) :=
  [ ([1;0], [2]); ([1;1], [3]); ([1;2], [1]); ([2;0], [0]); ([2;1], [4]) ].

Definition fact_producers : fact_locations (node_id := node_id) :=
  [ ("Alias", [[2;1]]); ("Assign", [[2;1]]); ("AssignAlloc", [[0;0]]); ("Load", [[1;2]]); ("PrimitiveAssign", [[2;2]]); ("Store", [[2;1]]); ("VarPointsTo", [[1;2]]) ].

Definition fact_consumers : fact_locations (node_id := node_id) :=
  [ ("Alias", [[2;2]]); ("Assign", [[2;0]]); ("VarPointsTo", [[1;0]]) ].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

Definition compiled_pointsto := compile_program program_to_compile layout fact_producers fact_consumers topo_dims 100.

Eval vm_compute in compiled_pointsto.
