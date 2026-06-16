From Stdlib Require Import List String.
From DatalogRocq Require Import Family StringGridCompiler.
Import ListNotations.

(* The family ("ancestor") program compiled onto a 3x3 grid, end to end, via the modular
   string+grid compiler (an instantiation of GridTopology + StringDatalog).  Node ids are grid
   coordinates [list nat]; the layout (from the ILP solver) assigns rule indices to nodes. *)

Definition generated_layout : list (list nat * list nat) :=
  [([0;0], []); ([0;1], [7]); ([0;2], [5]); ([1;0], [4]); ([1;1], [1]);
   ([1;2], [2]); ([2;0], [6]); ([2;1], [0]); ([2;2], [3])].

(* TODO: no designated input/output nodes, so this uses [all_io_locations] -- every grid node is an
   input AND output for every relation.  Replace with the real input/output nodes. *)
Definition compiled_family :=
  StringGridCompiler.compile_program family_program generated_layout
    (StringGridCompiler.all_io_locations family_program generated_layout [3; 3])
    (StringGridCompiler.all_io_locations family_program generated_layout [3; 3]) [3; 3] (StringGridCompiler.grid_fuel [3; 3]).

Eval vm_compute in compiled_family.
