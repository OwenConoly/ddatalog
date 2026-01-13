From JSON Require Import Encode Printer.
From Datalog Require Import JSON FancyNotations CompilerExamples.
From DatalogRocq Require Import BasicProgram Family Graph Matmul.

Redirect "json_examples/basic_program" Eval compute in (to_string (encode basic_program)).
Redirect "json_examples/family_program" Eval compute in (to_string (encode family_program)).
Redirect "json_examples/graph_program" Eval compute in (to_string (encode graph_program)).