From Stdlib Require Import Strings.String.
From Datalog Require Import Datalog.
From DatalogRocq Require Import StringDatalogParams.
From Stdlib Require Import List.
Import ListNotations.
Open Scope string_scope.

Import StringDatalogParams.

Definition empty_rule : rule := normal_rule [] [].

Definition edge_path_rule : rule :=
  normal_rule
    [ {| clause_rel := "path"; clause_args := [var_expr "x"; var_expr "y"] |} ]
    [ {| clause_rel := "edge"; clause_args := [var_expr "x"; var_expr "y"] |} ].

(* Constants *)

(* Helper to create a constant (as a nullary function) *)
Definition const (c : string) : expr := fun_expr c [].

(* Example: edge(x, 42) :- node(x) 
   This represents "for all x, if x is a node, then there's an edge from x to node 42" *)
Definition everything_connects_to_42_rule : rule :=
  normal_rule
    [ {| clause_rel := "edge"; clause_args := [var_expr "x"; const "42"] |} ]
    [ {| clause_rel := "node"; clause_args := [var_expr "x"] |} ].

(* Example: friends(alice, bob) :- .
   A fact about friendship with only constants *)
Definition alice_bob_friend : rule :=
  normal_rule
    [ {| clause_rel := "friends"; clause_args := [const "alice"; const "bob"] |} ]
    [].

Definition basic_program: list rule :=
   [edge_path_rule; everything_connects_to_42_rule; alice_bob_friend].

Definition computed_basic_program := Eval compute in basic_program.
Print computed_basic_program.
