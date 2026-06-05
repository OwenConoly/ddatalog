From Datalog Require Import Datalog.
From Stdlib Require Import List String Bool ZArith.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties.
From DatalogRocq Require Import EqbSpec DependencyGenerator SortedListNat Topologies.Graph ComputableGraph EqbSpec.

Open Scope bool_scope.
Import ListNotations.

(* The abstract syntax of hardware-readable datalog programs.

   This is the shared vocabulary used by the compiler (DistributedDatalogToHardwareCompiler), the
   single-node semantics (NodeHardwareSemantics), and the printers.  It is split into
   three layers:

   - [lowered_*]    : a datalog program with relations/functions renamed to
                      numeric ids, but variables and term structure intact.
   - [trie]/[join]  : the trie-join representation a single node executes.
   - [hardware_*]   : a full compiled program (a list of trie-join rules).

   Only [fact]/[rule]/[expr] (re-exported from [Datalog]) and the [lowered_*]
   family mention the source types [rel]/[var]/[fn]/[aggregator]; everything
   from [trie] onward is purely numeric. *)

Section HardwareProgram.

Context {rel var fn aggregator : Type}.

Definition var_id := nat.
Definition trie_id := nat.
Definition rel_id := nat.
Definition fn_id := nat.
Definition clause_id := nat.

(* An expr-carrying atom in a rule is a [Datalog.clause] (the old [fact]); a
   ground/runtime fact is [Datalog.fact] ([normal_fact R args]). *)
Definition fact := Datalog.clause rel var fn.
Definition rule := Datalog.rule rel var fn aggregator.
Definition expr := Datalog.expr var fn.
Definition program := list rule.
Definition permutation := list nat.

Record trie := {
  tid : trie_id;
  trel : rel_id;
  tperm : permutation;
}.

(* The "lowered" program is a [Datalog] program whose relations/functions are numeric ids
   ([rel_id]/[fn_id]) but whose variables/aggregator are the source's -- it is NOT a separate
   AST.  So [Datalog.interp_clause]/[prog_impl] apply to it directly and NO [lowered -> Datalog]
   conversion is ever needed (the compiler produces these rules in their final type).

   The lowered aggregator is the source's [aggregator] (NOT [unit]), so a [lowered_rule] is
   literally the rule the trie-join semantics verifies -- no retyping adapter.  Aggregation is
   still unsupported: the lowering ([DistributedDatalogToHardwareCompiler.global_rename_rule]/[compile_rule]) only ever
   emits [normal_rule]s and ERRORS (result monad) on [meta_rule]/[agg_rule], so a lowered program
   is normal by construction.  A lowered atom is a [Datalog.clause] ([clause_rel]/[clause_args]);
   a ground lowered fact is a [Datalog.fact] ([normal_fact]). *)
Definition lowered_expr := Datalog.expr var fn_id.
Definition lowered_fact := Datalog.clause rel_id var fn_id.
Definition lowered_rule := Datalog.rule rel_id var fn_id aggregator.
Definition lowered_program := list lowered_rule.

Record join :=
{
  tries : list trie_id;
  trie_levels : permutation;
  clauses : list clause_id
}.

Definition query := list join.

Record join_output :=
{
  output_rel : rel_id;
  output_var_indices : list nat
}.

Record hardware_rule :=
{
  hhyps : query;
  hconcls : list join_output;
  (* per-clause signatures (relation, arity): each hypothesis fact must have this relation and
     this many columns.  A rule fires only on facts of this shape, making the hardware semantics
     as strict as datalog's. *)
  hsig : list (rel_id * nat);
}.

Definition hardware_program := list hardware_rule.

Definition trie_ids := list trie_id.

End HardwareProgram.