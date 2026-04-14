From JSON Require Import Encode Printer.
From Stdlib Require Import String List ZArith.
From coqutil Require Import Map.Interface Result.
From DatalogRocq Require Import EncodeLayout CompiledFamily.

Instance JEncode__node_id : JEncode node_id :=
  fun n => JSON__Object [("x", encode (fst n)); ("y", encode (snd n))].

Instance JEncode__join : JEncode join :=
  fun j =>
    JSON__Object [("tries", encode j.(tries));
                ("trie_levels", encode j.(trie_levels));
                ("clauses", encode j.(clauses))].

Instance JEncode__join_output : JEncode join_output := 
  fun jo =>
    JSON__Object [("output_rel", encode jo.(output_rel));
                ("output_var_indices", encode jo.(output_var_indices))].

Instance JEncode_hardware_rule : JEncode hardware_rule :=
  fun hr =>
    JSON__Object [("hhyps", encode hr.(hhyps));
                ("hconcls", encode hr.(hconcls))].

Instance JEncode__destination : JEncode destination := fun d =>
  match d with
  | DestEdge e => JSON__Object [("DestEdge", encode e)]
  | DestTrie t => JSON__Object [("DestTrie", encode t)]
  end.
  

Instance JEncode__pair A B `{JEncode A} `{JEncode B} : JEncode (A * B) :=
  fun '(a, b) => JSON__Array [encode a; encode b].


Instance JEncode_forwarding_table : JEncode (SortedListNat.map (list destination)) :=
  fun m => encode (map.fold (fun acc k v => (k, v) :: acc) [] m).

Instance JEncode__trie : JEncode trie :=
  fun t =>
    JSON__Object [("tid", encode t.(tid));
                ("trel", encode t.(trel));
                ("tperm", encode t.(tperm))].

Instance JEncode__node_info : JEncode node_info :=
  fun ni =>
    JSON__Object [("nid", encode ni.(nid));
                ("nprogram", encode ni.(nprogram));
                ("nforwarding", encode ni.(nforwarding));
                ("ntries", encode ni.(ntries))].


Instance JEncode__Result {A} `{JEncode A} : JEncode (result A) :=
  fun r =>
  match r with
  | Success a => encode a
  | Failure _ => JSON__String "Failed to compile"
  end.

Redirect "json_examples/compiled_family_program" Eval vm_compute in (to_string (encode compiled_family)).