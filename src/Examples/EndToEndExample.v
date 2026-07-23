(* END-TO-END example: from a source datalog program + an indexed layout, run the real compiler,
   discharge the (decidable) side checks BY COMPUTATION, and obtain a PROOF OF EQUIVALENCE between
   the compiled distributed hardware network and the original program.

   The headline theorem [DistributedDatalogToHardwareCompilerCorrect.compile_implements_source] is
   stated generically (over arbitrary map instances).  Here we:
     1. pin every instance to the string-datalog / grid-topology backend ([grid_equiv]);
     2. give a concrete program  J(x,y) :- A(x,y), B(y,x)  and a one-node indexed layout;
     3. run the compiler ([compiled_J]) and its relabel pass ([lowered_J]) and show both SUCCEED;
     4. discharge the boolean side checks [bare_layoutb] / [layout_distributes_programb] by [vm_compute];
     5. conclude [end_to_end_equiv]: for the compiler's output [ninfos] (and the renamed tables it
        emits), the distributed run derives the renamed [fsrc] iff the source program derives [fsrc].

   Note on performance: proving  compile ... = Success ninfos  as a full Leibniz equality is slow,
   because the kernel re-checks the [eq_refl] sortedness proofs inside every emitted sorted-list map
   (string-keyed) WITHOUT the VM.  So the equivalence takes the compiler's outputs as hypotheses
   ([Hcompile]/[Hlower]); that those equations hold is witnessed cheaply by [compiled_J_ok] /
   [lowered_J_ok] (a [match ... => True], which never forces the map proofs).  The boolean checks,
   by contrast, reduce to [true = true] and are cheap.

   A successful build IS the test. *)

From Stdlib Require Import List String.
From coqutil Require Import Map.Interface Map.SortedListString Result.
From Datalog Require Import Datalog.
From DatalogRocq Require Import
  DistributedDatalogToHardwareCompilerCorrect
  DistributedDatalogToHardwareCompiler
  StringDatalogParams StringDatalog StringGridCompiler
  GridTopology GridGraph SortedListNat
  DistributedHardwareProgram DistributedHardwareSemantics
  DependencyGenerator RelabelCorrect.
Import ListNotations.
Open Scope string_scope.

(* Trivial value-signatures for the bare fragment (no functions / no aggregation). *)
#[local] Instance sig_hw  : signature nat    unit string :=
  {| interp_fun := fun _ _ => None;
     get_nat := fun _ => 0; agg_bop := fun _ x _ => x; agg_id := fun _ => "" |}.
#[local] Instance sig_src : signature string unit string :=
  {| interp_fun := fun _ _ => None;
     get_nat := fun _ => 0; agg_bop := fun _ x _ => x; agg_id := fun _ => "" |}.


(*==========================================================================*)
(*  [grid_equiv]: [compile_implements_source] with every instance pinned to   *)
(*  the string-datalog / grid-topology backend.  A reusable, instance-free    *)
(*  statement quantified only over the program / layout / facts.              *)
(*==========================================================================*)

Definition grid_equiv :=
  @compile_implements_source
    string string string unit string
    _ _
    sig_hw
    (SortedListString.map string) (SortedListString.ok string)
    StringDatalog.var_idx_map  (SortedListString.ok nat)
    StringDatalog.var_node_set (SortedListString.ok unit)
    StringDatalog.var_edge_set
    GridTopology.node_id GridTopology.node_id GridTopology.node_id_eqb GridTopology.node_id_eqb_spec
    _ _
    (GridTopology.node_id_map unit) (GridTopology.node_id_map (GridTopology.node_id_map unit))
    (SortedListNat.map (list (@DistributedHardwareProgram.destination GridTopology.node_id)))
    (SortedListNat.map (GridTopology.node_id_map unit))
    StringDatalog.fn_id_map StringDatalog.rel_relid_map
    (GridTopology.node_id_map (list rule)) (GridTopology.node_id_map_ok _)
    (GridTopology.node_id_map (list (lowered_rule)))
        (GridTopology.node_id_map_ok _)
    (GridTopology.node_id_map (SortedListNat.map (list (@DistributedHardwareProgram.destination GridTopology.node_id))))
    (SortedListString.map (list GridTopology.node_id)) (SortedListString.ok _)
    (SortedListNat.map (list GridTopology.node_id))    (SortedListNat.ok _)
    (SortedListNat.ok _)
    (GridTopology.node_id_map_ok _)
    (GridTopology.node_id_map_ok _)
    (GridTopology.node_id_map_ok _)
    sig_src
    (SortedListString.ok _)
    _ _.

(*==========================================================================*)
(*  The concrete program and indexed layout.                                  *)
(*==========================================================================*)

(* J(x, y) :- A(x, y), B(y, x). *)
Definition ruleJ : rule :=
  Datalog.normal_rule
    [ {| Datalog.clause_rel := "J"; Datalog.clause_args := [Datalog.var_expr "x"; Datalog.var_expr "y"] |} ]
    [ {| Datalog.clause_rel := "A"; Datalog.clause_args := [Datalog.var_expr "x"; Datalog.var_expr "y"] |} ;
      {| Datalog.clause_rel := "B"; Datalog.clause_args := [Datalog.var_expr "y"; Datalog.var_expr "x"] |} ].

Definition P : list rule := [ruleJ].
Definition idx_layout : list (node_id * list nat) := [ ([0; 0]%nat, [0]%nat) ].  (* rule 0 -> node (0,0) *)
Definition topo : GridGraph.Dimensions := [1; 1]%nat.                            (* a 1x1 grid *)

(* The inputs to the generic compiler, exactly as [compile_program] builds them. *)
Definition LAYOUT := make_layout_map P idx_layout.
Definition FPS    := all_io_locations P idx_layout topo.
Definition G      := GridTopology.make_topo_graph topo.

(* The relabel pass with the grid instances pinned -- exactly the [lower_inputs] the theorem uses. *)
Notation lowerJ := (@DistributedDatalogToHardwareCompiler.lower_inputs
  string string string unit node_id node_id
  (GridTopology.node_id_map unit) (SortedListNat.map (GridTopology.node_id_map unit))
  StringDatalog.fn_id_map StringDatalog.rel_relid_map
  (GridTopology.node_id_map (list rule))
  (GridTopology.node_id_map (list (lowered_rule)))
  (SortedListString.map (list node_id)) (SortedListNat.map (list node_id))).

(*==========================================================================*)
(*  Step 1: the compiler runs, the relabel pass runs, and both SUCCEED.       *)
(*  ([match ... => True] never forces the sorted-map proofs, so this is cheap.)*)
(*==========================================================================*)

Definition compiled_J := Eval vm_compute in compile_program P idx_layout FPS FPS topo.
Definition lowered_J  := Eval vm_compute in lowerJ LAYOUT FPS FPS.

Example compiled_J_ok : match compiled_J with Success _ => True | _ => False end := I.
Example lowered_J_ok  : match lowered_J  with Success _ => True | _ => False end := I.

(*==========================================================================*)
(*  Step 2: the boolean side checks pass (these reduce to [true = true]).      *)
(*==========================================================================*)

Example check_bare        : bare_layoutb LAYOUT = true.                       Proof. vm_compute; reflexivity. Qed.
Example check_distributes : layout_distributes_programb P LAYOUT = true. Proof. vm_compute; reflexivity. Qed.

(*==========================================================================*)
(*  Step 3: THE END-TO-END EQUIVALENCE.                                        *)
(*  For the compiler's output [ninfos] and the renamed tables [ll/lfp/lfc/gc]  *)
(*  its relabel pass emits (the two [Success] equations, witnessed above by     *)
(*  [compiled_J_ok]/[lowered_J_ok]), and for any routable EDB [Qsrc] and any    *)
(*  queried fact [fsrc] of [P], the distributed run of the COMPILED network     *)
(*  parks the renamed [fsrc] at an output node  iff  [P] derives [fsrc].        *)
(*==========================================================================*)

Theorem end_to_end_equiv
    (ninfos : list (@node_info node_id (SortedListNat.map (list destination))))
    (ll  : GridTopology.node_id_map
             (list (lowered_rule)))
    (lfp lfc : @DistributedDatalogToHardwareCompiler.lowered_fact_locations node_id
                 (SortedListNat.map (list node_id)))
    (gc : @DistributedDatalogToHardwareCompiler.global_context string string node_id node_id
            (GridTopology.node_id_map unit) (SortedListNat.map (GridTopology.node_id_map unit))
            StringDatalog.fn_id_map StringDatalog.rel_relid_map)
    (Qsrc : @Datalog.fact string string -> Prop) (fsrc : @Datalog.fact string string) :
  compile_program P idx_layout FPS FPS topo = Success ninfos ->
  lowerJ LAYOUT FPS FPS = Success (ll, lfp, lfc, gc) ->
  In (Datalog.rel_of fsrc) (program_rels P) ->
  @edb_routable_src string string node_id (SortedListString.map (list node_id)) FPS Qsrc ->
  @run_ninfos string node_id GridTopology.node_id_eqb (SortedListNat.map (list destination))
    ninfos
    (fun n f0 => RelabelCorrect.relabel_Q (rho_gc gc) Qsrc f0 /\
                 In n (@rel_locs node_id (SortedListNat.map (list node_id)) lfp (Datalog.rel_of f0)))
    (fun n R  => In n (@rel_locs node_id (SortedListNat.map (list node_id)) lfc R))
    (RelabelCorrect.relabel_fact (rho_gc gc) fsrc)
  <-> Datalog.prog_impl P Qsrc fsrc.
Proof.
  intros Hcompile Hlower Hin Hedb.
  apply (grid_equiv LAYOUT FPS FPS G ninfos ll lfp lfc gc P Qsrc fsrc
           Hcompile Hlower);
    [ vm_compute; reflexivity   (* bare_layoutb LAYOUT = true *)
    | vm_compute; reflexivity
    | exact Hin
    | exact Hedb ].
Qed.

(*==========================================================================*)
(*  A SECOND, two-rule example: transitive closure, distributed over 2 nodes. *)
(*     Path(x, y) :- Edge(x, y).                                               *)
(*     Path(x, z) :- Edge(x, y), Path(y, z).                                   *)
(*  rule 0 is laid out on node (0,0), rule 1 on node (1,0), on a 2x1 grid; the *)
(*  compiler builds forwarding tables so [Path] facts flow between the nodes.  *)
(*  [grid_equiv] is program/layout-agnostic, so it is reused verbatim.         *)
(*==========================================================================*)

Definition Path (x y : string) : @Datalog.clause string string string :=
  {| Datalog.clause_rel := "Path"; Datalog.clause_args := [Datalog.var_expr x; Datalog.var_expr y] |}.
Definition Edge (x y : string) : @Datalog.clause string string string :=
  {| Datalog.clause_rel := "Edge"; Datalog.clause_args := [Datalog.var_expr x; Datalog.var_expr y] |}.

Definition r0 : rule := Datalog.normal_rule [Path "x" "y"] [Edge "x" "y"].
Definition r1 : rule := Datalog.normal_rule [Path "x" "z"] [Edge "x" "y"; Path "y" "z"].
Definition Preach : list rule := [r0; r1].

Definition idx_layout_r : list (node_id * list nat) :=
  [ ([0; 0]%nat, [0]%nat); ([1; 0]%nat, [1]%nat) ].  (* rule 0 -> (0,0), rule 1 -> (1,0) *)
Definition topo_r : GridGraph.Dimensions := [2; 1]%nat.  (* a 2x1 grid *)

Definition LAYOUT_r := make_layout_map Preach idx_layout_r.
Definition FPS_r    := all_io_locations Preach idx_layout_r topo_r.
Definition G_r      := GridTopology.make_topo_graph topo_r.

(* The compiler and its relabel pass run and SUCCEED (cheap head-constructor check). *)
Definition compiled_R := Eval vm_compute in compile_program Preach idx_layout_r FPS_r FPS_r topo_r.
Definition lowered_R  := Eval vm_compute in lowerJ LAYOUT_r FPS_r FPS_r.
Example compiled_R_ok : match compiled_R with Success _ => True | _ => False end := I.
Example lowered_R_ok  : match lowered_R  with Success _ => True | _ => False end := I.

(* The boolean side checks pass. *)
Example check_bare_r        : bare_layoutb LAYOUT_r = true.                              Proof. vm_compute; reflexivity. Qed.
Example check_distributes_r : layout_distributes_programb Preach LAYOUT_r = true. Proof. vm_compute; reflexivity. Qed.

Theorem end_to_end_equiv_reach
    (ninfos : list (@node_info node_id (SortedListNat.map (list destination))))
    (ll  : GridTopology.node_id_map
             (list (lowered_rule)))
    (lfp lfc : @DistributedDatalogToHardwareCompiler.lowered_fact_locations node_id
                 (SortedListNat.map (list node_id)))
    (gc : @DistributedDatalogToHardwareCompiler.global_context string string node_id node_id
            (GridTopology.node_id_map unit) (SortedListNat.map (GridTopology.node_id_map unit))
            StringDatalog.fn_id_map StringDatalog.rel_relid_map)
    (Qsrc : @Datalog.fact string string -> Prop) (fsrc : @Datalog.fact string string) :
  compile_program Preach idx_layout_r FPS_r FPS_r topo_r = Success ninfos ->
  lowerJ LAYOUT_r FPS_r FPS_r = Success (ll, lfp, lfc, gc) ->
  In (Datalog.rel_of fsrc) (program_rels Preach) ->
  @edb_routable_src string string node_id (SortedListString.map (list node_id)) FPS_r Qsrc ->
  @run_ninfos string node_id GridTopology.node_id_eqb (SortedListNat.map (list destination))
    ninfos
    (fun n f0 => RelabelCorrect.relabel_Q (rho_gc gc) Qsrc f0 /\
                 In n (@rel_locs node_id (SortedListNat.map (list node_id)) lfp (Datalog.rel_of f0)))
    (fun n R  => In n (@rel_locs node_id (SortedListNat.map (list node_id)) lfc R))
    (RelabelCorrect.relabel_fact (rho_gc gc) fsrc)
  <-> Datalog.prog_impl Preach Qsrc fsrc.
Proof.
  intros Hcompile Hlower Hin Hedb.
  apply (grid_equiv LAYOUT_r FPS_r FPS_r G_r ninfos ll lfp lfc gc
           Preach Qsrc fsrc Hcompile Hlower);
    [ vm_compute; reflexivity   (* bare_layoutb LAYOUT_r = true *)
    | vm_compute; reflexivity
    | exact Hin
    | exact Hedb ].
Qed.
