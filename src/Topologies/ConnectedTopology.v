(* ConnectedTopology: an ABSTRACT topology interface and a GENERIC proof that any topology
   satisfying it yields a [good_network] for any checked layout.

   The point: [good_network] is not a property of any particular graph -- it only needs a
   handful of topology facts (a finite node enumeration, a well-formed graph, forwarding that
   only travels along edges, forwarding-*connectivity*, no external input, and output
   everywhere).  We bundle exactly those into [connected_topology] and prove [good_network]
   from them alone -- never touching grid (or any other) specifics.  A grid is then just one
   instance; so is any other topology we care to build. *)

From Stdlib Require Import List Bool.
From Datalog Require Import Datalog Eqb.
From DatalogRocq Require Import DistributedDatalog Topologies.Graph.
From coqutil Require Import Map.Interface Eqb Tactics.destr.
Import ListNotations.

Section ConnectedTopology.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context {Node : Type}.
  Context {node_eqb : Node -> Node -> bool}
          {node_eqb_spec : forall x y : Node, BoolSpec (x = y) (x <> y) (node_eqb x y)}.

  Context {rule_eqb : Eqb rule} {rule_eqb_ok : Eqb_ok rule_eqb}.

  (* The abstract interface: every fact about a topology that [good_network] depends on, and
     nothing else.  All program-/layout-dependent obligations are theorem hypotheses below;
     this record is purely about the topology. *)
  Record connected_topology := {
    ct_graph    : Graph (Node := Node);
    ct_forward  : Node -> rel -> list Node;
    ct_input    : Node -> fact -> Prop;
    ct_output   : Node -> rel -> Prop;
    (* a finite enumeration of the graph's nodes *)
    ct_all_nodes      : list Node;
    ct_all_nodes_spec : forall n, In n ct_all_nodes <-> ct_graph.(nodes) n;
    (* the graph is well-formed *)
    ct_good_graph     : good_graph ct_graph;
    (* forwarding only ever travels along edges (and between real nodes) *)
    ct_forward_sound  : forall n1 n2 r, In n2 (ct_forward n1 r) ->
                          ct_graph.(nodes) n1 /\ ct_graph.(nodes) n2 /\ ct_graph.(edge) n1 n2;
    (* CONNECTIVITY: any two nodes are joined by a forwarding path *)
    ct_connected      : forall r n1 n2, ct_graph.(nodes) n1 -> ct_graph.(nodes) n2 ->
                          n1 = n2 \/ forwarding_reachable ct_forward r n1 n2;
    (* no facts are injected from outside *)
    ct_no_input       : forall n f, ~ ct_input n f;
    (* every (real) node will output every relation *)
    ct_output_total   : forall n r, ct_graph.(nodes) n -> ct_output n r;
    (* STREAMING: a designated (real) input node per relation, where external base facts of that
       relation enter and are forwarded from. *)
    ct_input_node      : rel -> Node;
    ct_input_node_real : forall r, ct_graph.(nodes) (ct_input_node r);
  }.

  (* The dataflow network obtained by running layout [L] on topology [ct]. *)
  Definition net_of (ct : connected_topology) (L : Node -> list rule) : DataflowNetwork :=
    {| DistributedDatalog.graph   := ct_graph ct;
       DistributedDatalog.forward := ct_forward ct;
       DistributedDatalog.input   := ct_input ct;
       DistributedDatalog.output  := ct_output ct;
       DistributedDatalog.layout  := L |}.

  (* A layout only ever places rules on real nodes of the topology. *)
  Definition layout_valid_nodes (ct : connected_topology) (L : Node -> list rule) : Prop :=
    forall n r, In r (L n) -> (ct_graph ct).(nodes) n.

  (* Generic decidable layout check over the topology's node enumeration:
     (1) every rule placed on a node is a program rule, and
     (2) every program rule is placed on some node. *)
  Definition node_rules_ok (L : Node -> list rule) (program : list rule) (n : Node) : bool :=
    forallb (fun r => existsb (eqb r) program) (L n).
  Definition rule_in_layout (all : list Node) (L : Node -> list rule) (r : rule) : bool :=
    existsb (fun n => existsb (eqb r) (L n)) all.
  Definition check_layout (ct : connected_topology) (L : Node -> list rule) (program : list rule) : bool :=
    forallb (node_rules_ok L program) (ct_all_nodes ct) &&
    forallb (rule_in_layout (ct_all_nodes ct) L) program.

  (* GENERIC good_layout: every program rule lives somewhere, and the layout only assigns
     program rules to real nodes -- straight from the checker + valid-nodes side condition. *)
  Theorem good_layout_ct (ct : connected_topology) (L : Node -> list rule) (program : list rule) :
    layout_valid_nodes ct L ->
    check_layout ct L program = true ->
    good_layout L (ct_graph ct).(nodes) program.
  Proof.
    intros Hvalid Hcheck.
    unfold good_layout. unfold check_layout in Hcheck.
    apply andb_true_iff in Hcheck. destruct Hcheck as [H_nodes_ok H_rule_in_layout].
    rewrite forallb_forall in H_nodes_ok. rewrite forallb_forall in H_rule_in_layout.
    split.
    - apply Forall_forall. intros r Hr.
      apply H_rule_in_layout in Hr as H_layout.
      unfold rule_in_layout in H_layout. rewrite existsb_exists in H_layout.
      destruct H_layout as [n [H_n_in_nodes H_r_in_layout]].
      rewrite existsb_exists in H_r_in_layout.
      destruct H_r_in_layout as [r' [Hin H_r_eq]].
      exists n. cbv [eqb] in H_r_eq. destr (rule_eqb r r').
      + subst. split; [apply (ct_all_nodes_spec ct); exact H_n_in_nodes | exact Hin].
      + discriminate H_r_eq.
    - intros n r H0. split.
      + apply (Hvalid n r H0).
      + pose proof (Hvalid n r H0) as Hgn.
        apply (ct_all_nodes_spec ct) in Hgn.
        specialize (H_nodes_ok n Hgn).
        unfold node_rules_ok in H_nodes_ok. rewrite forallb_forall in H_nodes_ok.
        specialize (H_nodes_ok r H0). rewrite existsb_exists in H_nodes_ok.
        destruct H_nodes_ok as [r' [Hin H_r_eq]].
        cbv [eqb] in H_r_eq. destr (rule_eqb r r'); [subst; exact Hin | discriminate H_r_eq].
  Qed.

  (* THE GENERIC THEOREM: any topology satisfying [connected_topology], run with any layout that
     passes the checker (and only assigns to real nodes), yields a [good_network].  The proof
     uses only the interface fields -- no grid, no concrete coordinates. *)
  Theorem good_network_ct_gl (ct : connected_topology) (L : Node -> list rule) (program : list rule) :
    layout_valid_nodes ct L ->
    good_layout L (ct_graph ct).(nodes) program ->
    good_network (net_of ct L) program.
  Proof.
    intros Hvalid Hgl.
    unfold net_of, good_network. simpl. split.
    - apply (ct_good_graph ct).
    - split.
      + exact Hgl.
      + split.
        * unfold good_forwarding, good_forwarding_sound. simpl. split.
          ** intros n1 n2 r H. apply (ct_forward_sound ct n1 n2 r H).
          ** unfold good_forwarding_complete. simpl. intros rel0. split.
             --- intros n_prod n_cons Hprod Hcons.
                 assert (Hn_prod : (ct_graph ct).(nodes) n_prod).
                 { destruct Hprod as [rl [Hin_layout _]].
                   apply (Hvalid n_prod rl Hin_layout). }
                 assert (Hn_cons : (ct_graph ct).(nodes) n_cons).
                 { destruct Hcons as [r [Hin_layout _]]. apply (Hvalid n_cons r Hin_layout). }
                 apply (ct_connected ct rel0 n_prod n_cons Hn_prod Hn_cons).
             --- intros n_prod Hprod. exists n_prod.
                 assert (Hn_prod : (ct_graph ct).(nodes) n_prod).
                 { destruct Hprod as [rl [Hin_layout _]].
                   apply (Hvalid n_prod rl Hin_layout). }
                 split.
                 +++ apply (ct_output_total ct n_prod rel0 Hn_prod).
                 +++ left; reflexivity.
        * split.
          ** unfold good_input. intros n f H. exfalso. apply (ct_no_input ct n f H).
          ** unfold good_output. simpl. intros n f H. exists n.
             assert (Hn : (ct_graph ct).(nodes) n).
             { destruct H as [rl [Hin_layout _]]. apply (Hvalid n rl Hin_layout). }
             split.
             --- exact Hn.
             --- apply (ct_output_total ct n (rel_of f) Hn).
  Qed.

  (* The original [good_network_ct]: discharge [good_layout] from the decidable checker. *)
  Theorem good_network_ct (ct : connected_topology) (L : Node -> list rule) (program : list rule) :
    layout_valid_nodes ct L ->
    check_layout ct L program = true ->
    good_network (net_of ct L) program.
  Proof.
    intros Hvalid Hcheck.
    apply good_network_ct_gl; [exact Hvalid | apply good_layout_ct; assumption].
  Qed.

  (* The CANONICAL program of a layout on a topology: the union of every (real) node's rules.
     [good_layout] holds for it structurally -- no rule equality / checker needed -- so it is the
     natural reference program to state correctness against when no program is supplied. *)
  Definition canonical_program (ct : connected_topology) (L : Node -> list rule) : list rule :=
    flat_map L (ct_all_nodes ct).

  Theorem good_layout_canonical (ct : connected_topology) (L : Node -> list rule) :
    layout_valid_nodes ct L ->
    good_layout L (ct_graph ct).(nodes) (canonical_program ct L).
  Proof.
    intros Hvalid. unfold good_layout, canonical_program. split.
    - apply Forall_forall. intros r Hr. apply in_flat_map in Hr.
      destruct Hr as [n [Hn Hrn]]. exists n. split.
      + apply (proj1 (ct_all_nodes_spec ct n)). exact Hn.
      + exact Hrn.
    - intros n r H0. split.
      + apply (Hvalid n r H0).
      + apply in_flat_map. exists n. split.
        * apply (proj2 (ct_all_nodes_spec ct n)). apply (Hvalid n r H0).
        * exact H0.
  Qed.

  Theorem good_network_canonical (ct : connected_topology) (L : Node -> list rule) :
    layout_valid_nodes ct L ->
    good_network (net_of ct L) (canonical_program ct L).
  Proof.
    intros Hvalid.
    apply good_network_ct_gl; [exact Hvalid | apply good_layout_canonical; exact Hvalid].
  Qed.

  (*==========================================================================*)
  (*  STREAMING: base facts [Q] enter at per-relation input nodes              *)
  (*==========================================================================*)

  (* The streaming dataflow network for layout [L] and base facts [Q]: identical to [net_of]
     except its input injects each base fact [f] at the input node for [f]'s relation. *)
  Definition net_of_streaming (ct : connected_topology) (L : Node -> list rule)
      (Q : fact -> Prop) : DataflowNetwork :=
    {| DistributedDatalog.graph   := ct_graph ct;
       DistributedDatalog.forward := ct_forward ct;
       DistributedDatalog.input   := fun n f => Q f /\ n = ct_input_node ct (rel_of f);
       DistributedDatalog.output  := ct_output ct;
       DistributedDatalog.layout  := L |}.

  (* In a connected topology every (real) node is a good source for every relation: by
     connectivity it reaches every (real) consumer, and by [ct_output_total] it itself outputs. *)
  Lemma good_source_ct (ct : connected_topology) (L : Node -> list rule)
      (Q : fact -> Prop) (n : Node) (R : rel) :
    layout_valid_nodes ct L ->
    (ct_graph ct).(nodes) n ->
    good_source (net_of_streaming ct L Q) n R.
  Proof.
    intros Hvalid Hn. unfold good_source, net_of_streaming. cbn. split.
    - intros n_cons Hcons.
      assert (Hcons_real : (ct_graph ct).(nodes) n_cons).
      { destruct Hcons as [rl [Hin _]]. apply (Hvalid n_cons rl Hin). }
      apply (ct_connected ct R n n_cons Hn Hcons_real).
    - exists n. split; [apply (ct_output_total ct n R Hn) | left; reflexivity].
  Qed.

  (* THE STREAMING GENERIC THEOREM: any connected topology, run with any checked layout, yields a
     [good_network_streaming] for any base facts [Q] -- base facts enter at the per-relation input
     nodes and forward to every consumer. *)
  Theorem good_network_streaming_ct (ct : connected_topology) (L : Node -> list rule)
      (program : list rule) (Q : fact -> Prop) :
    layout_valid_nodes ct L ->
    check_layout ct L program = true ->
    good_network_streaming (net_of_streaming ct L Q) program Q.
  Proof.
    intros Hvalid Hcheck. unfold good_network_streaming, net_of_streaming. cbn.
    split; [exact (ct_good_graph ct) |].
    split; [apply good_layout_ct; assumption |].
    split; [intros n1 n2 r H; apply (ct_forward_sound ct n1 n2 r H) |].
    split.
    - intros n_prod R Hprod.
      assert (Hn_prod_real : (ct_graph ct).(nodes) n_prod).
      { destruct Hprod as [rl [Hin _]]. apply (Hvalid n_prod rl Hin). }
      apply (good_source_ct ct L Q n_prod R Hvalid Hn_prod_real).
    - split.
      + intros n f [HQ _]. exact HQ.
      + intros f HQ. exists (ct_input_node ct (rel_of f)). split.
        * split; [exact HQ | reflexivity].
        * apply (good_source_ct ct L Q _ (rel_of f) Hvalid (ct_input_node_real ct (rel_of f))).
  Qed.

  Theorem good_network_streaming_canonical (ct : connected_topology) (L : Node -> list rule)
      (Q : fact -> Prop) :
    layout_valid_nodes ct L ->
    good_network_streaming (net_of_streaming ct L Q) (canonical_program ct L) Q.
  Proof.
    intros Hvalid. unfold good_network_streaming, net_of_streaming. cbn.
    split; [exact (ct_good_graph ct) |].
    split; [apply good_layout_canonical; exact Hvalid |].
    split; [intros n1 n2 r H; apply (ct_forward_sound ct n1 n2 r H) |].
    split.
    - intros n_prod R Hprod.
      assert (Hn_prod_real : (ct_graph ct).(nodes) n_prod).
      { destruct Hprod as [rl [Hin _]]. apply (Hvalid n_prod rl Hin). }
      apply (good_source_ct ct L Q n_prod R Hvalid Hn_prod_real).
    - split.
      + intros n f [HQ _]. exact HQ.
      + intros f HQ. exists (ct_input_node ct (rel_of f)). split.
        * split; [exact HQ | reflexivity].
        * apply (good_source_ct ct L Q _ (rel_of f) Hvalid (ct_input_node_real ct (rel_of f))).
  Qed.

End ConnectedTopology.
