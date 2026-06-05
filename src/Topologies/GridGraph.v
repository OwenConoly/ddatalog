From Stdlib Require Import List Bool ZArith.Znat Lia.
From DatalogRocq Require Import Topologies.Graph.
From coqutil Require Import Datatypes.List.
Import ListNotations.

Section GridGraph.

  Definition Node : Type := list nat.
  Definition Dimensions : Type := list nat.

  Variable dims : Dimensions.

  Definition node_eqb (n1 n2 : Node) : bool := list_eqb Nat.eqb n1 n2.

  Lemma node_eqb_spec :
    forall n1 n2 : Node,
      BoolSpec (n1 = n2) (n1 <> n2) (node_eqb n1 n2).
  Proof.
    unfold node_eqb.
    apply list_eqb_spec.
  Qed.

  Inductive is_graph_node : Dimensions -> Node -> Prop :=
  | valid_nil : is_graph_node [] []
  | valid_cons : forall (d : nat) (ds : list nat) (coord : nat) (rest : Node),
      coord < d ->
      is_graph_node ds rest ->
      is_graph_node (d :: ds) (coord :: rest).

  Fixpoint check_node_in_bounds_h (coords dims : list nat) : bool :=
    match coords, dims with
    | [], [] => true
    | c :: cs, d :: ds => (c <? d) && check_node_in_bounds_h cs ds
    | _, _ => false
    end. 

  Definition check_node_in_bounds (n : Node) : bool :=
    check_node_in_bounds_h n dims.

  Lemma check_node_in_bounds_h_correct :
    forall n dims0,
      is_graph_node dims0 n <-> check_node_in_bounds_h n dims0 = true.
  Proof.
    intros n. split.
    - intros Hnode.
      induction Hnode.
      + simpl. reflexivity.
      + simpl. apply andb_true_iff. split.
        * apply Nat.ltb_lt. assumption.
        * apply IHHnode.
    - revert n.
      induction dims0 as [| d ds IH]; intros n Hcheck.
      + destruct n; [constructor | simpl in Hcheck; inversion Hcheck].
      + destruct n as [| c cs].
        * simpl in Hcheck. inversion Hcheck.
        * simpl in Hcheck. apply andb_true_iff in Hcheck. destruct Hcheck as [Hc Hrest].
          apply Nat.ltb_lt in Hc.
          constructor; try assumption.
          apply IH. assumption.
  Qed.

  Lemma check_node_in_bounds_correct :
    forall n,
      is_graph_node dims n <-> check_node_in_bounds n = true.
  Proof.
    intros n.
    apply check_node_in_bounds_h_correct.
  Qed.

  Definition abs (c1 c2 : nat) : nat := Nat.max (c1 - c2) (c2 - c1).

  (* This definition says if a node is n steps away from another node by manhattan distance,
     and here we don't care about the dimensions *)
  Inductive manhattan_distance : nat -> Node -> Node -> Prop := 
  | neighbor_zero_steps : forall n,
      manhattan_distance 0 n n
  | neighbor_steps : forall prev_diff next_coord_diff n1 n2 c1 c2,
      manhattan_distance prev_diff n1 n2 -> 
      abs c1 c2 = next_coord_diff -> 
      manhattan_distance (prev_diff + next_coord_diff) (c1 :: n1) (c2 :: n2).
    
  (* Simple adjacency: differs by +1 on exactly one coordinate *)
  Inductive is_graph_edge : Dimensions -> Node -> Node -> Prop := 
  | valid_edge : forall (dims : Dimensions) (u v : Node),
                 is_graph_node dims u ->
                 is_graph_node dims v -> 
                 manhattan_distance 1 u v ->
                 is_graph_edge dims u v.

  Fixpoint is_mth_neighbor (n1 n2 : Node) (m : nat) : bool :=
    match n1, n2 with 
    | [], [] => if m =? 0 then true else false
    | c :: cs, c' :: cs' => 
      if m <? (abs c c') then false 
      else is_mth_neighbor cs cs' (m - (abs c c'))
    | _, _ => false
    end.

  Definition is_neighbor (n1 n2 : Node) : bool :=
   check_node_in_bounds n1 &&
   check_node_in_bounds n2 &&
   is_mth_neighbor n1 n2 1.

  Lemma abs_same : forall n, abs n n = 0.
  Proof. 
    induction n; auto. 
  Qed.

  Lemma is_mth_neighbor_self : forall n,
    is_mth_neighbor n n 0 = true.
  Proof.
    induction n; auto.
    simpl. rewrite abs_same. simpl.
    apply IHn.
  Qed.

  Lemma is_mth_neighbor_is_manhattan_distance : forall n1 n2 m, 
    is_mth_neighbor n1 n2 m = true <-> manhattan_distance m n1 n2.
  Proof.
    split.
    - revert n2. revert m. induction n1; intros m n2 H.
      + destruct n2; simpl in H.
        * destruct m; try discriminate. econstructor.
        * destruct m; try discriminate.
      + destruct n2.
        * simpl in H. discriminate.
        * simpl in H. destruct (m <? abs a n) eqn:Hcomp; try discriminate.
          assert (abs a n <= m) by (apply Nat.ltb_ge; exact Hcomp).
          replace m with ((m - (abs a n)) + (abs a n)) by lia.
          econstructor; eauto.
    - induction 1.
      + apply is_mth_neighbor_self.
      + simpl. subst. assert (prev_diff + abs c1 c2 <? abs c1 c2 = false).
        { apply Nat.ltb_ge. lia. }
        rewrite H0. rewrite Nat.add_sub; try lia.
        apply IHmanhattan_distance.
  Qed.

  Lemma is_neighbor_correct : forall n1 n2,
    is_neighbor n1 n2 = true <-> is_graph_edge dims n1 n2.
  Proof.
    intros n1 n2. split.
    - intros Hneighbor.
      unfold is_neighbor in Hneighbor.
      apply andb_true_iff in Hneighbor.
      destruct Hneighbor as [Hrest Hmth].
      apply andb_true_iff in Hrest.
      destruct Hrest as [Hn1 Hn2].
      apply check_node_in_bounds_correct in Hn1.
      apply check_node_in_bounds_correct in Hn2.
      apply is_mth_neighbor_is_manhattan_distance in Hmth.
      econstructor; eauto.
    - intros Hedge.
      unfold is_neighbor.
      apply andb_true_iff. split.
      + apply andb_true_iff. split.
        * apply check_node_in_bounds_correct. inversion Hedge; assumption.
        * apply check_node_in_bounds_correct. inversion Hedge; assumption.
      + apply is_mth_neighbor_is_manhattan_distance. inversion Hedge; assumption.
  Qed.

  (* The actual graph *)
  Definition GridGraph : Graph.Graph :=
    {|
      nodes := is_graph_node dims;
      edge  := is_graph_edge dims
    |}.

  Theorem good_graph : Graph.good_graph GridGraph.
  Proof.
    unfold Graph.good_graph.
    intros n1 n2 Hedge.
    split; inversion Hedge; assumption.
  Qed.

  Definition add_dimension (ln : list Node) (i : nat) : list Node :=
    map (fun n => i :: n) ln.

  Lemma add_dimension_length :
    forall (ln : list Node) (i : nat),
      length (add_dimension ln i) = length ln.
  Proof.
    intros. induction ln; eauto.
    simpl. rewrite IHln. reflexivity.
  Qed.

  Fixpoint all_nodes_h (dims : list nat) : list Node :=
    match dims with
    | [] => [[]]
    | d :: ds =>
        let rest := all_nodes_h ds in
        flat_map (add_dimension rest) (seq 0 d)
    end.
  
  Definition all_nodes : list Node := all_nodes_h dims.

  Lemma all_nodes_h_correct : forall (n : Node),
    is_graph_node dims n <-> In n (all_nodes_h dims).
  Proof.
    intros n. split.
    - intros Hnode.
      induction Hnode.
      + simpl. left. reflexivity.
      + simpl. apply in_flat_map. 
        exists coord. split.
        * apply in_seq. simpl. lia.
        * apply in_map. apply IHHnode.
    - revert n.
      induction dims as [| d ds IH]; intros n Hin; simpl in Hin.
    + destruct Hin as [H | H]; [subst; constructor | inversion H].
    + apply in_flat_map in Hin.
      destruct Hin as [r [Hin_seq Hin_map]].
      apply in_map_iff in Hin_map.
      destruct Hin_map as [rest [Heq Hin_rest]].
      subst n.
      constructor.
      * apply in_seq in Hin_seq. lia.
      * apply IH. assumption.
  Qed.

  Theorem all_nodes_correct : forall (n : Node),
    is_graph_node dims n <-> In n (all_nodes).
  Proof.
    intros n. unfold all_nodes.
    apply all_nodes_h_correct.
  Qed.

  Lemma length_flatmap_nonzero :
    forall (A B : Type) (f : A -> list B) (l : list A),
      (exists a, In a l /\ length (f a) > 0) ->
      length (flat_map f l) > 0.
  Proof.
    induction l; simpl; intros.
    - destruct H. destruct H. destruct H.
    - rewrite length_app. destruct H.
      destruct H. destruct H.
      + subst. lia.
      + assert (length (flat_map f l) > 0).
        { apply IHl; exists x; split; assumption. }
        lia.
  Qed.
  
  Theorem all_nodes_nonzero_dim_nonempty :
    forall dims0,
      (forall d, In d dims0 -> d > 0) ->
      length (all_nodes_h dims0) > 0.
  Proof.
    intros. induction dims0.
    - simpl. lia.
    - simpl. apply length_flatmap_nonzero. destruct a.
      + specialize (H 0). simpl in H. lia.
      + exists 0. split.
        * apply in_seq. lia.
        * intros. rewrite add_dimension_length. apply IHdims0.
          intros. apply H. right. assumption.
  Qed.

(* Reachability via edges *)
  Inductive grid_reachable : Dimensions -> Node -> Node -> Prop :=
  | reach_refl : forall dims0 n,
      is_graph_node dims0 n ->
      grid_reachable dims0 n n
  | reach_step : forall dims0 n1 n2 n3,
      is_graph_edge dims0 n1 n2 ->
      grid_reachable dims0 n2 n3 ->
      grid_reachable dims0 n1 n3.

  Lemma grid_reachable_trans :
    forall dims0 n1 n2 n3,
      grid_reachable dims0 n1 n2 ->
      grid_reachable dims0 n2 n3 ->
      grid_reachable dims0 n1 n3.
  Proof.
    intros dims0 n1 n2 n3 H12 H23.
    induction H12.
    - exact H23.
    - eapply reach_step; eauto.
  Qed.

  (* abs properties *)
  Lemma abs_comm : forall a b, abs a b = abs b a.
  Proof.
    unfold abs. intros. lia.
  Qed.

  Lemma abs_succ : forall a b,
      a < b -> abs a b = S (abs (S a) b).
  Proof.
    unfold abs. intros. lia.
  Qed.

  Lemma abs_pred : forall a b,
      a > b -> abs a b = S (abs (a - 1) b).
  Proof.
    unfold abs. intros. lia.
  Qed.

  Lemma abs_adjacent_l : forall a b,
      a < b -> abs a (S a) = 1.
  Proof.
    unfold abs. intros. lia.
  Qed.

  Lemma abs_n_Sn : forall n, abs n (S n) = 1.
  Proof.
    unfold abs. intros. lia.
  Qed.

  Lemma abs_Sn_n : forall n, abs (S n) n = 1.
  Proof.
    unfold abs. intros. lia.
  Qed.

  (* Manhattan distance for nodes that share a tail *)
  Lemma manhattan_distance_cons_same :
    forall c rest,
      manhattan_distance 0 rest rest ->
      manhattan_distance 0 (c :: rest) (c :: rest).
  Proof.
    intros.
    replace 0 with (0 + 0) by lia.
    econstructor; eauto.
  Qed.

  Lemma manhattan_distance_cons_diff :
    forall c1 c2 rest,
      manhattan_distance 0 rest rest ->
      manhattan_distance (abs c1 c2) (c1 :: rest) (c2 :: rest).
  Proof.
    intros.
    replace (abs c1 c2) with (0 + abs c1 c2) by lia.
    econstructor; eauto.
  Qed.

  Lemma manhattan_distance_refl :
    forall n, manhattan_distance 0 n n.
  Proof.
    induction n.
    - constructor.
    - replace 0 with (0 + 0) by lia.
      econstructor; eauto.
  Qed.

  (* Two nodes differing by 1 in the first coordinate are neighbors *)
  Lemma edge_step_first_coord :
    forall d ds c rest,
      c + 1 < d ->
      is_graph_node ds rest ->
      is_graph_edge (d :: ds) (c :: rest) (S c :: rest).
  Proof.
    intros.
    econstructor.
    - constructor; [lia | assumption].
    - constructor; [lia | assumption].
    - replace 1 with (0 + abs c (S c)) by (rewrite abs_n_Sn; lia).
      econstructor; eauto.
      apply manhattan_distance_refl.
  Qed.

  Lemma edge_step_first_coord_down :
    forall d ds c rest,
      c > 0 ->
      c < d ->
      (c - 1) < d ->
      is_graph_node ds rest ->
      is_graph_edge (d :: ds) (c :: rest) ((c - 1) :: rest).
  Proof.
    intros.
    econstructor.
    - constructor; [lia | assumption].
    - constructor; [lia | assumption].
    - replace 1 with (0 + abs c (c - 1)).
      + econstructor; eauto; try apply manhattan_distance_refl. unfold abs.
        lia.
      + unfold abs. lia.
  Qed.

  (* Walking along the first coordinate *)
  Lemma walk_first_coord :
    forall d ds c1 c2 rest,
      c1 < d ->
      c2 < d ->
      is_graph_node ds rest ->
      grid_reachable (d :: ds) (c1 :: rest) (c2 :: rest).
  Proof.
    intros d ds c1 c2 rest Hc1 Hc2 Hrest.
    destruct (Nat.eq_dec c1 c2) as [-> | Hneq].
    - apply reach_refl. constructor; auto.
    - destruct (Nat.lt_ge_cases c1 c2) as [Hlt | Hge].
      + (* c1 < c2: walk up *)
        induction c2 as [| c2' IH].
        * lia.
        * destruct (Nat.eq_dec c1 c2') as [-> | Hneq'].
          -- (* one step *)
            eapply reach_step.
            ++ apply edge_step_first_coord; auto. lia.
            ++ apply reach_refl. constructor; auto.
          -- (* IH then one more step *)
            assert (c1 < c2') by lia.
            eapply grid_reachable_trans.
            ++ apply IH; lia.
            ++ eapply reach_step.
               ** apply edge_step_first_coord; auto. lia.
               ** apply reach_refl. constructor; auto.
      + (* c1 >= c2: walk down *)
        induction c1 as [| c1' IH].
        * lia.
        * destruct (Nat.eq_dec c1' c2) as [-> | Hneq'].
          -- (* one step *)
            eapply reach_step.
            ++ apply edge_step_first_coord_down; auto; lia.
            ++ simpl. replace (c2 - 0) with c2 by lia. apply reach_refl. constructor; auto.
          -- (* one step then IH *)
            assert (c1' >= c2) by lia.
            eapply reach_step.
            ++ apply edge_step_first_coord_down; auto; lia.
            ++ simpl. replace (c1' - 0) with c1' by lia. apply IH; lia.
  Qed.

  (* Walking across all dimensions: change one coordinate at a time *)
  Lemma grid_connected_h :
    forall dims0 n1 n2,
      is_graph_node dims0 n1 ->
      is_graph_node dims0 n2 ->
      grid_reachable dims0 n1 n2.
  Proof.
    induction dims0 as [| d ds IH]; intros n1 n2 Hn1 Hn2.
    - inversion Hn1; subst. inversion Hn2; subst.
      apply reach_refl. constructor.
    - inversion Hn1; subst. inversion Hn2; subst.
      (* n1 = coord :: rest, n2 = coord0 :: rest0 *)
      (* Strategy: first walk from (coord :: rest) to (coord :: rest0)
         using IH on the tail, then walk from (coord :: rest0) to (coord0 :: rest0)
         along the first coordinate *)
      eapply grid_reachable_trans.
      + (* Walk the tail: (coord :: rest) -> (coord :: rest0) *)
        assert (Htail : grid_reachable ds rest rest0) by (apply IH; auto).
        clear -Htail H1 H5.
        induction Htail.
        * apply reach_refl. constructor; auto.
        * inversion H; subst.
          eapply reach_step.
          -- apply (valid_edge (d :: dims0) (coord :: n1) (coord :: n2)).
             ++ constructor; eauto.
             ++ constructor; eauto.
             ++ replace 1 with (1 + 0) by lia.
                apply (neighbor_steps 1 0 n1 n2 coord coord).
                ** exact H6.
                ** apply abs_same.
          -- apply IHHtail; auto.
             constructor; auto.
      + (* Walk the head: (coord :: rest0) -> (coord0 :: rest0) *)
        apply walk_first_coord; auto.
  Qed.

  Theorem grid_connected :
    forall n1 n2,
      is_graph_node dims n1 ->
      is_graph_node dims n2 ->
      grid_reachable dims n1 n2.
  Proof.
    apply grid_connected_h.
  Qed.
  
  Definition all_edges : list (Node * Node) :=
      filter (fun '(n1, n2) => is_neighbor n1 n2)
        (list_prod all_nodes all_nodes).
 
  Lemma all_edges_correct : forall n1 n2,
    is_graph_edge dims n1 n2 <-> In (n1, n2) all_edges.
  Proof.
    intros n1 n2.
    unfold all_edges.
    rewrite filter_In.
    rewrite in_prod_iff.
    repeat (rewrite <- all_nodes_correct).
    rewrite is_neighbor_correct.
    split.
    - intros Hedge.
      inversion Hedge; subst.
      auto.
    - intros [[Hn1 Hn2] Hedge].
      exact Hedge.
  Qed.

End GridGraph.