From Stdlib Require Import List Bool.
From coqutil Require Import Eqb Tactics.fwd.
From GraphSearch Require Import Dag.
Import ListNotations.

(* Decides the channel dependency graph of Dally & Seitz 1986 Theorem 1, whose acyclicity is
   deadlock freedom. Deciding it lets a forwarding table be generated any way at all. *)

Section Acyclic.
  Context {V : Type} {V_eqb : Eqb V} {V_eqb_ok : Eqb_ok V_eqb}.
  Implicit Type g : list (V * V).

  Definition is_target g (v : V) : bool := existsb (fun e => eqb v (snd e)) g.

  (* An edge nothing points at can be peeled: it heads no cycle. *)
  Definition ready_edges g := filter (fun e => negb (is_target g (fst e))) g.
  Definition blocked_edges g := filter (fun e => is_target g (fst e)) g.

  Fixpoint acyclicb' (fuel : nat) g : bool :=
    match g with
    | [] => true
    | _ :: _ =>
        match fuel with
        | O => false
        | S fuel' =>
            match ready_edges g with
            | [] => false
            | _ :: _ => acyclicb' fuel' (blocked_edges g)
            end
        end
    end.

  (* Each round peels at least one edge, so the length is enough fuel to never reject wrongly. *)
  Definition acyclicb g : bool := acyclicb' (length g) g.

  Lemma dag_nil : dag (@nil (V * V)).
  Proof. intro x. constructor. intros y Hy. destruct Hy. Qed.

  Lemma is_target_false g v : is_target g v = false -> ~ In v (map snd g).
  Proof.
    unfold is_target. intros H Hin.
    rewrite <- Bool.not_true_iff_false in H. apply H.
    apply in_map_iff in Hin. destruct Hin as [e [Heq Hin]].
    apply existsb_exists. exists e. split; [assumption|].
    subst v. apply eqb_refl_true; eauto.
  Qed.

  Lemma in_ready g e : In e (ready_edges g) -> is_target g (fst e) = false.
  Proof.
    unfold ready_edges. intros H. apply filter_In in H. fwd.
    destruct (is_target g (fst e)); [discriminate | reflexivity].
  Qed.

  Lemma ready_incl g : incl (ready_edges g) g.
  Proof. unfold ready_edges, incl. intros a H. apply filter_In in H. apply H. Qed.

  Lemma blocked_incl g : incl (blocked_edges g) g.
  Proof. unfold blocked_edges, incl. intros a H. apply filter_In in H. apply H. Qed.

  (* Every source in [ready_edges] is a non-target of all of [g], so chains stop after one step. *)
  Lemma dag_ready g : dag (ready_edges g).
  Proof.
    intro x. constructor. intros y Hy. constructor. intros z Hz.
    exfalso.
    apply ready_incl in Hy.
    pose proof (in_ready _ _ Hz) as Hnt. simpl in Hnt.
    apply (is_target_false _ _ Hnt). apply in_map_iff. exists (x, y). split; auto.
  Qed.

  Lemma no_cycles_ready g : no_cycles (ready_edges g) (blocked_edges g).
  Proof.
    unfold no_cycles. apply Forall_forall. intros v Hv.
    apply in_map_iff in Hv. destruct Hv as [e [Heq Hin]].
    pose proof (in_ready _ _ Hin) as Hnt. rewrite Heq in Hnt.
    unfold not_in_snd. intros Hin2. apply (is_target_false _ _ Hnt).
    apply in_map_iff in Hin2. destruct Hin2 as [e2 [Heq2 Hin2]].
    apply in_map_iff. exists e2. split; [assumption|]. apply blocked_incl. assumption.
  Qed.

  Lemma incl_ready_blocked g : incl g (ready_edges g ++ blocked_edges g).
  Proof.
    unfold incl. intros e He. apply in_app_iff.
    destruct (is_target g (fst e)) eqn:E.
    - right. unfold blocked_edges. apply filter_In. split; assumption.
    - left. unfold ready_edges. apply filter_In. split; [assumption|]. rewrite E. reflexivity.
  Qed.

  Lemma acyclicb'_sound fuel : forall g, acyclicb' fuel g = true -> dag g.
  Proof.
    induction fuel as [|fuel IH]; intros g H.
    - destruct g; [apply dag_nil | discriminate].
    - destruct g as [|e g']; [apply dag_nil|].
      cbn [acyclicb'] in H.
      destruct (ready_edges (e :: g')) eqn:E; [discriminate|].
      apply IH in H.
      eapply dag_incl; [|apply incl_ready_blocked].
      apply dag_app; [apply no_cycles_ready | apply dag_ready | exact H].
  Qed.

  Theorem acyclicb_sound g : acyclicb g = true -> dag g.
  Proof. apply acyclicb'_sound. Qed.
End Acyclic.

(* A join is not a cycle, and a cycle behind a chain is still a cycle. *)
Example acyclicb_chain   : acyclicb [(0,1); (1,2); (2,3)]%nat = true.  Proof. reflexivity. Qed.
Example acyclicb_diamond : acyclicb [(0,1); (0,2); (1,3); (2,3)]%nat = true.  Proof. reflexivity. Qed.
Example acyclicb_two     : acyclicb [(0,1); (1,0)]%nat = false. Proof. reflexivity. Qed.
Example acyclicb_self    : acyclicb [(0,0)]%nat = false. Proof. reflexivity. Qed.
Example acyclicb_hidden  : acyclicb [(9,0); (0,1); (1,2); (2,3); (3,1)]%nat = false. Proof. reflexivity. Qed.
