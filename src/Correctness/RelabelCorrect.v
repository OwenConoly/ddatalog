(* RelabelCorrect: an INJECTIVE relabeling of relation names preserves [Datalog.prog_impl] for the
   BARE fragment (every clause argument is a variable).

   This is the bridge that lets a top-level correctness theorem be stated over the ORIGINAL relation
   names [rel] (e.g. strings) instead of the numeric ids [rel'] (= nat) the compiler lowers to.

   The bare fragment is what makes this clean: [interp_expr] on a [var_expr] is just [map.get ctx]
   -- it never touches the [signature]'s [interp_fun] -- and relations are only ever compared by
   Leibniz equality.  So relabeling along an injective [rho : rel -> rel'] (and any [iota : fn -> fn']
   for type-totality; functions never appear in bare programs) preserves derivability. *)

From Datalog Require Import Datalog.
From Stdlib Require Import List.
From coqutil Require Import Map.Interface.
Import ListNotations.

(* A normal rule's [rule_impl] is just [simple_rule_impl] over a [non_meta_rule_impl] (the meta
   constructor needs a [meta_rule]).  Generic over the Datalog params, so it serves both the source
   and the relabeled instances. *)
Section NormalInv.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context `{qsig : query_signature rel}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool}
          {var_eqb_spec : forall x y : var, BoolSpec (x = y) (x <> y) (var_eqb x y)}.

  Lemma rule_impl_normal_inv (env : list (@Datalog.fact rel T) -> rel -> list T -> Prop)
      (cs hs : list (@Datalog.clause rel var fn)) (f : @Datalog.fact rel T)
      (hyps : list (@Datalog.fact rel T)) :
    rule_impl env (Datalog.normal_rule cs hs) f hyps ->
    exists R args, f = Datalog.normal_fact R args /\
      non_meta_rule_impl (Datalog.normal_rule cs hs) R args hyps.
  Proof.
    intros H. inversion H as [r0 R args hyps0 Hnm | ]; subst. exists R, args. split; [reflexivity | exact Hnm].
  Qed.
End NormalInv.

Section RelabelCorrect.
  Context {rel rel' var fn fn' aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context `{sig' : signature fn' aggregator T}.
  Context `{qsig : query_signature rel}.
  Context `{qsig' : query_signature rel'}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool}
          {var_eqb_spec : forall x y : var, BoolSpec (x = y) (x <> y) (var_eqb x y)}.
  Context (rho : rel -> rel') (iota : fn -> fn').
  (* [rho] need only be injective on the relations [S] that actually occur in the program/EDB --
     the compiler's relation map is injective only on the names it collected, not globally, and for
     an abstract [rel] there is no global injection into [nat] anyway. *)
  Context (S : rel -> Prop).
  Context (rho_inj : forall a b, S a -> S b -> rho a = rho b -> a = b).

  (* abbreviations for the two type instances *)
  Notation expr   := (@Datalog.expr var fn).
  Notation expr'  := (@Datalog.expr var fn').
  Notation clause := (@Datalog.clause rel var fn).
  Notation clause':= (@Datalog.clause rel' var fn').
  Notation mclause := (@Datalog.meta_clause rel var fn).
  Notation mclause':= (@Datalog.meta_clause rel' var fn').
  Notation fact   := (@Datalog.fact rel T).
  Notation fact'  := (@Datalog.fact rel' T).
  Notation rule   := (@Datalog.rule rel var fn aggregator).
  Notation rule'  := (@Datalog.rule rel' var fn' aggregator).

  (*----The relabeling (total functions)----*)

  Fixpoint relabel_expr (e : expr) : expr' :=
    match e with
    | Datalog.var_expr v => Datalog.var_expr v
    | Datalog.fun_expr f args => Datalog.fun_expr (iota f) (List.map relabel_expr args)
    end.

  Definition relabel_clause (c : clause) : clause' :=
    {| Datalog.clause_rel := rho c.(Datalog.clause_rel);
       Datalog.clause_args := List.map relabel_expr c.(Datalog.clause_args) |}.

  Definition relabel_mclause (c : mclause) : mclause' :=
    {| Datalog.meta_clause_rel := rho c.(Datalog.meta_clause_rel);
       Datalog.meta_clause_args := List.map (option_map relabel_expr) c.(Datalog.meta_clause_args) |}.

  Definition relabel_fact (f : fact) : fact' :=
    match f with
    | Datalog.normal_fact R args => Datalog.normal_fact (rho R) args
    | Datalog.meta_fact R margs Sset => Datalog.meta_fact (rho R) margs Sset
    end.

  Definition relabel_rule (r : rule) : rule' :=
    match r with
    | Datalog.normal_rule cs hs =>
        Datalog.normal_rule (List.map relabel_clause cs) (List.map relabel_clause hs)
    | Datalog.meta_rule cs hs =>
        Datalog.meta_rule (List.map relabel_mclause cs) (List.map relabel_mclause hs)
    | Datalog.agg_rule cr agg hr => Datalog.agg_rule (rho cr) agg (rho hr)
    end.

  Definition relabel_program (p : list rule) : list rule' := List.map relabel_rule p.

  (* the EDB [Q] over original facts, viewed over relabeled facts (its forward image) *)
  Definition relabel_Q (Q : fact -> Prop) : fact' -> Prop :=
    fun f' => exists f, Q f /\ relabel_fact f = f'.

  (*----The bare fragment----*)

  Definition bare_expr (e : expr) : Prop := exists v, e = Datalog.var_expr v.
  Definition bare_clause (c : clause) : Prop := Forall bare_expr c.(Datalog.clause_args).
  Definition bare_rule (r : rule) : Prop :=
    match r with
    | Datalog.normal_rule cs hs => Forall bare_clause cs /\ Forall bare_clause hs
    | _ => False
    end.
  Definition bare_program (p : list rule) : Prop := Forall bare_rule p.

  (*----Well-scopedness: the relations occurring in a clause/rule/program are all in [S]----*)

  Definition Sclause (c : clause) : Prop := S c.(Datalog.clause_rel).
  Definition Srule (r : rule) : Prop :=
    match r with
    | Datalog.normal_rule cs hs => Forall Sclause cs /\ Forall Sclause hs
    | _ => True
    end.
  Definition Sprogram (p : list rule) : Prop := Forall Srule p.

  (* a fact's relation is the relation of any clause that interprets to it *)
  Lemma interp_clause_rel (ctx : context) (c : clause) (f : fact) :
    interp_clause ctx c f -> Datalog.rel_of f = c.(Datalog.clause_rel).
  Proof. intros [args [_ Hf]]. subst f. reflexivity. Qed.

  Lemma interp_clauses_Srel (ctx : context) (cs : list clause) (fs : list fact) :
    Forall Sclause cs -> Forall2 (interp_clause ctx) cs fs ->
    Forall (fun h => S (Datalog.rel_of h)) fs.
  Proof.
    intros HS H. induction H as [| c f cs fs Hc Hrest IH]; [constructor|].
    inversion HS as [| c0 cs0 Hsc Hscs]; subst. constructor.
    - rewrite (interp_clause_rel ctx c f Hc). exact Hsc.
    - apply IH. exact Hscs.
  Qed.

  (*----[relabel_fact] is injective on facts whose relation is in [S]----*)

  Lemma relabel_fact_inj (f1 f2 : fact) :
    S (Datalog.rel_of f1) -> S (Datalog.rel_of f2) ->
    relabel_fact f1 = relabel_fact f2 -> f1 = f2.
  Proof.
    destruct f1 as [R1 a1 | R1 m1 S1]; destruct f2 as [R2 a2 | R2 m2 S2]; cbn; try discriminate.
    - intros HS1 HS2 H. injection H as HR Ha. apply (rho_inj _ _ HS1 HS2) in HR. subst. reflexivity.
    - intros HS1 HS2 H. injection H as HR Hm HS. apply (rho_inj _ _ HS1 HS2) in HR. subst. reflexivity.
  Qed.

  (*----[interp_expr] on a bare (variable) argument is signature-free, hence commutes----*)

  Lemma interp_var_iff (ctx : context) (v : var) (val : T) :
    interp_expr ctx (Datalog.var_expr v : expr) val <-> map.get ctx v = Some val.
  Proof.
    split.
    - intros H. inversion H; subst; assumption.
    - intros H. apply Datalog.interp_var_expr. exact H.
  Qed.

  Lemma interp_var_iff' (ctx : context) (v : var) (val : T) :
    interp_expr ctx (Datalog.var_expr v : expr') val <-> map.get ctx v = Some val.
  Proof.
    split.
    - intros H. inversion H; subst; assumption.
    - intros H. apply Datalog.interp_var_expr. exact H.
  Qed.

  (*----[interp] commutes with relabeling on the bare fragment----*)

  Lemma interp_args_relabel (ctx : context) (args : list expr) (vals : list T) :
    Forall bare_expr args ->
    Forall2 (interp_expr ctx) args vals ->
    Forall2 (interp_expr ctx) (List.map relabel_expr args) vals.
  Proof.
    intros Hbare H. revert Hbare. induction H as [| e v l1 l2 He Hl IH]; intros Hbare; cbn; [constructor|].
    inversion Hbare as [| e0 l0 Hbe Hbl]; subst.
    destruct Hbe as [w Hw]; subst e. cbn. constructor.
    - apply interp_var_iff'. apply interp_var_iff in He. exact He.
    - apply IH. exact Hbl.
  Qed.

  Lemma interp_args_unrelabel (ctx : context) (args : list expr) :
    forall vals,
    Forall bare_expr args ->
    Forall2 (interp_expr ctx) (List.map relabel_expr args) vals ->
    Forall2 (interp_expr ctx) args vals.
  Proof.
    induction args as [| e args IH]; intros vals Hbare H; cbn in H.
    - inversion H; subst. constructor.
    - inversion Hbare as [| e0 l0 Hbe Hbl]; subst.
      destruct Hbe as [w Hw]; subst e. cbn in H.
      inversion H as [| x v xs l2 He Hl]; subst. constructor.
      + apply interp_var_iff. apply interp_var_iff' in He. exact He.
      + apply IH; [exact Hbl | exact Hl].
  Qed.

  Lemma interp_clause_relabel (ctx : context) (c : clause) (f : fact) :
    bare_clause c ->
    interp_clause ctx c f ->
    interp_clause ctx (relabel_clause c) (relabel_fact f).
  Proof.
    intros Hbare [args [Hargs Hf]]. subst f. exists args. split.
    - apply interp_args_relabel; [exact Hbare | exact Hargs].
    - cbn. reflexivity.
  Qed.

  Lemma interp_clause_unrelabel (ctx : context) (c : clause) (f' : fact') :
    bare_clause c ->
    interp_clause ctx (relabel_clause c) f' ->
    exists f, relabel_fact f = f' /\ interp_clause ctx c f.
  Proof.
    intros Hbare [args' [Hargs' Hf']]. cbn in Hf'.
    exists (Datalog.normal_fact c.(Datalog.clause_rel) args'). split.
    - cbn. rewrite Hf'. reflexivity.
    - exists args'. split; [apply interp_args_unrelabel; [exact Hbare | exact Hargs'] | reflexivity].
  Qed.

  (* the hypothesis clause list commutes (forward and backward) *)
  Lemma interp_clauses_relabel (ctx : context) (cs : list clause) (fs : list fact) :
    Forall bare_clause cs ->
    Forall2 (interp_clause ctx) cs fs ->
    Forall2 (interp_clause ctx) (List.map relabel_clause cs) (List.map relabel_fact fs).
  Proof.
    intros Hbare H. revert Hbare. induction H as [| c f cs fs Hc Hrest IH]; intros Hbare; cbn; [constructor|].
    inversion Hbare as [| c0 cs0 Hbc Hbcs]; subst. constructor.
    - apply interp_clause_relabel; [exact Hbc | exact Hc].
    - apply IH. exact Hbcs.
  Qed.

  Lemma interp_clauses_unrelabel (ctx : context) (cs : list clause) :
    forall fs',
    Forall bare_clause cs ->
    Forall2 (interp_clause ctx) (List.map relabel_clause cs) fs' ->
    exists fs, fs' = List.map relabel_fact fs /\ Forall2 (interp_clause ctx) cs fs.
  Proof.
    induction cs as [| c cs IH]; intros fs' Hbare H; cbn in H.
    - inversion H; subst. exists []. split; [reflexivity | constructor].
    - inversion Hbare as [| c0 cs0 Hbc Hbcs]; subst.
      inversion H as [| x f0 xs fs0 Hc Hrest]; subst.
      destruct (interp_clause_unrelabel ctx c f0 Hbc Hc) as [f [Hf Hcf]].
      destruct (IH fs0 Hbcs Hrest) as [fs [Hfs Hcsfs]].
      exists (f :: fs). split.
      + cbn. rewrite Hf, Hfs. reflexivity.
      + constructor; [exact Hcf | exact Hcsfs].
  Qed.

  (* the conclusion clause [Exists] commutes (forward and backward) *)
  Lemma exists_concl_relabel (ctx : context) (cs : list clause) (R : rel) (args : list T) :
    Forall bare_clause cs ->
    Exists (fun c => interp_clause ctx c (Datalog.normal_fact R args)) cs ->
    Exists (fun c => interp_clause ctx c (Datalog.normal_fact (rho R) args)) (List.map relabel_clause cs).
  Proof.
    intros Hbare H. induction H as [c cs Hc | c cs Hrest IH].
    - inversion Hbare as [| c0 cs0 Hbc Hbcs]; subst. apply Exists_cons_hd.
      pose proof (interp_clause_relabel ctx c (Datalog.normal_fact R args) Hbc Hc) as Hr. cbn in Hr. exact Hr.
    - inversion Hbare as [| c0 cs0 Hbc Hbcs]; subst. apply Exists_cons_tl. apply IH. exact Hbcs.
  Qed.

  Lemma exists_concl_unrelabel (ctx : context) (cs : list clause) (R' : rel') (args' : list T) :
    Forall bare_clause cs ->
    Exists (fun c => interp_clause ctx c (Datalog.normal_fact R' args')) (List.map relabel_clause cs) ->
    exists R, R' = rho R /\ Exists (fun c => interp_clause ctx c (Datalog.normal_fact R args')) cs.
  Proof.
    intros Hbare. induction cs as [| c cs IH]; intros H; cbn in H.
    - inversion H.
    - inversion Hbare as [| c0 cs0 Hbc Hbcs]; subst.
      inversion H as [c' rest Hc | c' rest Hrest]; subst.
      + destruct (interp_clause_unrelabel ctx c (Datalog.normal_fact R' args') Hbc Hc) as [f [Hf Hcf]].
        destruct f as [R0 fa | R0 mm ss]; cbn in Hf; [| discriminate].
        injection Hf as HR Hfa. subst fa. exists R0.
        split; [exact (eq_sym HR) | apply Exists_cons_hd; exact Hcf].
      + destruct (IH Hbcs Hrest) as [R0 [HR HE]].
        exists R0. split; [exact HR | apply Exists_cons_tl; exact HE].
  Qed.

  (*----[non_meta_rule_impl] (one bare normal rule firing) commutes----*)

  Lemma non_meta_relabel (r : rule) (R : rel) (args : list T) (hyps : list fact) :
    bare_rule r ->
    non_meta_rule_impl r R args hyps ->
    non_meta_rule_impl (relabel_rule r) (rho R) args (List.map relabel_fact hyps).
  Proof.
    intros Hbare H. destruct r as [cs hs | mcs mhs | cr agg hr]; cbn [bare_rule] in Hbare;
      [| contradiction | contradiction].
    destruct Hbare as [Hbcs Hbhs].
    inversion H as [cs0 hs0 ctx0 R0 a0 h0 Hex Hall | ]; subst.
    cbn [relabel_rule]. apply (Datalog.normal_rule_impl _ _ ctx0).
    - apply exists_concl_relabel; [exact Hbcs | exact Hex].
    - apply interp_clauses_relabel; [exact Hbhs | exact Hall].
  Qed.

  Lemma non_meta_unrelabel (r : rule) (R' : rel') (args' : list T) (hyps' : list fact') :
    bare_rule r -> Srule r ->
    non_meta_rule_impl (relabel_rule r) R' args' hyps' ->
    exists R hyps, R' = rho R /\ hyps' = List.map relabel_fact hyps /\
      S R /\ Forall (fun h => S (Datalog.rel_of h)) hyps /\
      non_meta_rule_impl r R args' hyps.
  Proof.
    intros Hbare HSr H. destruct r as [cs hs | mcs mhs | cr agg hr]; cbn [bare_rule] in Hbare;
      cbn [Srule] in HSr; cbn [relabel_rule] in H; [| contradiction | contradiction].
    destruct Hbare as [Hbcs Hbhs]. destruct HSr as [HScs HShs].
    inversion H as [cs0 hs0 ctx0 R0 a0 h0 Hex Hall | ]; subst.
    destruct (exists_concl_unrelabel ctx0 cs R' args' Hbcs Hex) as [R [HR Hex0]].
    destruct (interp_clauses_unrelabel ctx0 hs hyps' Hbhs Hall) as [hyps [Hhyps Hall0]].
    assert (HSR : S R).
    { pose proof Hex0 as Hex0'. apply Exists_exists in Hex0'. destruct Hex0' as [c [Hcin Hc]].
      pose proof (interp_clause_rel ctx0 c (Datalog.normal_fact R args') Hc) as Hrel. cbn in Hrel.
      rewrite Hrel. exact (proj1 (Forall_forall Sclause cs) HScs c Hcin). }
    exists R, hyps.
    split; [exact HR | split; [exact Hhyps | split; [exact HSR | split]]].
    - exact (interp_clauses_Srel ctx0 hs hyps HShs Hall0).
    - apply (Datalog.normal_rule_impl _ _ ctx0); [exact Hex0 | exact Hall0].
  Qed.

  (*----The [prog_impl] bridge (pftree closure), forward and backward----*)

  Lemma relabel_prog_fwd (p : list rule) (Q : fact -> Prop) :
    bare_program p ->
    forall f, Datalog.prog_impl p Q f ->
    Datalog.prog_impl (relabel_program p) (relabel_Q Q) (relabel_fact f).
  Proof.
    intros Hbp.
    apply (Datalog.prog_impl_ind p Q
             (fun f => Datalog.prog_impl (relabel_program p) (relabel_Q Q) (relabel_fact f))).
    - intros f HQ. apply Datalog.pftree_leaf. exists f. split; [exact HQ | reflexivity].
    - intros f hyps Hex _ IH.
      apply Exists_exists in Hex. destruct Hex as [r [Hrin Hri]].
      pose proof (proj1 (Forall_forall bare_rule p) Hbp r Hrin) as Hbr.
      destruct r as [cs hs | mcs mhs | cr agg hr]; cbn [bare_rule] in Hbr; [| contradiction | contradiction].
      destruct (rule_impl_normal_inv (one_step_derives p) cs hs f hyps Hri) as [R [args [Hf Hnm]]].
      subst f.
      apply (Datalog.prog_impl_step (relabel_program p) (relabel_Q Q)
               (relabel_fact (Datalog.normal_fact R args)) (List.map relabel_fact hyps)).
      + apply Exists_exists. exists (relabel_rule (Datalog.normal_rule cs hs)). split.
        * apply in_map. exact Hrin.
        * cbn [relabel_fact]. apply Datalog.simple_rule_impl.
          apply (non_meta_relabel (Datalog.normal_rule cs hs) R args hyps Hbr Hnm).
      + rewrite Forall_forall in IH |- *. intros f' Hf'. apply in_map_iff in Hf'.
        destruct Hf' as [h [Heq Hh]]. subst f'. exact (IH h Hh).
  Qed.

  Lemma relabel_prog_bwd (p : list rule) (Q : fact -> Prop) :
    bare_program p -> Sprogram p -> (forall g, Q g -> S (Datalog.rel_of g)) ->
    forall f', Datalog.prog_impl (relabel_program p) (relabel_Q Q) f' ->
    exists f, relabel_fact f = f' /\ S (Datalog.rel_of f) /\ Datalog.prog_impl p Q f.
  Proof.
    intros Hbp HSp HSQ.
    apply (Datalog.prog_impl_ind (relabel_program p) (relabel_Q Q)
             (fun f' => exists f, relabel_fact f = f' /\ S (Datalog.rel_of f) /\ Datalog.prog_impl p Q f)).
    - intros f' [g [HQ Hg]]. exists g. split; [exact Hg | split; [exact (HSQ g HQ) | apply Datalog.pftree_leaf; exact HQ]].
    - intros f' hyps' Hex _ IH.
      apply Exists_exists in Hex. destruct Hex as [r' [Hr'in Hri]].
      apply in_map_iff in Hr'in. destruct Hr'in as [r [Hr'eq Hrin]]. subst r'.
      pose proof (proj1 (Forall_forall bare_rule p) Hbp r Hrin) as Hbr.
      pose proof (proj1 (Forall_forall Srule p) HSp r Hrin) as HSr.
      destruct r as [cs hs | mcs mhs | cr agg hr]; cbn [bare_rule] in Hbr; [| contradiction | contradiction].
      cbn [relabel_rule] in Hri.
      destruct (rule_impl_normal_inv (one_step_derives (relabel_program p))
                  (List.map relabel_clause cs) (List.map relabel_clause hs) f' hyps' Hri)
        as [R' [args' [Hf' Hnm']]].
      destruct (non_meta_unrelabel (Datalog.normal_rule cs hs) R' args' hyps' Hbr HSr Hnm')
        as [R [hyps [HR [Hhyps [HSR [HShyps Hnm]]]]]].
      exists (Datalog.normal_fact R args'). split; [| split].
      + cbn [relabel_fact]. rewrite <- HR. exact (eq_sym Hf').
      + cbn [Datalog.rel_of]. exact HSR.
      + apply (Datalog.prog_impl_step p Q (Datalog.normal_fact R args') hyps).
        * apply Exists_exists. exists (Datalog.normal_rule cs hs). split; [exact Hrin|].
          apply Datalog.simple_rule_impl. exact Hnm.
        * subst hyps'. rewrite Forall_forall in IH, HShyps |- *. intros h Hh.
          specialize (IH (relabel_fact h) (in_map relabel_fact hyps h Hh)).
          destruct IH as [g [Hg [HSg Hpg]]]. apply (relabel_fact_inj g h HSg (HShyps h Hh)) in Hg.
          subst g. exact Hpg.
  Qed.

  (* THE BRIDGE: a relabel of relations -- injective on the relations [S] that occur -- preserves
     derivability of a bare, well-scoped program over its EDB.  [f] is over the ORIGINAL relations;
     [relabel_fact f] is what the lowered network derives. *)
  Theorem prog_impl_relabel (p : list rule) (Q : fact -> Prop) (f : fact) :
    bare_program p -> Sprogram p ->
    (forall g, Q g -> S (Datalog.rel_of g)) -> S (Datalog.rel_of f) ->
    (Datalog.prog_impl (relabel_program p) (relabel_Q Q) (relabel_fact f) <-> Datalog.prog_impl p Q f).
  Proof.
    intros Hbp HSp HSQ HSf. split.
    - intros H. destruct (relabel_prog_bwd p Q Hbp HSp HSQ (relabel_fact f) H) as [g [Hg [HSg Hpg]]].
      apply (relabel_fact_inj g f HSg HSf) in Hg. subst g. exact Hpg.
    - intros H. exact (relabel_prog_fwd p Q Hbp f H).
  Qed.

End RelabelCorrect.
