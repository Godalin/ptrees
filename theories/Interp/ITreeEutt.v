(** Source weak bisimulation is preserved by the genuine datatype embedding.
    Finite silent prefixes are eliminated inductively; infinite silent
    behavior has the zero hitting witness, never a coinductive Tau guard. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Classical_Prop.
From Paco Require Import paco.
From ITree.Core Require Import ITreeDefinition.
From ITree.Eq Require Import Eqit.
From PTree.Core Require Import PTreeDefinition ITreeBridge.
From PTree.Prob.Interface Require Import Measure Omega Mixed RelationalClosure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting
  StableHittingRelation PTreeKernel PEutt.
Set Implicit Arguments.
Unset Strict Implicit.

Section Heads.
Context {E MN : Type -> Type}.

Fixpoint itree_head_at {A} (n : nat) (ot : itree' E A) :
    option (stable_head E MN A) :=
  match ot with
  | ITreeDefinition.RetF a => Some (FHRet a)
  | ITreeDefinition.TauF t =>
      match n with O => None | S m => itree_head_at m (ITreeDefinition.observe t) end
  | @ITreeDefinition.VisF _ _ _ X e k =>
      Some (FHVis e (fun x => from_itree (k x)))
  end.

Lemma itree_head_at_succ {A} n (ot : itree' E A) h :
  itree_head_at n ot = Some h -> itree_head_at (S n) ot = Some h.
Proof.
  revert ot. induction n; intros [a|t|X e k] H; cbn in *; auto; discriminate.
Qed.

Definition embedded_eutt {A B} (RR : A -> B -> Prop)
    (t : ptree E MN A) (u : ptree E MN B) : Prop :=
  exists s v, t = from_itree s /\ u = from_itree v /\ eutt RR s v.

Lemma eutt_head_at {A B} (RR : A -> B -> Prop) n
    (t : itree E A) (u : itree E B) h :
  eutt RR t u -> itree_head_at n (ITreeDefinition.observe t) = Some h ->
  exists m j, itree_head_at m (ITreeDefinition.observe u) = Some j /\
    stable_head_rel RR (embedded_eutt RR) h j.
Proof.
  revert t u h. induction n as [|n IH]; intros t u h Htu;
    punfold Htu; red in Htu; induction Htu; intro Hhead; cbn in Hhead.
  - inversion Hhead; subst. exists 0, (FHRet r2). split; [reflexivity|constructor; assumption].
  - discriminate.
  - inversion Hhead; subst. exists 0, (FHVis e (fun x => from_itree (k2 x))).
    split; [reflexivity|constructor]. intro x. exists (k1 x), (k2 x).
    split; [reflexivity|split; [reflexivity|]]. destruct (REL x) as [H|[]]. exact H.
  - discriminate.
  - destruct (IHHtu Hhead) as [m [j [Hj Hrel]]].
    exists (S m), j. split; assumption.
  - inversion Hhead; subst. exists 0, (FHRet r2). split; [reflexivity|constructor; assumption].
  - destruct REL as [Hrel|[]].
    destruct (IH _ _ _ Hrel Hhead) as [m [j [Hj Hr]]].
    exists (S m), j. split; assumption.
  - inversion Hhead; subst. exists 0, (FHVis e (fun x => from_itree (k2 x))).
    split; [reflexivity|constructor]. intro x. exists (k1 x), (k2 x).
    split; [reflexivity|split; [reflexivity|]]. destruct (REL x) as [H|[]]. exact H.
  - apply IHHtu. apply itree_head_at_succ. exact Hhead.
  - destruct (IHHtu Hhead) as [m [j [Hj Hrel]]].
    exists (S m), j. split; assumption.
Qed.
End Heads.

Section Hitting.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}.

Lemma from_itree_head_hitting {A} n (t : itree E A) h :
  itree_head_at n (ITreeDefinition.observe t) = Some h ->
  ptree_stable_hitting (MF := MF) (observe (@from_itree E MN A t)) (sem_ret h).
Proof.
  revert t h. induction n as [|n IH]; intros t h H;
    unfold ptree_stable_hitting; rewrite observe_from_itree;
    destruct (ITreeDefinition.observe t) as [a|u|X e k]; cbn in H;
    try discriminate; try (inversion H; subst; apply stable_hitting_ret);
    try (inversion H; subst; apply stable_hitting_vis).
  apply (proj2 (stable_hitting_tau_iff _ _)). exact (IH _ _ H).
Qed.

Lemma from_itree_no_head_approx {A} n (t : itree E A) :
  (forall m, @itree_head_at E MN A m (ITreeDefinition.observe t) = None) ->
  sem_eq (ptree_hitting_approx (MF := MF) n (observe (from_itree t))) sem_zero.
Proof.
  revert t. induction n as [|n IH]; intros t H;
    rewrite observe_from_itree;
    destruct (ITreeDefinition.observe t) as [a|u|X e k] eqn:Ht.
  - discriminate (H 0).
  - apply ptree_hitting_tau_zero.
  - discriminate (H 0).
  - discriminate (H 0).
  - eapply sem_eq_trans; [apply ptree_hitting_tau_succ|].
    apply IH. intro m. exact (H (S m)).
  - discriminate (H 0).
Qed.

Lemma from_itree_no_head_hitting {A} (t : itree E A) :
  (forall m, @itree_head_at E MN A m (ITreeDefinition.observe t) = None) ->
  ptree_stable_hitting (MF := MF) (observe (from_itree t)) sem_zero.
Proof.
  intro H. unfold ptree_stable_hitting, stable_hitting.
  eapply sem_lub_chain_proper with (chain := fun _ => sem_zero).
  - intro n. apply sem_eq_sym. exact (from_itree_no_head_approx n H).
  - apply sem_lub_constant.
Qed.

Definition embedded_eutt_state {A B} (RR : A -> B -> Prop)
    (s : ptree' E MN A) (v : ptree' E MN B) : Prop :=
  exists t u, s = observe (from_itree t) /\ v = observe (from_itree u) /\ eutt RR t u.

(** No native probability laws, relational-lub law, or termination premise
    are needed for the probability-free embedding. Classical case analysis
    separates finite head convergence from pure silent divergence. *)
Theorem from_itree_eutt {A B} (RR : A -> B -> Prop)
    (t : itree E A) (u : itree E B) (Hzero : relational_zero FO) :
  eutt RR t u -> peutt (MF := MF) RR (from_itree t) (from_itree u).
Proof.
  intro Htu. eapply peutt_coinduction with (sim := embedded_eutt_state RR).
  - intros s v [t' [u' [-> [-> H]]]].
    destruct (classic (exists n h, @itree_head_at E MN A n
      (ITreeDefinition.observe t') = Some h)) as [[n [h Hh]]|Hnone].
    + destruct (eutt_head_at H Hh) as [m [j [Hj Hrel]]].
      eapply stable_hitting_match_of_hitting_lift.
      * exact (from_itree_head_hitting Hh).
      * exact (from_itree_head_hitting Hj).
      * apply sem_lift_ret. eapply stable_head_rel_mono; [|exact Hrel].
        intros a b [x [y [-> [-> Hxy]]]].
        exists x, y. split; [reflexivity|split; [reflexivity|exact Hxy]].
    + assert (Ht : forall n, @itree_head_at E MN A n
        (ITreeDefinition.observe t') = None).
      { intro n. destruct (itree_head_at n (ITreeDefinition.observe t')) eqn:Hn;
          [exfalso; apply Hnone; eauto|reflexivity]. }
      assert (Hu : forall n, @itree_head_at E MN B n
        (ITreeDefinition.observe u') = None).
      { intro n. destruct (itree_head_at n (ITreeDefinition.observe u')) eqn:Hn;
          [|reflexivity]. exfalso.
        pose proof (eqit_flip _ _ _ _ _ H) as Hrev.
        destruct (eutt_head_at Hrev Hn) as [m [j [Hj _]]].
        rewrite Ht in Hj. discriminate. }
      eapply stable_hitting_match_of_hitting_lift.
      * exact (from_itree_no_head_hitting Ht).
      * exact (from_itree_no_head_hitting Hu).
      * apply Hzero.
  - exists t, u. split; [reflexivity|split; [reflexivity|exact Htu]].
Qed.
End Hitting.
