(** Probability-free conservativity on the image of [from_itree].
    Reflection needs separation of Dirac observations from each other and
    from zero. These are existing probability laws, not an ITree axiom. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Classical_Prop Program.Equality.
From Paco Require Import paco.
From ITree.Core Require Import ITreeDefinition.
From ITree.Eq Require Import Eqit.
From PTree.Core Require Import PTreeDefinition ITreeBridge.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed RelationalClosure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting
  StableHittingRelation PTreeKernel PEutt.
From PTree.Interp Require Import ITreeEutt.
Set Implicit Arguments.
Unset Strict Implicit.

Section SourceHeads.
Context {E MN : Type → Type} {A B : Type}.
Variable RR : A → B → Prop.

(** Finite Tau prefixes are discharged inductively, not used as a
    coinductive guard. Only the matched visible continuations use [sim].
    The current dependent head inversion uses UIP; reflection and its iff
    inherit it. This is separate from the excluded middle used below to
    distinguish finite-head existence from silent divergence, and from
    [from_itree_eutt] preservation, which does not depend on UIP. *)
Lemma itree_head_at_eqitF
    (rel : ptree E MN A → ptree E MN B → Prop)
    (sim : itree E A → itree E B → Prop)
    (Hsim : ∀ t u, rel (from_itree t) (from_itree u) → sim t u)
    n m (t : itree E A) (u : itree E B) h j :
  itree_head_at n (ITreeDefinition.observe t) = Some h →
  itree_head_at m (ITreeDefinition.observe u) = Some j →
  stable_head_rel RR rel h j →
  eqitF RR true true id sim (ITreeDefinition.observe t) (ITreeDefinition.observe u).
Proof.
  revert t u h j m. induction n as [|n IH]; intros t u h j m Ht Hu Hrel;
    destruct (ITreeDefinition.observe t) as [a|t'|X e k] eqn:Et;
    cbn in Ht; try discriminate.
  all: try (eapply EqTauL; [reflexivity|]; eapply IH; eassumption).
  all: inversion Ht; subst h; clear Ht;
    revert u j Hu Hrel; induction m as [|m IHm]; intros u j Hu Hrel;
    destruct (ITreeDefinition.observe u) as [b|u'|Y f l] eqn:Eu;
    cbn in Hu; try discriminate.
  all: try (eapply EqTauR; [reflexivity|]; eapply IHm; eassumption).
  all: inversion Hu; subst j; clear Hu; dependent destruction Hrel.
  all: constructor; auto.
  all: intro v; apply Hsim, H.
Qed.

Lemma itree_no_head_eutt (t : itree E A) (u : itree E B) :
  (∀ n, @itree_head_at E MN A n (ITreeDefinition.observe t) = None) →
  (∀ n, @itree_head_at E MN B n (ITreeDefinition.observe u) = None) →
  eutt RR t u.
Proof.
  revert t u. pcofix CIH. intros t u Ht Hu. pfold. red.
  destruct (ITreeDefinition.observe t) as [a|t'|X e k] eqn:Et;
    try discriminate (Ht 0).
  destruct (ITreeDefinition.observe u) as [b|u'|Y f l] eqn:Eu;
    try discriminate (Hu 0).
  apply EqTau. right. apply CIH.
  - intro n. exact (Ht (S n)).
  - intro n. exact (Hu (S n)).
Qed.
End SourceHeads.

Section Reflection.
Context {E MN MF : Type → Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{CA : @SemanticMeasureCouplingAELaws MF FI}
  `{DA : @SemanticMeasureDiracAELaws MF FI}
  `{OA : @SemanticOmegaAELaws MF FI FO}.

Lemma from_itree_peutt_head {A B} (RR : A → B → Prop)
    (t : itree E A) (u : itree E B) n h :
  peutt (MF := MF) RR (from_itree t) (from_itree u) →
  itree_head_at n (ITreeDefinition.observe t) = Some h →
  ∃ m j, itree_head_at m (ITreeDefinition.observe u) = Some j ∧
    stable_head_rel RR (peutt (MF := MF) RR) h j.
Proof.
  intros Htu Hh.
  destruct (classic (exists m j, @itree_head_at E MN B m
    (ITreeDefinition.observe u) = Some j)) as [[m [j Hj]]|Hnone].
  - exists m, j. split; [exact Hj|].
    exact (sem_lift_ret_inv (peutt_hitting_lift Htu
      (from_itree_head_hitting Hh) (from_itree_head_hitting Hj))).
  - assert (Hu : ∀ m, @itree_head_at E MN B m
        (ITreeDefinition.observe u) = None).
    { intro m. destruct (itree_head_at m (ITreeDefinition.observe u)) eqn:Hm;
        [exfalso; apply Hnone; eauto|reflexivity]. }
    pose proof (peutt_hitting_lift Htu (from_itree_head_hitting Hh)
      (from_itree_no_head_hitting Hu)) as Hlift.
    pose proof (sem_lift_ae_transport_r (sem_lift_sym Hlift)
      (sem_ae_zero (λ _ : stable_head E MN B, False))) as Hfalse.
    apply (proj1 (sem_ae_ret_iff _ _)) in Hfalse.
    destruct Hfalse as [j [_ Hfalse]]. contradiction.
Qed.

Theorem from_itree_eutt_reflect {A B} (RR : A → B → Prop)
    (t : itree E A) (u : itree E B) :
  peutt (MF := MF) RR (from_itree t) (from_itree u) → eutt RR t u.
Proof.
  revert t u. pcofix CIH. intros t u Htu.
  destruct (classic (exists n h, @itree_head_at E MN A n
    (ITreeDefinition.observe t) = Some h)) as [[n [h Hh]]|Hnone].
  - destruct (from_itree_peutt_head Htu Hh) as [m [j [Hj Hrel]]].
    pfold. red. eapply itree_head_at_eqitF; [|exact Hh|exact Hj|exact Hrel].
    intros s v Hsv. right. apply CIH. exact Hsv.
  - assert (Ht : ∀ n, @itree_head_at E MN A n
        (ITreeDefinition.observe t) = None).
    { intro n. destruct (itree_head_at n (ITreeDefinition.observe t)) eqn:Hn;
        [exfalso; apply Hnone; eauto|reflexivity]. }
    assert (Hu : ∀ n, @itree_head_at E MN B n
        (ITreeDefinition.observe u) = None).
    { intro n. destruct (itree_head_at n (ITreeDefinition.observe u)) eqn:Hn;
        [|reflexivity].
      pose proof (peutt_hitting_lift Htu (from_itree_no_head_hitting Ht)
        (from_itree_head_hitting Hn)) as Hlift.
      pose proof (sem_lift_ae_transport_r Hlift
        (sem_ae_zero (λ _ : stable_head E MN A, False))) as Hfalse.
      apply (proj1 (sem_ae_ret_iff _ _)) in Hfalse.
      destruct Hfalse as [j [_ Hfalse]]. contradiction. }
    eapply paco2_mon; [exact (itree_no_head_eutt RR Ht Hu)|]. intros x y [].
Qed.

Theorem from_itree_eutt_iff {A B} (RR : A → B → Prop)
    (t : itree E A) (u : itree E B) (Hzero : relational_zero FO) :
  eutt RR t u ↔ peutt (MF := MF) RR (from_itree t) (from_itree u).
Proof. split; [apply (from_itree_eutt Hzero)|apply from_itree_eutt_reflect]. Qed.
End Reflection.
