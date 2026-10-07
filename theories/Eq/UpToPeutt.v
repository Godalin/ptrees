(** Coinduction up to known behavioral rewriting on both endpoints.

    The candidate may be heterogeneous; its left and right rewrites use
    homogeneous peutt eq. No property of the return relation is required.
    This is not up-to-transitivity of the unknown candidate. *)
From Coq Require Import Utf8 Morphisms Program.Equality.
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel
  StableHittingRelation PEutt.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Rewriting.
Context {E MN MF : Type → Type}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.

Local Notation W A B RR := (@peutt_state E MN MF FI FC MX FO A B RR).
Local Notation matches RR sim := (stable_hitting_match
  (@ptree_primitive_kernel E MN MF FI MX _)
  (@ptree_primitive_kernel E MN MF FI MX _)
  (ptree_stable_head_rel RR) sim).

Definition peutt_upto_closure {A B}
    (sim : ptree' E MN A → ptree' E MN B → Prop) s1 s2 : Prop :=
  ∃ s1' s2', W A A eq s1 s1' ∧ sim s1' s2' ∧ W B B eq s2' s2.

Lemma peutt_upto_closure_includes {A B} sim (s1 : ptree' E MN A) (s2 : ptree' E MN B) :
  sim s1 s2 → peutt_upto_closure sim s1 s2.
Proof.
  intro H. exists s1, s2. split; [apply peutt_state_refl|].
  split; [exact H|apply peutt_state_refl].
Qed.

Lemma peutt_upto_closure_mono {A B}
    (sim sim' : ptree' E MN A → ptree' E MN B → Prop) :
  (∀ s1 s2, sim s1 s2 → sim' s1 s2) →
  ∀ s1 s2, peutt_upto_closure sim s1 s2 → peutt_upto_closure sim' s1 s2.
Proof.
  intros Hsub s1 s2 [x [y [Hl [H Hr]]]].
  exists x, y. split; [exact Hl|]. split; [apply Hsub; exact H|exact Hr].
Qed.

Lemma peutt_upto_closure_idempotent {A B} sim (s1 : ptree' E MN A) (s2 : ptree' E MN B) :
  peutt_upto_closure (peutt_upto_closure sim) s1 s2 ↔
  peutt_upto_closure sim s1 s2.
Proof.
  split.
  - intros [x [y [Hl [[x' [y' [Hl' [H Hr']]]] Hr]]]].
    exists x', y'. split.
    + exact (peutt_trans (x := go s1) (y := go x) (z := go x') Hl Hl').
    + split; [exact H|].
      exact (peutt_trans (x := go y') (y := go y) (z := go s2) Hr' Hr).
  - apply peutt_upto_closure_includes.
Qed.

(** Saturation, not the arbitrary candidate, respects endpoint rewriting. *)
#[global] Instance peutt_upto_closure_Proper {A B} sim :
  Proper (W A A eq ==> W B B eq ==> iff) (peutt_upto_closure sim).
Proof.
  intros s s' Hs t t' Ht. split; intro H.
  - apply (proj1 (peutt_upto_closure_idempotent _ _ _)).
    exists s, t. split.
    + exact (peutt_sym (x := go s) (y := go s') Hs).
    + split; assumption.
  - apply (proj1 (peutt_upto_closure_idempotent _ _ _)).
    exists s', t'. split; [exact Hs|]. split; [exact H|].
    exact (peutt_sym (x := go t) (y := go t') Ht).
Qed.

(** Expose the definitional state/tree bridge to setoid rewriting. *)
#[global] Instance observe_peutt_Proper {A} :
  Proper (@peutt E MN MF FI FC MX FO A A eq ==> W A A eq) (@observe E MN A).
Proof. intros t u H. exact H. Qed.

Local Lemma match_rel_compose {A B C}
    (R12 : A → B → Prop) (R23 : B → C → Prop) (R13 : A → C → Prop)
    sim12 sim23 sim13
    (Hret : ∀ a b c, R12 a b → R23 b c → R13 a c)
    (Hsim : ∀ a b c, sim12 a b → sim23 b c → sim13 a c) s1 s2 s3 :
  matches R12 sim12 s1 s2 → matches R23 sim23 s2 s3 → matches R13 sim13 s1 s3.
Proof.
  eapply stable_hitting_match_compose.
  intros a b c Hab Hbc. dependent destruction Hab; dependent destruction Hbc.
  - constructor. eapply Hret; eassumption.
  - constructor. intro x. eapply Hsim; eauto.
Qed.

(** Strong compatibility: C(F X) is included in F(C X). The outer
    equivalences are unfolded, not applied to an unproved recursive pair. *)
Lemma peutt_upto_closure_compatible {A B} (RR : A → B → Prop) sim s1 s2 :
  peutt_upto_closure (matches RR sim) s1 s2 →
  matches RR (peutt_upto_closure sim) s1 s2.
Proof.
  intros [x [y [Hl [Hmid Hr]]]].
  apply stable_hitting_bisim_unfold in Hl.
  apply stable_hitting_bisim_unfold in Hr.
  eapply match_rel_compose with (R12 := eq) (R23 := RR)
    (sim12 := W A A eq)
    (sim23 := λ b c, ∃ d, sim b d ∧ W B B eq d c).
  - intros a b c -> H. exact H.
  - intros a b c Hab [d [Hbd Hdc]].
    exists b, d. split; [exact Hab|]. split; [exact Hbd|exact Hdc].
  - exact Hl.
  - eapply match_rel_compose with (R12 := RR) (R23 := eq)
      (sim12 := sim) (sim23 := W B B eq).
    + intros a b c H ->. exact H.
    + intros a b c Hab Hbc. exists b. split; assumption.
    + exact Hmid.
    + exact Hr.
Qed.

Theorem peutt_coinduction_upto_peutt {A B} (RR : A → B → Prop) sim
    (Hprogress : ∀ s1 s2, sim s1 s2 → matches RR (peutt_upto_closure sim) s1 s2) :
  ∀ t u, sim (observe t) (observe u) → peutt (MF := MF) RR t u.
Proof.
  eapply peutt_coinduction_upto_closure with (clo := peutt_upto_closure).
  - exact (@peutt_upto_closure_includes A B).
  - intros rel Hrel s1 s2 H.
    eapply stable_hitting_match_mono.
    + apply ptree_stable_head_rel_mono.
    + intros a b Hab. apply (proj1 (peutt_upto_closure_idempotent _ _ _)), Hab.
    + apply peutt_upto_closure_compatible.
      eapply peutt_upto_closure_mono; [exact Hrel|exact H].
  - exact Hprogress.
Qed.

(** The practical variant also closes already proved heterogeneous pairs.
    Pure rewriting alone does not do this: C(empty) is still empty. *)
Definition peutt_upto_known_closure {A B} (RR : A → B → Prop) sim s1 s2 : Prop :=
  peutt_upto_closure sim s1 s2 ∨ W A B RR s1 s2.

Lemma peutt_upto_known_closure_includes {A B} (RR : A → B → Prop) sim s1 s2 :
  sim s1 s2 → peutt_upto_known_closure RR sim s1 s2.
Proof. intro H. left. apply peutt_upto_closure_includes, H. Qed.

Lemma peutt_upto_known_closure_known {A B} (RR : A → B → Prop) sim s1 s2 :
  W A B RR s1 s2 → peutt_upto_known_closure RR sim s1 s2.
Proof. intro H. right. exact H. Qed.

Lemma peutt_upto_known_closure_absorb {A B} (RR : A → B → Prop) sim s1 s2 :
  peutt_upto_closure (peutt_upto_known_closure RR sim) s1 s2 →
  peutt_upto_known_closure RR sim s1 s2.
Proof.
  intros [x [y [Hl [[Hmid|Hmid] Hr]]]].
  - left. apply (proj1 (peutt_upto_closure_idempotent _ _ _)).
    exists x, y. split; [exact Hl|]. split; assumption.
  - right. change (peutt (MF := MF) RR (go s1) (go s2)).
    eapply peutt_rel_compose with (R12 := eq) (R23 := RR) (u := go x).
    + intros a b c -> H. exact H.
    + exact Hl.
    + eapply peutt_rel_compose with (R12 := RR) (R23 := eq) (u := go y).
      * intros a b c H ->. exact H.
      * exact Hmid.
      * exact Hr.
Qed.

#[global] Instance peutt_upto_known_closure_Proper {A B} (RR : A → B → Prop) sim :
  Proper (W A A eq ==> W B B eq ==> iff) (peutt_upto_known_closure RR sim).
Proof.
  intros s s' Hs t t' Ht. split; intro H.
  - apply peutt_upto_known_closure_absorb. exists s, t. split.
    + exact (peutt_sym (x := go s) (y := go s') Hs).
    + split; assumption.
  - apply peutt_upto_known_closure_absorb. exists s', t'. split; [exact Hs|].
    split; [exact H|exact (peutt_sym (x := go t) (y := go t') Ht)].
Qed.

Theorem peutt_coinduction_upto_peutt_known {A B} (RR : A → B → Prop) sim
    (Hprogress : ∀ s1 s2, sim s1 s2 → matches RR (peutt_upto_known_closure RR sim) s1 s2) :
  ∀ t u, sim (observe t) (observe u) → peutt (MF := MF) RR t u.
Proof.
  eapply peutt_coinduction_upto_closure with (clo := peutt_upto_known_closure RR).
  - exact (peutt_upto_known_closure_includes RR).
  - intros rel Hrel s1 s2 [H|H].
    + eapply stable_hitting_match_mono.
      * apply ptree_stable_head_rel_mono.
      * intros a b Hab. apply peutt_upto_known_closure_absorb, Hab.
      * apply peutt_upto_closure_compatible.
        eapply peutt_upto_closure_mono; [exact Hrel|exact H].
    + apply stable_hitting_bisim_unfold in H.
      eapply stable_hitting_match_mono; [apply ptree_stable_head_rel_mono| |exact H].
      intros a b Hab. apply peutt_upto_known_closure_known, Hab.
  - exact Hprogress.
Qed.
End Rewriting.
