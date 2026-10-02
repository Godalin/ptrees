(** Coinduction up to bind and one visible continuation context.
    Visible contexts belong to the proof closure, not to the client's
    recursive invariant. This derives a proof rule from the existing
    up-to-bind theorem; it changes neither peutt nor its generator. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Eq Require Import PTreeKernel StableHittingRelation PEutt BindScheduling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section VisibleContext.
Context {E MN : Type → Type} {A B : Type}.
Local Notation state1 := (ptree' E MN A).
Local Notation state2 := (ptree' E MN B).

Definition vis_upto_closure (sim : state1 → state2 → Prop)
    (s1 : state1) (s2 : state2) : Prop :=
  sim s1 s2 ∨
  ∃ (X : Type) (e : E X)
    (k1 : X → ptree E MN A) (k2 : X → ptree E MN B),
    s1 = VisF e k1 ∧ s2 = VisF e k2 ∧
    ∀ x, sim (observe (k1 x)) (observe (k2 x)).

Lemma vis_upto_closure_includes sim s1 s2 :
  sim s1 s2 → vis_upto_closure sim s1 s2.
Proof. intro H. left. exact H. Qed.

Lemma vis_upto_closure_vis sim {X} (e : E X) k1 k2 :
  (∀ x, sim (observe (k1 x)) (observe (k2 x))) →
  vis_upto_closure sim (VisF e k1) (VisF e k2).
Proof.
  intro H. right. exists X, e, k1, k2. repeat split; auto.
Qed.
End VisibleContext.

Section BindVisibleContext.
Context {E MN MF : Type → Type}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{BindOrd : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MixedOrd : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.

(** The bind continuation may re-enter [sim], put a common visible event
    before re-entry, or close by an already proved peutt. Each root still
    progresses through complete stable hitting. In particular this rule
    does not treat internal sampling or Tau as a visible guard.
    As for generic [peutt_bind], finite scheduling is derived from the
    probability-level order laws, not supplied by the client. *)
Theorem peutt_coinduction_upto_bind_vis {A B} (RR : A → B → Prop)
    (sim : ptree' E MN A → ptree' E MN B → Prop)
    (Hprogress : ∀ s1 s2, sim s1 s2 →
      stable_hitting_match
        (@ptree_primitive_kernel E MN MF FI MX A)
        (@ptree_primitive_kernel E MN MF FI MX B)
        (@ptree_stable_head_rel E MN A B RR)
        (bind_upto_closure RR (vis_upto_closure sim)) s1 s2) :
  ∀ t u, sim (observe t) (observe u) → peutt (MF := MF) RR t u.
Proof.
  intros t u Hsim.
  eapply peutt_coinduction_upto_bind with (sim := vis_upto_closure sim);
    try typeclasses eauto.
  - intros X Y t0 k. apply BindScheduling.ptree_bind_cofinal_all.
    + exact (@sem_bind_ret_order MF FI FO BindOrd).
    + exact (@sem_bind_zero_order MF FI FO BindOrd).
    + exact (@mixed_bind_assoc_order MN MF FI MX FO MixedOrd).
    + exact (@mixed_bind_le_k MN MF FI MX FO MixedOrd).
    + exact (@sem_lub_cofinal MF FI FO Directed).
  - intros s1 s2 [Hroot | (X & e & k1 & k2 & -> & -> & Hk)].
    + exact (Hprogress _ _ Hroot).
    + apply stable_hitting_match_vis. intro x.
      apply bind_upto_closure_includes, vis_upto_closure_includes, Hk.
  - apply vis_upto_closure_includes. exact Hsim.
Qed.
End BindVisibleContext.
