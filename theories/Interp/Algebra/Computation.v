(** Finite computation steps used by effect algebra. These lemmas do not
    identify visible source effects or postulate an interpreter congruence. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Mixed Omega.
From PTree.Eq Require Import PEutt.
Set Implicit Arguments.
Unset Strict Implicit.

Section Observation.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.

Lemma peutt_observe_eq {A} (t u : ptree E MN A) :
  observe t = observe u -> peutt (MF := MF) eq t u.
Proof. intro H. unfold peutt. rewrite H. apply peutt_state_refl. Qed.

Context `{NI : SemanticMeasure MN} `{FB : @SemanticMeasureBindLaws MF FI}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}.

Lemma peutt_tau_step {A} (t u v : ptree E MN A) :
  observe t = TauF u -> peutt (MF := MF) eq u v -> peutt (MF := MF) eq t v.
Proof.
  intros H Huv. eapply peutt_trans with (y := Tau u).
  - apply peutt_observe_eq. exact H.
  - eapply peutt_trans; [apply peutt_tau_l|exact Huv].
Qed.
End Observation.
