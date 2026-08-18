Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import ShallowNew ProbabilisticEutt PStrong
  OperationalProbabilisticPTSFreeOmegaBase.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Iteration equations and fusion principles for the maintained FreeOmega
    backend.  Operational grids and productivity certificates will be
    colocated here as they are extracted from the compatibility Base. *)
Section FreeOmegaIter.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.
Local Notation MF := (FreeOmega MN).

Theorem free_probabilistic_eutt_iter_unfold {I R}
    (step : I -> ptree E MN (I + R)) (i : I) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.iter step i)
    (PTree.bind (step i) (fun lr =>
      match lr with
      | inl i' => Tau (PTree.iter step i')
      | inr r => Ret r
      end)).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply observe_eq_pstructural.
  exact (observing_observe (unfold_aloop_ step i)).
Qed.

Theorem free_probabilistic_eutt_iter_structural {I R}
    (step1 step2 : I -> ptree E MN (I + R)) (i : I) :
  (forall j, pstructural eq (step1 j) (step2 j)) ->
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.iter step1 i) (PTree.iter step2 i).
Proof.
  intro Hstep. apply free_probabilistic_eutt_of_pstructural.
  apply pstructural_iter. exact Hstep.
Qed.

Theorem free_probabilistic_eutt_iter_rel
    {I1 I2 R1 R2}
    (SI : I1 -> I2 -> Prop) (RR : R1 -> R2 -> Prop)
    (f : I1 -> ptree E MN (I1 + R1))
    (g : I2 -> ptree E MN (I2 + R2))
    (Hstep : forall i1 i2, SI i1 i2 ->
      pstructural (pstructural_iter_sum_rel SI RR) (f i1) (g i2))
    i1 i2 :
  SI i1 i2 ->
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R1 R2 RR
    (PTree.iter f i1) (PTree.iter g i2).
Proof.
  intro Hij. apply free_probabilistic_eutt_of_pstructural.
  eapply pstructural_iter_rel; eauto.
Qed.

End FreeOmegaIter.
