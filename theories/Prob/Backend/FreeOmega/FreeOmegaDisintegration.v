(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Universe Polymorphism.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.Backend Require Import TwoLevelMeasureSubEnum EnumDisintegration.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Conditional resampling is valid under an arbitrary FreeOmega
    continuation, including a higher-universe residual-tree kernel or an
    unbounded computation.  No native measure of those results is needed.
    Reconstruction of the WHOLE native joint is the premise; support and
    normalized fibers alone would not justify this equation. *)
Theorem free_omega_sample_disintegration {A B C}
    (mu : SubEnum A) (joint : SubEnum B) (conditional : A -> SubEnum B)
    (continue : B -> FreeOmega SubEnum C) :
  sem_eq (subenum_bind mu conditional) joint ->
  free_omega_qlift eq
    (FOSample mu (fun a => FOSample (conditional a) continue))
    (FOSample joint continue).
Proof.
  intro Hreconstruct.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := FOSample (subenum_bind mu conditional) continue).
  - apply (@FOQLSampleBind SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticOmega C C eq A B mu conditional continue continue).
    + intros P. apply (@sem_ae_bind_iff SubEnum SubEnum_SemanticMeasure
        SubEnum_SemanticMeasureBindAEExactLaws).
    + intro p. apply free_omega_qlift_refl. intro z. reflexivity.
  - eapply FOQLSample with (T := eq).
    + exact Hreconstruct.
    + intros p q ->. apply free_omega_qlift_refl. intro z. reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

(** The caller can use its own marginal representation.  Conditioning
    returns the pair, so the continuation may depend on BOTH components. *)
Theorem free_omega_resample_joint {A B C}
    (joint : SubEnum (A * B)) (mu : SubEnum A)
    (continue : A * B -> FreeOmega SubEnum C) :
  sem_lift (fun p x => fst p = x) joint mu ->
  exists conditional : A -> SubEnum (A * B),
    free_omega_qlift eq
      (FOSample mu (fun a => FOSample (conditional a) continue))
      (FOSample joint continue) /\
    (forall a, sem_ae (conditional a) (fun p => fst p = a)) /\
    sem_ae mu (fun a => subenum_total (conditional a)).
Proof.
  intro Hgraph.
  destruct (subenum_disintegration_over Hgraph)
    as [k [Hreconstruct [Hfiber [Hsupport Htotal]]]].
  exists k. split; [apply free_omega_sample_disintegration; exact Hreconstruct|].
  split; assumption.
Qed.
