(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Universe Polymorphism.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.Disintegration.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Conditional resampling is valid under an arbitrary FreeOmega
    continuation, including a higher-universe residual-tree kernel or an
    unbounded computation.  No native measure of those results is needed.
    Reconstruction of the WHOLE native joint is the premise; support and
    normalized fibers alone would not justify this equation. *)
Theorem free_omega_sample_disintegration {A B C}
    (mu : SubEnumQ A) (joint : SubEnumQ B) (conditional : A -> SubEnumQ B)
    (continue : B -> FreeOmega SubEnumQ C) :
  sem_eq (subenumQ_bind mu conditional) joint ->
  free_omega_qlift eq
    (FOSample mu (fun a => FOSample (conditional a) continue))
    (FOSample joint continue).
Proof.
  intro Hreconstruct.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := FOSample (subenumQ_bind mu conditional) continue).
  - apply (@FOQLSampleBind SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticOmega C C eq A B mu conditional continue continue).
    + intros P. apply (@sem_ae_bind_iff SubEnumQ SubEnumQ_SemanticMeasure
        SubEnumQ_SemanticMeasureBindAEExactLaws).
    + intro p. apply free_omega_qlift_refl. intro z. reflexivity.
  - eapply FOQLSample with (T := eq).
    + exact Hreconstruct.
    + intros p q ->. apply free_omega_qlift_refl. intro z. reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

(** The caller can use its own marginal representation.  Conditioning
    returns the pair, so the continuation may depend on BOTH components. *)
Theorem free_omega_resample_joint {A B C}
    (joint : SubEnumQ (A * B)) (mu : SubEnumQ A)
    (continue : A * B -> FreeOmega SubEnumQ C) :
  sem_lift (fun p x => fst p = x) joint mu ->
  exists conditional : A -> SubEnumQ (A * B),
    free_omega_qlift eq
      (FOSample mu (fun a => FOSample (conditional a) continue))
      (FOSample joint continue) /\
    (forall a, sem_ae (conditional a) (fun p => fst p = a)) /\
    sem_ae mu (fun a => subenumQ_total (conditional a)).
Proof.
  intro Hgraph.
  destruct (subenumQ_disintegration_over Hgraph)
    as [k [Hreconstruct [Hfiber [Hsupport Htotal]]]].
  exists k. split; [apply free_omega_sample_disintegration; exact Hreconstruct|].
  split; assumption.
Qed.
