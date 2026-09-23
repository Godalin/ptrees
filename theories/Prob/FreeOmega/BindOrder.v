(** Probability-level obligations for generic bind reasoning. Observable
    equality and structural approximation keep their distinct meanings. *)
Set Universe Polymorphism.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Omega
  PTree.Prob.Interface.Mixed PTree.Prob.Interface.BindOrder.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation
  PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.Measure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Laws.
Context {MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).

#[global] Instance FreeOmegaObservableBindOrderLaws :
  @SemanticMeasureBindOrderLaws (FreeOmega MN) FI FO.
Proof.
  constructor.
  - intros A B x k; split; cbn; apply free_omega_approx_refl; intro z; reflexivity.
  - intros A B k; cbn; constructor.
Qed.

#[global] Instance FreeOmegaObservableMixedBindOrderLaws :
  @MixedMeasureBindOrderLaws MN (FreeOmega MN) FI FreeOmegaMixedMeasure FO.
Proof.
  constructor.
  - intros A B C mu k h; split; cbn;
      apply free_omega_approx_refl; intro z; reflexivity.
  - intros A B mu k h H; cbn. eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl; intro z; reflexivity.
    + intros x y ->; apply H.
Qed.

#[global] Instance FreeOmegaObservableDirectedCofinalityLaws :
  @SemanticOmegaDirectedCofinalityLaws (FreeOmega MN) FI FO.
Proof.
  constructor. intros A c d out Hc Hd Hcd Hdc.
  apply free_omega_cofinal_lub_iff; try assumption.
  split; [exact Hcd|].
  intro n; destruct (Hdc n) as [m Hm]; exists m.
  eapply free_omega_approx_mono; [|exact Hm].
  intros x y ->; reflexivity.
Qed.

#[global] Instance FreeOmegaObservableOmegaSelection :
  @SemanticOmegaSelection (FreeOmega MN) FI FO.
Proof.
  constructor. intros A c Hi. exists (FOLub c).
  apply free_omega_qlift_refl; intro x; reflexivity.
Defined.
End Laws.
