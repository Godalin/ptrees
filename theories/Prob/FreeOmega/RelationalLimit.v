(** Relational continuity of the observable completion. This is stronger
    than ordinary equality-based lub properness. It is derived from qlift,
    not assumed by the generic probability interfaces. *)
Set Universe Polymorphism.
From PTree.Prob.Interface Require Import Measure Omega Mixed RelationalClosure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Quotient
  PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.StructuralMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RelationalLimit.
Context {MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).

Theorem free_omega_lift_lub {A B} (RR : A -> B -> Prop)
    (left : nat -> MF A) (right : nat -> MF B) out1 out2 :
  @sem_lub MF FI FO _ left out1 ->
  @sem_lub MF FI FO _ right out2 ->
  (forall n, @sem_lift MF FI _ _ RR (left n) (right n)) ->
  @sem_lift MF FI _ _ RR out1 out2.
Proof.
  intros Hleft Hright Hrel.
  eapply (sem_lift_proper_l (SI := FI)) with (mu := FOLub left).
  - apply sem_eq_sym. exact Hleft.
  - eapply (sem_lift_proper_r (SI := FI)) with (nu := FOLub right).
    + apply sem_eq_sym. exact Hright.
    + apply FOQLLub. exact Hrel.
Qed.

(** These four certificates do not require native AELift: the relational
    constructors themselves are weaker than the full bind-law bundles. *)
Theorem free_omega_relational_bind : relational_bind FI.
Proof. intros A B C D R T mu nu k h Hmu Hk. eapply FOQLBind; eassumption. Qed.

Theorem free_omega_relational_mixed_bind :
  relational_mixed_bind NI FI (FreeOmegaMixedMeasure (MN := MN)).
Proof. intros A B C D R T mu nu k h Hmu Hk. eapply FOQLSample; eassumption. Qed.

Theorem free_omega_relational_zero : relational_zero FO.
Proof. intros A B R. apply FOQLStructural. constructor. Qed.

Theorem free_omega_relational_lub : relational_lub FO.
Proof.
  intros A B R c d mu nu Hc Hd Hmu Hnu Hrel.
  eapply free_omega_lift_lub; eassumption.
Qed.
End RelationalLimit.
