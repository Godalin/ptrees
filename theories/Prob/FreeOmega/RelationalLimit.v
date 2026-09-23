(** Relational continuity of the observable completion. This is stronger
    than ordinary equality-based lub properness. It is derived from qlift,
    not assumed by the generic probability interfaces. *)
Set Universe Polymorphism.
From PTree.Prob.Interface Require Import Measure Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Quotient
  PTree.Prob.FreeOmega.Measure.
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
End RelationalLimit.
