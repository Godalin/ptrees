(** Sufficient conditions for relational limits, derived from existing laws.
    No realization or relational-continuity capability is postulated here.
    In particular, increasing marginals do NOT imply increasing joints. *)
Set Universe Polymorphism.
From PTree.Prob.Interface Require Import Measure AE Omega.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section JointLimit.
Context {M : Type -> Type} `{MI : SemanticMeasure M}
  `{MC : @SemanticMeasureCoreLaws M MI}
  `{MB : @SemanticMeasureBindLaws M MI}
  `{MA : @SemanticMeasureAELiftLaws M MI}
  `{MO : @SemanticOmega M MI}
  `{ML : @SemanticOmegaLaws M MI MO}
  `{MEA : @SemanticOmegaAELaws M MI MO}.

(** The marginal certificates are sem_eq, not merely equality liftings.
    Thus this argument does not smuggle in equality reflection. *)
Theorem sem_lift_lub_of_joint_chain {A B} (R : A -> B -> Prop)
    (left : nat -> M A) (right : nat -> M B)
    (joints : nat -> M (A * B)) out1 out2 :
  sem_increasing joints ->
  sem_lub left out1 -> sem_lub right out2 ->
  (forall n, sem_eq (sem_bind (joints n) (fun p => sem_ret (fst p))) (left n)) ->
  (forall n, sem_eq (sem_bind (joints n) (fun p => sem_ret (snd p))) (right n)) ->
  (forall n, sem_ae (joints n) (fun p => R (fst p) (snd p))) ->
  sem_lift R out1 out2.
Proof.
  intros Hi Hl Hr Hleft Hright Hsupport.
  destruct (sem_lub_exists Hi) as [joint Hj].
  assert (Heleft : sem_eq
    (sem_bind joint (fun p => sem_ret (fst p))) out1).
  { eapply sem_lub_proper; [exact Hleft| |exact Hl].
    eapply sem_bind_lub; eassumption. }
  assert (Heright : sem_eq
    (sem_bind joint (fun p => sem_ret (snd p))) out2).
  { eapply sem_lub_proper; [exact Hright| |exact Hr].
    eapply sem_bind_lub; eassumption. }
  eapply sem_lift_proper_l; [exact Heleft|].
  eapply sem_lift_proper_r; [exact Heright|].
  eapply sem_lift_bind with (R := fun p q => p = q /\ R (fst p) (snd p)).
  - apply sem_lift_refl_ae. eapply sem_ae_lub; eassumption.
  - intros p q [<- Hpq]. apply sem_lift_ret. exact Hpq.
Qed.
End JointLimit.
