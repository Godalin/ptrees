(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.

From Coq.Program Require Import Equality.

From mathcomp Require Import ssreflect ssrbool seq ssralg ssrnum order rat.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.FrontierLift PTree.Prob.Backend.EnumQ.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.EnumQ.Support.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ IndexedCoupling PTree.Prob.Backend.EnumQ.Coupling.
Import GRing.Theory.
Import Num.Theory.
Local Open Scope ring_scope.

Local Notation MF := (FreeOmegaAt EnumQ bool).

Definition transient_bad_chain (n : nat) : MF bool :=
  match n with
  | O => FORet false
  | Datatypes.S _ => FOZero
  end.

Definition zero_free_chain (_ : nat) : MF bool := FOZero.

Definition transient_bad_limit : MF bool := FOLub transient_bad_chain.
Definition zero_free_limit : MF bool := FOLub zero_free_chain.

Definition transient_observation (n : nat) : EnumQ bool :=
  match n with
  | O => ret_EnumQ false
  | Datatypes.S _ => [::]
  end.

Lemma transient_observation_converges_zero :
  enumQ_converges transient_observation [::].
Proof.
  intros P eps Heps. exists 1%nat. intros [|n] Hn; first inversion Hn.
  cbn. exact Heps.
Qed.

Lemma transient_bad_limit_not_observable out :
  ~ @free_omega_observes EnumQ EnumQ_SemanticMeasure
    EnumQ_SemanticOmega bool bool id transient_bad_limit out.
Proof.
  intro H. dependent destruction H.
  specialize (H1 O). dependent destruction H1.
Qed.

Lemma zero_free_limit_observes_zero :
  @free_omega_observes EnumQ EnumQ_SemanticMeasure
    EnumQ_SemanticOmega bool bool id zero_free_limit [::].
Proof.
  unfold zero_free_limit.
  eapply (@FOOObserveLub EnumQ EnumQ_SemanticMeasure
    EnumQ_SemanticOmega bool bool id zero_free_chain
    (fun _ : nat => (@nil (PTree.Prob.Backend.Common.RatSubTypes.nnQ * bool))) [::]).
  - intro n. constructor.
  - intros P eps Heps. exists O. intros n _. cbn. exact Heps.
  - intro n. apply FOApproxZero.
Qed.

Lemma enumQ_empty_lift_false :
  @sem_lift EnumQ EnumQ_SemanticMeasure bool bool
    (fun _ _ => False) [::] [::].
Proof.
  cbn. unfold indexed_coupling. exists [::]; try reflexivity.
  intros i j Hnz. cbn in Hnz. discriminate.
Qed.

Lemma zero_chain_ae_true : forall n,
  free_omega_ae (fun b => b = true) (zero_free_chain n).
Proof. intro n. constructor. Qed.

Lemma transient_bad_limit_not_ae_true :
  ~ free_omega_ae (fun b => b = true) transient_bad_limit.
Proof.
  intro Hae. dependent destruction Hae.
  specialize (H O). dependent destruction H.
Qed.

(** The native sequence converges to zero, but its formal Lub is now
    rejected already by observation's raw-monotonicity premise.  Its
    missing support certificate is an independent obstruction to the
    quotient observation rule and remains a useful AE regression. *)
Theorem transient_bad_support_zero_impossible :
  ~ @free_omega_support_lift EnumQ EnumQ_SemanticMeasure bool bool eq
      transient_bad_limit zero_free_limit.
Proof.
  intro Hsupport.
  assert (Hzero : free_omega_ae (fun b => b = true) zero_free_limit).
  { unfold zero_free_limit. constructor. exact zero_chain_ae_true. }
  pose proof ((proj2 Hsupport) _ Hzero) as Himage.
  apply transient_bad_limit_not_ae_true.
  eapply free_omega_ae_mono; [|exact Himage].
  intros x [y [-> Hy]]. exact Hy.
Qed.

Check FreeOmegaObservableSemanticOmegaAELaws.

(** The AE-continuity theorem deliberately excludes this disappearing atom. *)
Example transient_observation_not_increasing :
  ~ enumQ_chain_increasing transient_observation.
Proof.
  intro H. specialize (H (fun _ => true) O (S O) (Peano.le_0_n _)).
  vm_compute in H. discriminate.
Qed.
