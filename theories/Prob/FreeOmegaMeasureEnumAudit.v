Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.

Require Import Program.Equality.

From mathcomp Require Import ssreflect ssrbool seq ssralg ssrnum order rat.
From PTree.Prob Require Import DiscreteMC FrontierLiftEnum
  MeasureIterationEnum TwoLevelMeasure TwoLevelMeasureEnum FreeOmegaMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum IndexedCoupling Coupling.
Import GRing.Theory.
Import Num.Theory.
Local Open Scope ring_scope.

Local Notation MF := (FreeOmegaAt Enum bool).

Definition transient_bad_chain (n : nat) : MF bool :=
  match n with
  | O => FORet false
  | Datatypes.S _ => FOZero
  end.

Definition zero_free_chain (_ : nat) : MF bool := FOZero.

Definition transient_bad_limit : MF bool := FOLub transient_bad_chain.
Definition zero_free_limit : MF bool := FOLub zero_free_chain.

Definition transient_observation (n : nat) : Enum bool :=
  match n with
  | O => ret_Enum false
  | Datatypes.S _ => [::]
  end.

Lemma transient_observation_converges_zero :
  enum_converges transient_observation [::].
Proof.
  intros P eps Heps. exists 1%nat. intros [|n] Hn; first inversion Hn.
  cbn. exact Heps.
Qed.

Lemma transient_bad_limit_observes_zero :
  @free_omega_observes Enum Enum_SemanticMeasureInterface
    Enum_SemanticOmegaInterface bool bool id
    transient_bad_limit [::].
Proof.
  unfold transient_bad_limit. eapply FOOObserveLub with
    (outs := transient_observation).
  - intros [|n]; constructor.
  - exact transient_observation_converges_zero.
Qed.

Lemma zero_free_limit_observes_zero :
  @free_omega_observes Enum Enum_SemanticMeasureInterface
    Enum_SemanticOmegaInterface bool bool id zero_free_limit [::].
Proof.
  unfold zero_free_limit.
  eapply (@FOOObserveLub Enum Enum_SemanticMeasureInterface
    Enum_SemanticOmegaInterface bool bool id zero_free_chain
    (fun _ : nat => (@nil (RatSubTypes.nnQ * bool))) [::]).
  - intro n. constructor.
  - intros P eps Heps. exists O. intros n _. cbn. exact Heps.
Qed.

Lemma enum_empty_lift_false :
  @sem_lift Enum Enum_SemanticMeasureInterface bool bool
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

(** Equal low-level observations alone still forget the transient [false]
    return, but the repaired observation constructor additionally asks for
    this support coupling.  The missing certificate is now provably
    impossible, so the former omega-AE counterexample is rejected at the
    quotient boundary rather than contradicting the backend laws. *)
Theorem transient_bad_support_zero_impossible :
  ~ @free_omega_support_lift Enum Enum_SemanticMeasureInterface bool bool eq
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
