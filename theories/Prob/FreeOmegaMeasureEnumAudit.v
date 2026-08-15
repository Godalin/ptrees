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

Lemma transient_bad_qlift_zero :
  @free_omega_qlift Enum Enum_SemanticMeasureInterface
    Enum_SemanticOmegaInterface bool bool eq
    transient_bad_limit zero_free_limit.
Proof.
  refine (@FOQLObserve Enum Enum_SemanticMeasureInterface
    Enum_SemanticOmegaInterface bool bool eq bool bool id id
    transient_bad_limit zero_free_limit [::] [::]
    (fun _ _ => False) _ _ _ _).
  - exact transient_bad_limit_observes_zero.
  - exact zero_free_limit_observes_zero.
  - exact enum_empty_lift_false.
  - intros x y Hfalse. contradiction.
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

(** The current observation quotient forgets transient returned support.
    Consequently its structural [sem_ae] cannot satisfy omega admissibility:
    a zero chain may have a quotient-equal representative containing a bad
    transient return.  This theorem is the formal design audit that forces
    observable AE or [FOQLObserve] to be strengthened before installing the
    desired backend capability. *)
Theorem observable_free_omega_omega_ae_impossible :
  ~ @SemanticOmegaAELaws MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface))
      FreeOmegaObservableSemanticOmegaInterface.
Proof.
  intro Hlaws.
  pose proof (@sem_ae_lub MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface Hlaws bool
    zero_free_chain transient_bad_limit (fun b => b = true)
    transient_bad_qlift_zero zero_chain_ae_true) as Hae.
  exact (transient_bad_limit_not_ae_true Hae).
Qed.
