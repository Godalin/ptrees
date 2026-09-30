(** Legacy rational external-validation vocabulary.
    Modelability, denotation and quotient laws delegate to the generic Model.
    Canonical countable/joint clients must not import this compatibility layer.
    Scalar Upper* mathematics is separate: it also serves native transport. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals boolp.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation.
From PTree.Prob.FreeOmega Require Import Quotient Measure.
From PTree.Prob.FreeOmega.Validation Require Import Model.
From PTree.Prob.Backend.SubEnumQ Require Import Measure Expectation Domain.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import UpperExpectation Validation CountableSupport JointRealization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Admissibility.
Variable R : realType.

Definition free_omega_admissible {A} (t : FreeOmega SubEnumQ A) : Prop :=
  OmegaValLaws (free_omega_upper (R := R) t).

Definition free_omega_domain {A} (t : FreeOmega SubEnumQ A)
    (H : free_omega_admissible t) : OmegaVal R A :=
  {| oval_eval := free_omega_upper t; oval_laws := H |}.

(** Avoid shadowing the maintained internal [free_omega_denotes] relation:
    this name explicitly denotes the independent mathematical domain. *)
Definition free_omega_domain_denotes {A} (t : FreeOmega SubEnumQ A)
    (L : OmegaVal R A) : Prop :=
  forall f, oval_test f -> free_omega_upper t f = oval_eval L f.

Theorem free_omega_admissible_iff_denotes {A} (t : FreeOmega SubEnumQ A) :
  free_omega_admissible t <-> exists L, free_omega_domain_denotes t L.
Proof. exact: (@modelable_iff_denotes SubEnumQ R (fun X => @subenumQ_domain R X)). Qed.

Lemma free_omega_admissible_ext {A} (t u : FreeOmega SubEnumQ A) :
  free_omega_admissible t ->
  (forall f : A -> R, oval_test f -> free_omega_upper t f = free_omega_upper u f) ->
  free_omega_admissible u.
Proof. exact: (@modelable_ext SubEnumQ R (fun X => @subenumQ_domain R X)). Qed.

Lemma admissible_ret {A} (x : A) : free_omega_admissible (FORet x).
Proof. exact (oval_laws (oval_ret R x)). Qed.
Lemma admissible_zero {A} : free_omega_admissible (@FOZero SubEnumQ A).
Proof. exact (oval_laws (@oval_bottom R A)). Qed.

Lemma admissible_sample {A X} (mu : SubEnumQ X) (k : X -> FreeOmega SubEnumQ A) :
  (forall x, free_omega_admissible (k x)) ->
  free_omega_admissible (FOSample mu k).
Proof. exact: (@modelable_sample SubEnumQ R (fun X => @subenumQ_domain R X)). Qed.

Definition free_omega_domain_increasing {A} (c : nat -> FreeOmega SubEnumQ A) :=
  forall n (f : A -> R), oval_test f ->
    free_omega_upper (c n) f <= free_omega_upper (c (S n)) f.

Lemma admissible_lub {A} (c : nat -> FreeOmega SubEnumQ A)
    (H : forall n, free_omega_admissible (c n)) :
  free_omega_domain_increasing c -> free_omega_admissible (FOLub c).
Proof. exact: (@modelable_lub SubEnumQ R (fun X => @subenumQ_domain R X)). Qed.

Lemma admissible_lub_approx {A} (c : nat -> FreeOmega SubEnumQ A) :
  (forall n, free_omega_admissible (c n)) ->
  (forall n, free_omega_approx eq (c n) (c (S n))) ->
  free_omega_admissible (FOLub c).
Proof. exact: (modelable_lub_approx (@subenumQ_native_model_lift R)). Qed.

Lemma admissible_bind {A B} (t : FreeOmega SubEnumQ A)
    (k : A -> FreeOmega SubEnumQ B) :
  free_omega_admissible t -> (forall x, free_omega_admissible (k x)) ->
  free_omega_admissible (free_omega_bind t k).
Proof. exact: (@modelable_bind SubEnumQ R (fun X => @subenumQ_domain R X)). Qed.

(** A proof-only replacement outside the AE support. This is not a denotation
    for inadmissible terms: replacing them by zero is sound only under the
    explicit support hypothesis in the closure theorems below. *)
Definition admissible_support_kernel {A} (t : FreeOmega SubEnumQ A) :
    FreeOmega SubEnumQ A :=
  if pselect (free_omega_admissible t) then t else FOZero.

Lemma admissible_support_kernel_valid {A} (t : FreeOmega SubEnumQ A) :
  free_omega_admissible (admissible_support_kernel t).
Proof. rewrite /admissible_support_kernel; case: pselect=> H; [exact H|exact: admissible_zero]. Qed.
Lemma admissible_support_kernel_eq {A} (t : FreeOmega SubEnumQ A) :
  free_omega_admissible t -> admissible_support_kernel t = t.
Proof. exact: (@model_support_kernel_eq SubEnumQ R (fun X => @subenumQ_domain R X)). Qed.

Theorem admissible_bind_ae {A B} (t : FreeOmega SubEnumQ A)
    (k : A -> FreeOmega SubEnumQ B) :
  free_omega_admissible t ->
  free_omega_ae (fun x => free_omega_admissible (k x)) t ->
  free_omega_admissible (free_omega_bind t k).
Proof. exact: (modelable_bind_ae (@subenumQ_native_model_ae R)). Qed.

Theorem admissible_sample_ae {A X} (mu : SubEnumQ X)
    (k : X -> FreeOmega SubEnumQ A) :
  sem_ae mu (fun x => free_omega_admissible (k x)) ->
  free_omega_admissible (FOSample mu k).
Proof. exact: (modelable_sample_ae (@subenumQ_native_model_ae R)). Qed.
End Admissibility.

Section DomainSoundness.
Variable R : realType.

Theorem free_omega_domain_spec {A} (t : FreeOmega SubEnumQ A)
    (H : free_omega_admissible R t) :
  free_omega_domain_denotes t (free_omega_domain H).
Proof. intros f Hf; reflexivity. Qed.

Theorem free_omega_domain_proof_independent {A} (t : FreeOmega SubEnumQ A)
    (H H' : free_omega_admissible R t) :
  oval_eq (free_omega_domain H) (free_omega_domain H').
Proof. intros f Hf; reflexivity. Qed.

Theorem free_omega_denote_ret {A} (x : A) :
  free_omega_domain_denotes (FORet x) (oval_ret R x).
Proof. intros f Hf; reflexivity. Qed.
Theorem free_omega_denote_zero {A} :
  free_omega_domain_denotes (@FOZero SubEnumQ A) (@oval_bottom R A).
Proof. intros f Hf; reflexivity. Qed.

Theorem free_omega_denote_sample {A X} (mu : SubEnumQ X)
    (k : X -> FreeOmega SubEnumQ A) (K : X -> OmegaVal R A) :
  (forall x, free_omega_domain_denotes (k x) (K x)) ->
  free_omega_domain_denotes (FOSample mu k) (oval_bind (subenumQ_domain R mu) K).
Proof.
  intros H f Hf; cbn [free_omega_upper oval_bind oval_eval subenumQ_domain].
  f_equal; apply functional_extensionality=> x; exact (H x f Hf).
Qed.

Theorem free_omega_denote_native {A} (mu : SubEnumQ A) :
  free_omega_domain_denotes (FOSample mu (fun x => FORet x)) (subenumQ_domain R mu).
Proof. intros f Hf; reflexivity. Qed.

Theorem free_omega_denote_bind {A B} (t : FreeOmega SubEnumQ A)
    (k : A -> FreeOmega SubEnumQ B) (L : OmegaVal R A) (K : A -> OmegaVal R B) :
  free_omega_domain_denotes t L ->
  (forall x, free_omega_domain_denotes (k x) (K x)) ->
  free_omega_domain_denotes (free_omega_bind t k) (oval_bind L K).
Proof. exact: (@model_denotes_bind SubEnumQ R (fun X => @subenumQ_domain R X)). Qed.

Theorem free_omega_denote_bind_ae {A B} (t : FreeOmega SubEnumQ A)
    (k : A -> FreeOmega SubEnumQ B) (L : OmegaVal R A) (K : A -> OmegaVal R B) :
  free_omega_domain_denotes t L ->
  free_omega_ae (fun x => free_omega_domain_denotes (k x) (K x)) t ->
  free_omega_domain_denotes (free_omega_bind t k) (oval_bind L K).
Proof. exact: (model_denotes_bind_ae (@subenumQ_native_model_ae R)). Qed.

Theorem free_omega_denote_sample_ae {A X} (mu : SubEnumQ X)
    (k : X -> FreeOmega SubEnumQ A) (K : X -> OmegaVal R A) :
  sem_ae mu (fun x => free_omega_domain_denotes (k x) (K x)) ->
  free_omega_domain_denotes (FOSample mu k) (oval_bind (subenumQ_domain R mu) K).
Proof. exact: (model_denotes_sample_ae (@subenumQ_native_model_ae R)). Qed.

Theorem free_omega_denote_lub {A} (c : nat -> FreeOmega SubEnumQ A)
    (L : nat -> OmegaVal R A) (Hi : oval_increasing L) :
  (forall n, free_omega_domain_denotes (c n) (L n)) ->
  free_omega_domain_denotes (FOLub c) (oval_lub Hi).
Proof. exact: (@model_denotes_lub SubEnumQ R (fun X => @subenumQ_domain R X)). Qed.

(** Approximation is sound for the mathematical information order.
    The heterogeneous test inequality below is not called a joint coupling. *)
Theorem free_omega_denote_approx {A} (t u : FreeOmega SubEnumQ A)
    (L M : OmegaVal R A) :
  free_omega_domain_denotes t L -> free_omega_domain_denotes u M ->
  free_omega_approx eq t u -> oval_le L M.
Proof. intros Ht Hu H f Hf; rewrite -(Ht f Hf) -(Hu f Hf).
  eapply (model_upper_approx (@subenumQ_native_model_lift R));
    [exact H|exact Hf|exact Hf|]; intros x y ->; exact: lexx. Qed.

Theorem free_omega_denote_approx_test {A B} (S : A -> B -> Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (L : OmegaVal R A) (M : OmegaVal R B) (f : A -> R) (g : B -> R) :
  free_omega_domain_denotes t L -> free_omega_domain_denotes u M ->
  free_omega_approx S t u -> oval_test f -> oval_test g ->
  (forall x y, S x y -> f x <= g y) -> oval_eval L f <= oval_eval M g.
Proof. intros Ht Hu H Hf Hg Hfg; rewrite -(Ht f Hf) -(Hu g Hg).
  exact (model_upper_approx (@subenumQ_native_model_lift R) H Hf Hg Hfg). Qed.

Theorem free_omega_domain_increasing_of_approx {A} (c : nat -> FreeOmega SubEnumQ A)
    (H : forall n, free_omega_admissible R (c n)) :
  (forall n, free_omega_approx eq (c n) (c (S n))) ->
  oval_increasing (fun n => free_omega_domain (H n)).
Proof. intros Hi n f Hf.
  eapply (model_upper_approx (@subenumQ_native_model_lift R));
    [exact (Hi n)|exact Hf|exact Hf|]; intros x y ->; exact: lexx. Qed.
End DomainSoundness.

Section QuotientSoundness.
Variable R : realType.

(** Only equality preserves admissibility this way: arbitrary relational
    liftings may pass through inadmissible raw terms on other carriers. *)
Theorem free_omega_qlift_eq_admissible {A} (t u : FreeOmega SubEnumQ A) :
  free_omega_qlift eq t u ->
  (free_omega_admissible R t <-> free_omega_admissible R u).
Proof. exact: subenumQ_qlift_eq_modelable. Qed.

(** Both proof arguments can be arbitrary; obtain either one's existence
    from the preceding iff when only one endpoint is initially valid. *)
Theorem free_omega_qlift_eq_sound {A} (t u : FreeOmega SubEnumQ A)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  free_omega_qlift eq t u ->
  oval_eq (free_omega_domain Ht) (free_omega_domain Hu).
Proof. exact: subenumQ_qlift_eq_sound. Qed.

(** Pin sem_eq to the maintained observable instance, not the auxiliary
    structural instance. No Semantic capability becomes a new premise. *)
Theorem free_omega_sem_eq_admissible {A} (t u : FreeOmega SubEnumQ A) :
  @sem_eq (FreeOmega SubEnumQ)
    (@FreeOmegaObservableSemanticMeasure SubEnumQ
      SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega) A t u ->
  (free_omega_admissible R t <-> free_omega_admissible R u).
Proof. exact: free_omega_qlift_eq_admissible. Qed.

Theorem free_omega_sem_eq_sound {A} (t u : FreeOmega SubEnumQ A)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  @sem_eq (FreeOmega SubEnumQ)
    (@FreeOmegaObservableSemanticMeasure SubEnumQ
      SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega) A t u ->
  oval_eq (free_omega_domain Ht) (free_omega_domain Hu).
Proof. exact: free_omega_qlift_eq_sound. Qed.
End QuotientSoundness.

Section CountableCompatibility.
Variable R : realType.
Theorem free_omega_domain_enumerated {A} (t : FreeOmega SubEnumQ A)
    (H : free_omega_admissible R t) :
  oval_ae (free_omega_domain H) (oval_enumerated (free_omega_enumerate t)).
Proof. exact: subenumQ_free_omega_model_enumerated. Qed.

Theorem free_omega_domain_countable {A} (t : FreeOmega SubEnumQ A)
    (H : free_omega_admissible R t) : oval_countably_supported (free_omega_domain H).
Proof. exact: subenumQ_free_omega_model_countable. Qed.

Theorem free_omega_domain_countable_representation {A} (t : FreeOmega SubEnumQ A)
    (H : free_omega_admissible R t) :
  exists N : OmegaVal R nat,
    oval_mass N = oval_mass (free_omega_domain H) /\
    oval_ae N (fun n => exists x, free_omega_enumerate t n = Some x) /\
    oval_eq (free_omega_domain H)
      (oval_bind N (oval_decode R (free_omega_enumerate t))).
Proof. apply oval_countable_representation; exact: free_omega_domain_enumerated. Qed.
End CountableCompatibility.

Section Soundness.
Variable R : realType.
Local Notation qlift := (@free_omega_qlift SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).

(** Apply the all-raw theorem once. No induction on a qlift derivation,
    and no admissibility premise on any FOQLComp intermediate. *)
Theorem free_omega_qlift_domain_bidual {A B} (T : A -> B -> Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift T t u -> oval_bidual T (free_omega_domain Ht) (free_omega_domain Hu).
Proof. exact: subenumQ_generic_qlift_bidual. Qed.

Theorem free_omega_qlift_countable_constraints {A B} (T : A -> B -> Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift T t u ->
  oval_countably_supported (free_omega_domain Ht) /\
  oval_countably_supported (free_omega_domain Hu) /\
  oval_bidual T (free_omega_domain Ht) (free_omega_domain Hu).
Proof.
  intro H; split; first exact: free_omega_domain_countable.
  split; first exact: free_omega_domain_countable.
  exact (free_omega_qlift_domain_bidual Ht Hu H).
Qed.

Theorem free_omega_qlift_domain_mass {A B} (T : A -> B -> Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift T t u -> oval_mass (free_omega_domain Ht) = oval_mass (free_omega_domain Hu).
Proof. intro H; apply (@oval_bidual_mass R A B T); exact (free_omega_qlift_domain_bidual Ht Hu H). Qed.

Theorem free_omega_qlift_domain_hall {A B} (T : A -> B -> Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift T t u -> forall P,
    oval_eval (free_omega_domain Ht) (oval_indicator R P) <=
    oval_eval (free_omega_domain Hu) (oval_indicator R (oval_rel_image T P)).
Proof. intro H; apply oval_dual_hall; exact (proj1 (free_omega_qlift_domain_bidual Ht Hu H)). Qed.

Theorem free_omega_qlift_eq_joint {A} (t u : FreeOmega SubEnumQ A)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift eq t u ->
  oval_joint eq (free_omega_domain Ht) (free_omega_domain Hu)
    (oval_bind (free_omega_domain Ht) (fun x => oval_ret R (x,x))).
Proof. intro H; apply oval_eq_joint; exact (free_omega_qlift_eq_sound Ht Hu H). Qed.

Theorem free_omega_qlift_eq_joint_agrees_ds3 {A} (t u : FreeOmega SubEnumQ A)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  oval_coupled eq (free_omega_domain Ht) (free_omega_domain Hu) <->
  oval_eq (free_omega_domain Ht) (free_omega_domain Hu).
Proof. exact: oval_eq_coupled_iff. Qed.
End Soundness.

Section JointCompatibility.
Variable R : realType.
Local Notation qlift := (@free_omega_qlift SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).
Theorem free_omega_qlift_sound {A B} (T : A -> B -> Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift T t u -> oval_coupled T (free_omega_domain Ht) (free_omega_domain Hu).
Proof. exact: subenumQ_qlift_sound. Qed.

(** Recover DS3 bounded equality through general joint realization. No claim
    identifies the existential joint with the separately constructed diagonal. *)
Theorem free_omega_qlift_eq_sound_via_joint {A} (t u : FreeOmega SubEnumQ A)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift eq t u -> oval_eq (free_omega_domain Ht) (free_omega_domain Hu).
Proof. exact: subenumQ_qlift_eq_sound_via_joint. Qed.

(** The realized joint has exactly the original subprobability mass;
    its complement-of-relation observable has expectation zero. *)
Theorem free_omega_qlift_joint_mass_support {A B} (T : A -> B -> Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift T t u -> exists J : OmegaVal R (A * B),
    oval_joint T (free_omega_domain Ht) (free_omega_domain Hu) J /\
    oval_mass J = oval_mass (free_omega_domain Ht) /\
    oval_mass J = oval_mass (free_omega_domain Hu) /\
    oval_eval J (oval_indicator R (fun z => ~ T (fst z) (snd z))) = 0.
Proof. exact: subenumQ_qlift_joint_mass_support. Qed.
End JointCompatibility.

Section SubEnumQValidation.
Variable R : realType.
Local Notation native := (fun X => @subenumQ_domain R X).

Theorem subenumQ_model_upper {A} (t : FreeOmega SubEnumQ A) f :
  free_omega_model_upper native t f = free_omega_upper t f.
Proof.
  reflexivity.
Qed.

Theorem subenumQ_modelable_iff_admissible {A} (t : FreeOmega SubEnumQ A) :
  free_omega_modelable native t <-> free_omega_admissible R t.
Proof.
  split; intro H; eapply oval_laws_ext; [exact H| |exact H|];
    intros f Hf; [symmetry|]; exact: subenumQ_model_upper.
Qed.

Theorem subenumQ_model_denotes_iff {A} (t : FreeOmega SubEnumQ A) L :
  free_omega_model_denotes native t L <-> free_omega_domain_denotes t L.
Proof.
  split; intros H f Hf.
  - rewrite -(subenumQ_model_upper t f); exact (H f Hf).
  - rewrite subenumQ_model_upper; exact (H f Hf).
Qed.

Theorem subenumQ_generic_domain_agrees {A} (t : FreeOmega SubEnumQ A)
    (H : free_omega_modelable native t) (Hds : free_omega_admissible R t) :
  oval_eq (free_omega_model H) (free_omega_domain Hds).
Proof. intros f Hf; exact: subenumQ_model_upper. Qed.

End SubEnumQValidation.

Section LegacyTests.
Variable R : realType.
(** The conclusion agrees with DS5 at the evaluator level, without
    replacing or depending on the frozen DS5 quotient induction. *)
Theorem subenumQ_generic_qlift_tests {A B} (T : A -> B -> Prop) t u (f : A -> R) (g : B -> R) :
  free_omega_qlift T t u -> oval_test f -> oval_test g ->
  (forall x y, T x y -> f x <= g y) ->
  free_omega_upper t f <= free_omega_upper u g.
Proof. intro H; exact (proj1 (subenumQ_qlift_bidual_raw R H) f g). Qed.
End LegacyTests.
