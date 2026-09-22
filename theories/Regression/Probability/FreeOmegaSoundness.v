(** Equality, countable support and arbitrary-carrier joint soundness contracts.
    The first block deliberately tests the independent external layer before
    importing FreeOmega. Shared samples live in Regression/Fixtures. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum order rat reals.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
From PTree.Prob.Backend.Common Require Import CountableCoupling.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Core.PTreeDefinition.ptree.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Lemma dirac_countable (R : realType) {A} (x : A) : oval_countably_supported (oval_ret R x).
Proof.
  exists (fun _ => Some x); intros f g Hf Hg Hfg; apply Hfg; exists O; reflexivity.
Qed.

Lemma bottom_countable (R : realType) A : oval_countably_supported (@oval_bottom R A).
Proof. exists (fun _ => None); intros f g Hf Hg Hfg; reflexivity. Qed.

Example empty_carrier_joint (R : realType) :
  oval_coupled (fun (_ : Empty_set) (_ : bool) => False) (oval_bottom R) (oval_bottom R).
Proof.
  apply oval_bidual_coupled; [exact: bottom_countable|exact: bottom_countable|].
  split; intros f g Hf Hg Hfg; exact: lexx.
Qed.

Section LargeCarriers.
Universe u v.
Variable R : realType.
(** Values are themselves types, on independently quantified universes. *)
Example type_carrier_joint (A : Type@{u}) (B : Type@{v}) :
  oval_coupled (fun (_ : Type@{u}) (_ : Type@{v}) => True) (oval_ret R A) (oval_ret R B).
Proof.
  apply oval_bidual_coupled; [exact: dirac_countable|exact: dirac_countable|].
  split; intros f g Hf Hg Hfg; apply Hfg; exact I.
Qed.
End LargeCarriers.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Core.PTreeDefinition.ptree.
(** Role: DS3 equality/validity boundary tests. In particular, a genuine
    FOQLComp may have an inadmissible intermediate on another carrier.
    Neither quotient equality alone nor arbitrary relational lifting is
    a certificate that every raw term denotes a subprobability. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Domain Require Import Expectation.
From PTree.Prob.Interface Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Quotient Measure.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import
  Admissibility QuotientSoundness.

Fail Check PTree.Prob.Domain.MeasureModel.oval_probability.
Fail Check PTree.Core.PTreeDefinition.ptree.
Fail Check PTree.Eq.PEutt.peutt.

From PTree.Regression.Probability Require Import FreeOmegaDomain.
From PTree.Regression.Fixtures Require Import FreeOmegaSamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Notation observable_measure := (@FreeOmegaObservableSemanticMeasure
  SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).

Definition constant_unit : FreeOmega SubEnumQ unit := FOLub (fun _ => FORet tt).

Lemma constant_to_invalid :
  free_omega_qlift (fun (_ : unit) (_ : bool) => True) constant_unit alternating_bool.
Proof. apply FOQLLub=> n; apply FOQLStructural; constructor; exact I. Qed.

Lemma invalid_to_ret :
  free_omega_qlift (fun (_ : bool) (_ : unit) => True) alternating_bool (FORet tt).
Proof.
  eapply FOQLComp with (mid := constant_unit) (T := fun _ _ => True) (U := eq).
  - apply FOQLLub=> n; apply FOQLStructural; constructor; exact I.
  - apply FOQLSym, FOQLLubConstantR, FOQLStructural; constructor; reflexivity.
  - intros x [] _; exact I.
Qed.

(** Deliberately use the inadmissible alternating carrier as FOQLComp's
    actual middle term. Do not replace this evidence with reflexivity. *)
Lemma equality_through_invalid_middle :
  free_omega_qlift eq constant_unit (FORet tt).
Proof.
  eapply FOQLComp with (mid := alternating_bool)
    (T := fun _ _ => True) (U := fun _ _ => True).
  - exact constant_to_invalid.
  - exact invalid_to_ret.
  - intros [] [] _; reflexivity.
Qed.

Lemma retry_quotient :
  @sem_eq _ observable_measure _
    (FOLub retry_approx) (FOLub (fun _ => FOLub retry_approx)).
Proof. apply FOQLLubConstantR, free_omega_qlift_refl; intros x; reflexivity. Qed.

Section Tests.
Variable R : realType.

Example invalid_middle_really_invalid : ~ free_omega_admissible R alternating_bool.
Proof. exact: alternating_bool_not_admissible. Qed.

Lemma constant_valid_by_quotient : free_omega_admissible R constant_unit.
Proof.
  apply (proj2 (free_omega_qlift_eq_admissible R equality_through_invalid_middle)).
  exact: admissible_ret.
Qed.

Example invalid_middle_does_not_block_soundness :
  oval_eq (free_omega_domain constant_valid_by_quotient)
    (free_omega_domain (@admissible_ret R unit tt)).
Proof. apply free_omega_qlift_eq_sound; exact equality_through_invalid_middle. Qed.

Example equality_alone_is_not_validity :
  free_omega_qlift eq alternating_bool alternating_bool /\
  ~ free_omega_admissible R alternating_bool.
Proof.
  split; [apply free_omega_qlift_refl; intros x; reflexivity|].
  exact: alternating_bool_not_admissible.
Qed.

Example invalid_not_equal_to_valid (t : FreeOmega SubEnumQ bool) :
  free_omega_admissible R t -> ~ @sem_eq _ observable_measure _ alternating_bool t.
Proof.
  intros Hv H; apply (@alternating_bool_not_admissible R).
  exact (proj2 (free_omega_sem_eq_admissible R H) Hv).
Qed.

Lemma retry_valid_by_quotient :
  free_omega_admissible R (FOLub (fun _ => FOLub retry_approx)).
Proof.
  apply (proj1 (free_omega_sem_eq_admissible R retry_quotient)).
  exact: unbounded_retry_admissible.
Qed.

Example unbounded_retry_quotient_sound :
  oval_eq (free_omega_domain (unbounded_retry_admissible R))
    (free_omega_domain retry_valid_by_quotient).
Proof. apply free_omega_sem_eq_sound; exact retry_quotient. Qed.

Example soundness_ignores_validity_proofs
    (H1 H2 : free_omega_admissible R constant_unit)
    (H3 : free_omega_admissible R (FORet tt)) :
  oval_eq (free_omega_domain H1) (free_omega_domain H3) /\
  oval_eq (free_omega_domain H2) (free_omega_domain H3).
Proof. split; apply free_omega_sem_eq_sound; exact equality_through_invalid_middle. Qed.

Example quotient_cannot_erase_missing_mass :
  ~ @sem_eq _ observable_measure _ (@FOZero SubEnumQ unit) (FORet tt).
Proof.
  intro H.
  have Heq := free_omega_sem_eq_sound (@admissible_zero R unit) (@admissible_ret R unit tt) H.
  have H01 := Heq (fun _ => 1) (oval_test_one R).
  change (0 = (1 : R)) in H01.
  have Hneq : (1 : R) != 0 by apply oner_neq0.
  by rewrite -H01 eqxx in Hneq.
Qed.
End Tests.

(** Countable representation and all-raw dual contracts; the final block below
    additionally checks general joint realization. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrbool eqtype choice ssrnat ssralg ssrnum order reals.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.FreeOmega Require Import Approximation Quotient.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import
  Admissibility CountableSupport CouplingSoundness.
Fail Check PTree.Prob.Domain.MeasureModel.oval_probability.
Fail Check PTree.Eq.PEutt.peutt.
From PTree.Regression.Probability Require Import FreeOmegaDomain.
From PTree.Regression.Fixtures Require Import FreeOmegaSamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Example empty_cover n : free_omega_enumerate (@FOZero SubEnumQ Empty_set) n = None.
Proof. reflexivity. Qed.

Example raw_invalid_cover :
  free_omega_ae (oval_enumerated (free_omega_enumerate alternating_bool)) alternating_bool.
Proof. exact: free_omega_enumerate_covers. Qed.

Definition returns_true (_ : unit) (b : bool) := b = true.
Lemma heterogeneous_invalid_middle : free_omega_qlift returns_true constant_unit (FORet true).
Proof.
  eapply FOQLComp with (mid := alternating_bool)
    (T := fun (_ : unit) (_ : bool) => True) (U := fun (_ : bool) b => b = true).
  - exact constant_to_invalid.
  - eapply FOQLComp with (mid := FORet tt)
      (T := fun (_ : bool) (_ : unit) => True) (U := fun (_ : unit) b => b = true).
    + exact invalid_to_ret.
    + apply FOQLStructural, FOLRet; reflexivity.
    + intros x b [y [_ Hb]]; exact Hb.
  - intros x b [y [_ Hb]]; exact Hb.
Qed.

Section Tests.
Variable R : realType.

Local Notation geometric_valid := (FreeOmegaSamples.geometric_valid R).

Example geometric_countable : oval_countably_supported (free_omega_domain geometric_valid).
Proof. exact: free_omega_domain_countable. Qed.

Example geometric_on_naturals :
  exists N : OmegaVal R nat,
    oval_mass N = oval_mass (free_omega_domain geometric_valid) /\
    oval_ae N (fun n => exists x, free_omega_enumerate geometric n = Some x) /\
    oval_eq (free_omega_domain geometric_valid)
      (oval_bind N (oval_decode R (free_omega_enumerate geometric))).
Proof. exact: free_omega_domain_countable_representation. Qed.

Example countable_cover_is_not_validity : ~ free_omega_admissible R alternating_bool.
Proof. exact: alternating_bool_not_admissible. Qed.

Example heterogeneous_dual_through_invalid :
  oval_bidual returns_true (free_omega_domain (constant_valid_by_quotient R))
    (free_omega_domain (@admissible_ret R bool true)).
Proof. apply free_omega_qlift_domain_bidual; exact heterogeneous_invalid_middle. Qed.

Example equality_joint_through_invalid :
  oval_joint eq (free_omega_domain (constant_valid_by_quotient R))
    (free_omega_domain (@admissible_ret R unit tt))
    (oval_bind (free_omega_domain (constant_valid_by_quotient R))
      (fun x => oval_ret R (x,x))).
Proof. apply free_omega_qlift_eq_joint; exact equality_through_invalid_middle. Qed.

Example zero_joint_empty_relation :
  oval_joint (fun (_ : bool) (_ : nat) => False)
    (oval_bottom R) (oval_bottom R) (oval_bottom R).
Proof. split; [by intros|split; by intros]. Qed.

Example nonzero_joint_empty_relation_impossible :
  ~ oval_coupled (fun (_ : bool) (_ : nat) => False) (oval_ret R true) (oval_ret R O).
Proof.
  intros [J HJ]; have H := proj1 (oval_joint_dual HJ).
  have Hbad := H (fun _ => 1) (fun _ => 0) (oval_test_one R) (oval_test_zero R)
    (fun x y Hfalse => False_rect _ Hfalse).
  change (is_true (1 <= (0 : R))) in Hbad; by rewrite ler10 in Hbad.
Qed.

Example unequal_mass_no_joint :
  ~ oval_coupled (fun (_ : unit) (_ : unit) => True) (oval_bottom R) (oval_ret R tt).
Proof.
  intros [J HJ]; have H := oval_bidual_mass (oval_joint_dual HJ).
  change (0 = (1 : R)) in H.
  have Hne : (1 : R) != 0 by apply oner_neq0.
  by rewrite -H eqxx in Hne.
Qed.
End Tests.

Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.FreeOmega Require Import Quotient Measure.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import
  Admissibility JointSoundness.
Fail Check PTree.Prob.Domain.MeasureModel.oval_probability.
Fail Check PTree.Core.PTreeDefinition.ptree.
Fail Check PTree.Eq.PEutt.peutt.
From PTree.Regression.Probability Require Import
  FreeOmegaDomain.
From PTree.Regression.Fixtures Require Import FreeOmegaSamples.

Section Tests.
Variable R : realType.

Example duplicate_invalid_codes_joint :
  oval_coupled (fun (_ : unit) b => b = true) (oval_ret R tt) (oval_ret R true).
Proof.
  apply (@oval_bidual_coupled_on_enumerations R unit bool (fun _ b => b = true)
    (oval_ret R tt) (oval_ret R true) repeated_unit repeated_bool).
  - intros f g Hf Hg Hfg; apply Hfg; exists 1%N; reflexivity.
  - intros f g Hf Hg Hfg; apply Hfg; exists 1%N; reflexivity.
  - split; intros f g Hf Hg Hfg; apply Hfg; reflexivity.
Qed.

(** The existing evidence really uses FOQLComp with alternating_bool as its
    invalid intermediate on another carrier. Only the final endpoints are valid. *)
Example heterogeneous_joint_through_invalid :
  oval_coupled returns_true (free_omega_domain (constant_valid_by_quotient R))
    (free_omega_domain (@admissible_ret R bool true)).
Proof. apply free_omega_qlift_sound; exact heterogeneous_invalid_middle. Qed.

Example invalid_middle_stays_invalid : ~ free_omega_admissible R alternating_bool.
Proof. exact: alternating_bool_not_admissible. Qed.

Example equality_joint_recovers_ds3 :
  oval_eq (free_omega_domain (constant_valid_by_quotient R))
    (free_omega_domain (@admissible_ret R unit tt)).
Proof. apply free_omega_qlift_eq_sound_via_joint; exact equality_through_invalid_middle. Qed.

Example empty_endpoint_qlift_joint :
  oval_coupled (fun (_ : Empty_set) (_ : bool) => False)
    (free_omega_domain (@admissible_zero R Empty_set))
    (free_omega_domain (@admissible_zero R bool)).
Proof. apply free_omega_qlift_sound; apply FOQLStructural, FOLZero. Qed.

Definition partial_bool : FreeOmega SubEnumQ bool :=
  FOSample domain_fair (fun b => if b then FORet true else FOZero).
Definition partial_nat : FreeOmega SubEnumQ nat :=
  FOSample domain_fair (fun b => if b then FORet 7%N else FOZero).
Lemma partial_bool_valid : free_omega_admissible R partial_bool.
Proof. apply admissible_sample; intros []; [apply admissible_ret|apply admissible_zero]. Qed.
Lemma partial_nat_valid : free_omega_admissible R partial_nat.
Proof. apply admissible_sample; intros []; [apply admissible_ret|apply admissible_zero]. Qed.
Lemma partial_heterogeneous_qlift :
  free_omega_qlift (fun b n => b = true /\ n = 7%N) partial_bool partial_nat.
Proof.
  apply FOQLStructural, FOLSample with (S := eq).
  - exact (@sem_lift_refl SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticMeasureCoreLaws bool eq domain_fair (fun b => @Logic.eq_refl bool b)).
  - intros b c ->; destruct c; [apply FOLRet; auto|apply FOLZero].
Qed.

Example partial_joint_keeps_mass_and_support :
  exists J, oval_joint (fun b n => b = true /\ n = 7%N)
    (free_omega_domain partial_bool_valid) (free_omega_domain partial_nat_valid) J /\
    oval_mass J = oval_mass (free_omega_domain partial_bool_valid) /\
    oval_mass J = oval_mass (free_omega_domain partial_nat_valid) /\
    oval_eval J (oval_indicator R (fun z => ~ (fst z = true /\ snd z = 7%N))) = 0.
Proof. apply free_omega_qlift_joint_mass_support; exact partial_heterogeneous_qlift. Qed.

Example geometric_quotient_joint :
  oval_coupled eq (free_omega_domain (geometric_valid R))
    (free_omega_domain (geometric_valid R)).
Proof. apply free_omega_qlift_sound, free_omega_qlift_refl; intro n; reflexivity. Qed.

(** Soundness does not turn a raw qlift derivation into endpoint validity. *)
Example qlift_alone_still_not_admissible :
  free_omega_qlift eq alternating_bool alternating_bool /\
  ~ free_omega_admissible R alternating_bool.
Proof.
  split; [apply free_omega_qlift_refl; intro b; reflexivity|exact: alternating_bool_not_admissible].
Qed.
End Tests.

Section LargeFreeOmegaCarriers.
Universe u v.
Variable R : realType.
Example type_valued_qlift_joint (A : Type@{u}) (B : Type@{v}) :
  oval_coupled (fun (_ : Type@{u}) (_ : Type@{v}) => True)
    (free_omega_domain (@admissible_ret R Type@{u} A))
    (free_omega_domain (@admissible_ret R Type@{v} B)).
Proof. apply free_omega_qlift_sound; apply FOQLStructural, FOLRet; exact I. Qed.
End LargeFreeOmegaCarriers.
