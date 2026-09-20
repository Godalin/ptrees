Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From PTree.Prob Require Import DiscreteMC MeasureIterationEnum TwoLevelMeasure TwoLevelMeasureSubEnum
  FreeOmegaMeasure FreeOmegaUpperExpectationSubEnum FreeOmegaUpperCouplingSubEnum.
From PTree.Regression.Backend Require Import SubEnumRegression FreeOmegaEscapingMass.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section ScalarAudit.
Variable R : realType.
Local Notation upper := (free_omega_upper (R := R)).

Lemma upper_big_mass : upper EscapingMass.big (fun _ => 1) = 1.
Proof.
  change (enum_real_expect (R := R) (fun _ : bool => 1) (subenum_raw subenum_fair) = 1).
  rewrite enum_real_expect_one.
  have Hmass : enum_mass (subenum_raw subenum_fair) = 1 by vm_compute; reflexivity.
  by rewrite Hmass rmorph1.
Qed.

Lemma upper_small_mass : upper EscapingMass.small (fun _ => 1) = 1 / 2.
Proof.
  change (enum_real_expect (R := R) (fun b : bool => if b then 1 else 0)
    (subenum_raw subenum_fair) = 1 / 2).
  rewrite (_ : (fun b : bool => if b then (1 : R) else 0) =
    (fun b : bool => ratr (if b then (1 : rat) else 0)));
    last by apply functional_extensionality; intros []; cbn; rewrite ?rmorph1 ?rmorph0.
  rewrite enum_real_expect_rat.
  have Hmass : enum_expect (fun b : bool => if b then (1 : rat) else 0)
      (subenum_raw subenum_fair) = 1 / 2 by vm_compute; reflexivity.
  by rewrite Hmass fmorph_div ?rmorphD ?rmorph1 ?ratr_nat.
Qed.

(** The old decreasing row is assigned its supremum (mass one), not its
    eventual value (mass one half).  This model therefore distinguishes
    the exact native endpoints of the previous mass-collapse audit. *)
Lemma upper_escaped_row_mass n :
  upper (FOLub (fun x => EscapingMass.kernel x n)) (fun _ => 1) = 1.
Proof.
  have Hone : forall _ : unit, 0 <= (1 : R) /\ (1 : R) <= 1.
  { intro x. split; [exact: ler01|exact: lexx]. }
  apply/eqP. rewrite eq_le. apply/andP. split.
  - exact (proj2 (free_omega_upper_bounds _ Hone)).
  - rewrite -{1}upper_big_mass.
    change (upper (EscapingMass.kernel 0%nat n) (fun _ => 1) <=
      countable_upper (fun x => upper (EscapingMass.kernel x n) (fun _ => 1))).
    exact (@countable_upper_ge R
      (fun x => upper (EscapingMass.kernel x n) (fun _ => 1)) 1 0%nat
      (fun x => proj2 (free_omega_upper_bounds (EscapingMass.kernel x n) Hone))).
Qed.

Theorem upper_separates_big_small :
  upper EscapingMass.big (fun _ => 1) <> upper EscapingMass.small (fun _ => 1).
Proof.
  rewrite upper_big_mass upper_small_mass.
  have Hhalf : (1 / 2 : R) < 1 by rewrite div1r invf_lt1 // ltr1n.
  move=> Hbad. rewrite -Hbad ltxx in Hhalf. discriminate.
Qed.

(** Arbitrary formal Lub syntax is not silently promoted to a measure.
    Both singleton tests below have upper value one, although their sum
    is the constant-one test. *)
Definition raw_choice : FreeOmega SubEnum bool :=
  FOLub (fun n => FORet (match n with O => true | S _ => false end)).

Lemma upper_raw_choice_test (f : bool -> R) witness :
  (forall b, 0 <= f b /\ f b <= 1) -> f witness = 1 ->
  upper raw_choice f = 1.
Proof.
  intros Hf Hw. apply/eqP. rewrite eq_le. apply/andP. split.
  - exact (proj2 (free_omega_upper_bounds (R := R) raw_choice Hf)).
  - rewrite -Hw. unfold raw_choice. cbn [free_omega_upper].
    destruct witness.
    + exact (@countable_upper_ge R
        (fun n => f (match n with O => true | S _ => false end)) 1 0%nat
        (fun n => proj2 (Hf (match n with O => true | S _ => false end)))).
    + exact (@countable_upper_ge R
        (fun n => f (match n with O => true | S _ => false end)) 1 1%nat
        (fun n => proj2 (Hf (match n with O => true | S _ => false end)))).
Qed.

Theorem raw_upper_is_not_additive :
  upper raw_choice (fun _ => 1) <
  upper raw_choice (fun b => if b then 1 else 0) +
  upper raw_choice (fun b => if b then 0 else 1).
Proof.
  have H1 : upper raw_choice (fun _ => 1) = 1.
  { apply (@upper_raw_choice_test (fun _ => 1) true); [|reflexivity].
    intros []. all: split; [exact: ler01|exact: lexx]. }
  have Htrue : upper raw_choice (fun b => if b then 1 else 0) = 1.
  { apply (@upper_raw_choice_test (fun b => if b then 1 else 0) true); [|reflexivity].
    intros []; split; try exact: ler01; exact: lexx. }
  have Hfalse : upper raw_choice (fun b => if b then 0 else 1) = 1.
  { apply (@upper_raw_choice_test (fun b => if b then 0 else 1) false); [|reflexivity].
    intros []; split; try exact: ler01; exact: lexx. }
  rewrite H1 Htrue Hfalse. change ((1%:R : R) < 2%:R).
  by rewrite ltr_nat.
Qed.

(** Splitting a weight changes the enumeration, not any real-valued test.
    The proof uses the actual native coupling, not literal list equality. *)
Theorem upper_split_mass_real_test (f : bool -> R) :
  enum_real_expect f (subenum_raw subenum_fair) =
  enum_real_expect f (subenum_raw subenum_fair_split).
Proof.
  apply/eqP. rewrite eq_le. apply/andP. split.
  - eapply subenum_lift_real_expect; [exact subenum_fair_split_lift|].
    intros x y ->. exact: lexx.
  - eapply subenum_lift_real_expect; [apply sem_lift_sym; exact subenum_fair_split_lift|].
    intros x y ->. exact: lexx.
Qed.

Theorem upper_unreachable_test_change :
  upper (FOSample (subenum_ret true) (fun b : bool => FORet b)) (fun _ => 1) =
  upper (FOSample (subenum_ret true) (fun b : bool => FORet b))
    (fun b => if b then 1 else 0).
Proof.
  apply free_omega_upper_ae_ext.
  - intro b. split; [exact: ler01|exact: lexx].
  - intros []; split; try exact: ler01; exact: lexx.
  - apply FOAESample with (Good := fun b => b = true).
    + apply (@sem_ae_ret SubEnum SubEnum_SemanticMeasure
        SubEnum_SemanticMeasureAEKleisliLaws bool (fun b => b = true) true).
      reflexivity.
    + intros b ->. apply FOAERet. reflexivity.
Qed.

Definition padded_grid (i j : nat) : FreeOmega SubEnum bool :=
  match i, j with
  | S _, S _ => FOSample subenum_fair (fun b => FORet b)
  | _, _ => FOZero
  end.

Theorem upper_padded_double_limit (f : bool -> R)
    (Hf : forall b, 0 <= f b /\ f b <= 1) :
  upper (FOLub (fun i => FOLub (padded_grid i))) f =
  enum_real_expect f (subenum_raw subenum_fair).
Proof.
  rewrite (@free_omega_diagonal_upper R _ padded_grid f).
  - change (upper (FOLub (fun n => padded_grid n n)) f =
      upper (FOSample subenum_fair (fun b => FORet b)) f).
    rewrite -(@countable_upper_constant R
      (upper (FOSample subenum_fair (fun b => FORet b)) f)).
    change (upper (FOLub (fun n => padded_grid n n)) f =
      upper (FOLub (fun _ => FOSample subenum_fair (fun b => FORet b))) f).
    apply free_omega_cofinal_upper_eq; [split|exact Hf].
    + intros [|n]; exists 0%nat; cbn [padded_grid].
      * apply FOApproxZero.
      * apply free_omega_approx_refl. intro b. reflexivity.
    + intro n. exists 1%nat. apply free_omega_approx_refl. intro b. reflexivity.
  - intros [|i] [|j]; cbn [padded_grid]; try apply FOApproxZero.
    apply free_omega_approx_refl. intro b. reflexivity.
  - intros [|i] [|j]; cbn [padded_grid]; try apply FOApproxZero.
    apply free_omega_approx_refl. intro b. reflexivity.
  - exact Hf.
Qed.
End ScalarAudit.
