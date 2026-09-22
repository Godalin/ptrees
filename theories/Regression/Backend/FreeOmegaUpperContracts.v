(** Thematic raw-upper, continuity, observation and quotient contracts. *)
Set Warnings "-notation-overridden,-ambiguous-paths".

From PTree.Prob.Backend.SubEnumQ Require Import Expectation.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperExpectation PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperCoupling.
From PTree.Regression.Backend Require Import SubEnumQRegression FreeOmegaEscapingMass.
Import EnumQ.
Module ExpectationTests.
(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

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
  change (enumQ_real_expect (R := R) (fun _ : bool => 1) (subenumQ_raw subenumQ_fair) = 1).
  rewrite enumQ_real_expect_one.
  have Hmass : enumQ_mass (subenumQ_raw subenumQ_fair) = 1 by vm_compute; reflexivity.
  by rewrite Hmass rmorph1.
Qed.

Lemma upper_small_mass : upper EscapingMass.small (fun _ => 1) = 1 / 2.
Proof.
  change (enumQ_real_expect (R := R) (fun b : bool => if b then 1 else 0)
    (subenumQ_raw subenumQ_fair) = 1 / 2).
  rewrite (_ : (fun b : bool => if b then (1 : R) else 0) =
    (fun b : bool => ratr (if b then (1 : rat) else 0)));
    last by apply functional_extensionality; intros []; cbn; rewrite ?rmorph1 ?rmorph0.
  rewrite enumQ_real_expect_rat.
  have Hmass : enumQ_expect (fun b : bool => if b then (1 : rat) else 0)
      (subenumQ_raw subenumQ_fair) = 1 / 2 by vm_compute; reflexivity.
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
Definition raw_choice : FreeOmega SubEnumQ bool :=
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
  enumQ_real_expect f (subenumQ_raw subenumQ_fair) =
  enumQ_real_expect f (subenumQ_raw subenumQ_fair_split).
Proof.
  apply/eqP. rewrite eq_le. apply/andP. split.
  - eapply subenumQ_lift_real_expect; [exact subenumQ_fair_split_lift|].
    intros x y ->. exact: lexx.
  - eapply subenumQ_lift_real_expect; [apply sem_lift_sym; exact subenumQ_fair_split_lift|].
    intros x y ->. exact: lexx.
Qed.

Theorem upper_unreachable_test_change :
  upper (FOSample (subenumQ_ret true) (fun b : bool => FORet b)) (fun _ => 1) =
  upper (FOSample (subenumQ_ret true) (fun b : bool => FORet b))
    (fun b => if b then 1 else 0).
Proof.
  apply free_omega_upper_ae_ext.
  - intro b. split; [exact: ler01|exact: lexx].
  - intros []; split; try exact: ler01; exact: lexx.
  - apply FOAESample with (Good := fun b => b = true).
    + apply (@sem_ae_ret SubEnumQ SubEnumQ_SemanticMeasure
        SubEnumQ_SemanticMeasureAEKleisliLaws bool (fun b => b = true) true).
      reflexivity.
    + intros b ->. apply FOAERet. reflexivity.
Qed.

Definition padded_grid (i j : nat) : FreeOmega SubEnumQ bool :=
  match i, j with
  | S _, S _ => FOSample subenumQ_fair (fun b => FORet b)
  | _, _ => FOZero
  end.

Theorem upper_padded_double_limit (f : bool -> R)
    (Hf : forall b, 0 <= f b /\ f b <= 1) :
  upper (FOLub (fun i => FOLub (padded_grid i))) f =
  enumQ_real_expect f (subenumQ_raw subenumQ_fair).
Proof.
  rewrite (@free_omega_diagonal_upper R _ padded_grid f).
  - change (upper (FOLub (fun n => padded_grid n n)) f =
      upper (FOSample subenumQ_fair (fun b => FORet b)) f).
    rewrite -(@countable_upper_constant R
      (upper (FOSample subenumQ_fair (fun b => FORet b)) f)).
    change (upper (FOLub (fun n => padded_grid n n)) f =
      upper (FOLub (fun _ => FOSample subenumQ_fair (fun b => FORet b))) f).
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

End ExpectationTests.

From PTree.Prob.Backend.SubEnumQ Require Import Expectation.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.FrontierLift PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperExpectation PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperContinuity.
From PTree.Regression.Backend Require Import FreeOmegaEscapingMass.
Module ContinuityTests.
(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** A syntactically present, zero-weight branch deliberately decreases.
    The numeric sample/limit law must need monotonicity only almost
    everywhere, not on all syntactic samples. *)
Definition null_branch_node : SubEnumQ bool.
Proof.
  refine (subenumQ_of_list (mu := (1,true) :: (0,false) :: nil) _ _).
  - intros p x [H|[H|[]]]; inversion H; subst; vm_compute; reflexivity.
  - vm_compute. reflexivity.
Defined.

Definition null_branch_chain (b : bool) (n : nat) : FreeOmega SubEnumQ bool :=
  if b then FORet true else match n with O => FORet false | S _ => FOZero end.

Lemma null_branch_chain_ae_increasing :
  enumQ_ae (subenumQ_raw null_branch_node)
    (fun b => forall n, free_omega_approx eq
      (null_branch_chain b n) (null_branch_chain b (S n))).
Proof.
  intros p b Hin Hnz n. destruct Hin as [H|[H|H]]; [| |contradiction].
  - inversion H. subst. apply free_omega_approx_refl. intro x. reflexivity.
  - inversion H. subst. exfalso. apply Hnz. apply val_inj. reflexivity.
Qed.

Lemma null_branch_chain_not_everywhere_increasing :
  ~ (forall b n, free_omega_approx eq
    (null_branch_chain b n) (null_branch_chain b (S n))).
Proof.
  intro H. specialize (H false 0%nat).
  cbn [null_branch_chain] in H. inversion H.
Qed.

Section ScalarContinuityRegression.
Variable R : realType.
Local Notation upper := (free_omega_upper (R := R)).

Theorem null_branch_sample_limit (f : bool -> R)
    (Hf : forall b, 0 <= f b /\ f b <= 1) :
  upper (FOSample null_branch_node (fun b => FOLub (null_branch_chain b))) f =
  upper (FOLub (fun n => FOSample null_branch_node (fun b => null_branch_chain b n))) f.
Proof.
  apply free_omega_sample_lub_upper; [exact null_branch_chain_ae_increasing|exact Hf].
Qed.

Theorem null_branch_sample_mass :
  upper (FOSample null_branch_node (fun b => FOLub (null_branch_chain b))) (fun _ => 1) = 1.
Proof.
  change ((ratr (1 : rat) : R) * countable_upper (fun _ => (1 : R)) +
    ((ratr (0 : rat) : R) * countable_upper (fun n => upper (null_branch_chain false n) (fun _ => 1)) + 0) = 1).
  rewrite rmorph1 rmorph0 mul1r mul0r !addr0.
  apply countable_upper_constant.
Qed.

(** The bind theorem allows malformed formal Lub nodes INSIDE each
    source term.  It requires exactly increasing outer source/kernel
    chains; no hidden totality, AST or hereditary well-formedness premise
    rules out the escaping source from the previous safety audit. *)
Theorem escaping_source_bind_limit (f : unit -> R)
    (Hf : forall x, 0 <= f x /\ f x <= 1) :
  upper (free_omega_bind (FOLub (fun _ => EscapingMass.escaping))
    (fun x => FOLub (EscapingMass.kernel x))) f =
  upper (FOLub (fun n => free_omega_bind EscapingMass.escaping
    (fun x => EscapingMass.kernel x n))) f.
Proof.
  apply free_omega_bind_lub_upper.
  - intro n. apply free_omega_approx_refl. intro x. reflexivity.
  - exact EscapingMass.kernel_increasing.
  - exact Hf.
Qed.
End ScalarContinuityRegression.

End ContinuityTests.

From PTree.Prob.Backend.SubEnumQ Require Import Expectation.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperExpectation PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperObservation.
From PTree.Examples Require Import RandomWalk.
From PTree.Regression.Backend Require Import FreeOmegaEscapingMass.
Module ObservationTests.
(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Import ExpectationTests.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section ObservationModelRegression.
Variable R : realType.
Local Notation upper := (free_omega_upper (R := R)).

Lemma unit_test_bounded : forall _ : unit, 0 <= (1 : R) /\ (1 : R) <= 1.
Proof. intro x. split; [exact: ler01|exact: lexx]. Qed.

(** The actual unbounded, infinite-state RandomWalk example, with its
    high-universe stable-head carrier, has numeric mass one.  This uses
    the direct hitting observation, not unproved quotient invariance. *)
Theorem random_walk_limit_upper_mass x y : upper (walk_limit x y) (fun _ => 1) = 1.
Proof.
  rewrite (free_omega_observes_upper (walk_limit_observes_unit x y)
    (f := fun _ : unit => (1 : R)) unit_test_bounded).
  change (ratr (1 : rat) * (1 : R) + 0 = 1).
  by rewrite rmorph1 mul1r addr0.
Qed.

Theorem increasing_kernel_observation_upper_mass x :
  upper (FOLub (EscapingMass.kernel x)) (fun _ => 1) = 1.
Proof.
  rewrite (free_omega_observes_upper (EscapingMass.increasing_kernel_observable x)
    (f := fun _ : unit => (1 : R)) unit_test_bounded).
  by rewrite enumQ_real_expect_one EscapingMass.big_mass_one rmorph1.
Qed.

(** A second, NUMERIC rejection of the former escaping-mass observation.
    It deliberately does not use inversion of FOOObserveLub or the earlier
    escaped_row_not_observable theorem. *)
Theorem escaped_row_wrong_mass_rejected_numerically n :
  ~ @free_omega_observes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    unit unit (fun x => x) (FOLub (fun x => EscapingMass.kernel x n))
    EscapingMass.small_out.
Proof.
  intro Hobs.
  have Hnumeric := free_omega_observes_upper Hobs
    (f := fun _ : unit => (1 : R)) unit_test_bounded.
  rewrite upper_escaped_row_mass enumQ_real_expect_one
    EscapingMass.small_mass_half ?fmorph_div ?rmorphD ?rmorph1 ?ratr_nat in Hnumeric.
  apply (upper_separates_big_small (R := R)).
  rewrite upper_big_mass upper_small_mass. exact Hnumeric.
Qed.
End ObservationModelRegression.

End ObservationTests.

From PTree.Prob.Backend.SubEnumQ Require Import Expectation.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperExpectation PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperRelational PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperQuotient.
From PTree.Regression.Backend Require Import SubEnumQRegression FreeOmegaEscapingMass.
From PTree.Examples Require Import RandomWalk.
Module QuotientTests.
(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Import ExpectationTests ObservationTests.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section QuotientModelRegression.
Variable R : realType.
Local Notation upper := (free_omega_upper (R := R)).

(** Same support does not hide missing mass, even under a universal
    result relation and arbitrary combinations of quotient rules. *)
Theorem quotient_big_small_separated (T : unit -> unit -> Prop) :
  ~ @free_omega_qlift SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    unit unit T EscapingMass.big EscapingMass.small.
Proof.
  intro H. apply (upper_separates_big_small (R := R)).
  exact (free_omega_qlift_upper_mass R H).
Qed.

Theorem quotient_escaped_row_separated n :
  ~ @free_omega_qlift SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    unit unit eq (FOLub (fun x => EscapingMass.kernel x n)) EscapingMass.small.
Proof.
  intro H. have Hmass := free_omega_qlift_upper_mass R H.
  apply (upper_separates_big_small (R := R)).
  rewrite upper_escaped_row_mass in Hmass. by rewrite upper_big_mass.
Qed.

(** Equal total mass is not enough either: a non-increasing formal Lub
    cannot become a fair distribution by quotient reasoning. *)
Theorem quotient_raw_choice_not_fair :
  ~ @free_omega_qlift SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    bool bool eq raw_choice (FOSample subenumQ_fair (fun b => FORet b)).
Proof.
  intro H.
  have Hf : bounded_test (fun b : bool => if b then (1 : R) else 0).
  { intros []; split; try exact: ler01; exact: lexx. }
  have Heq := free_omega_qlift_eq_upper H Hf.
  have Hleft : upper raw_choice (fun b : bool => if b then 1 else 0) = 1.
  { apply (@upper_raw_choice_test R (fun b : bool => if b then 1 else 0) true);
      [exact Hf|reflexivity]. }
  change (upper raw_choice (fun b : bool => if b then 1 else 0) =
    upper EscapingMass.small (fun _ => 1)) in Heq.
  apply (upper_separates_big_small (R := R)).
  rewrite Hleft in Heq. rewrite upper_big_mass. exact Heq.
Qed.

(** Real unbounded behavior with a high-universe result carrier remains
    covered after quotient rewrites; no finite-support limit is assumed. *)
Theorem rewritten_random_walk_upper_mass x y mu :
  @free_omega_qlift SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    _ _ eq mu (walk_limit x y) -> upper mu (fun _ => 1) = 1.
Proof.
  intro H. rewrite (free_omega_qlift_upper_mass R H).
  apply random_walk_limit_upper_mass.
Qed.
End QuotientModelRegression.

End QuotientTests.
