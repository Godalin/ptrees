(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Arith Require Import PeanoNat.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From mathcomp.classical Require Import classical_sets.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.FrontierLift PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperExpectation PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperCoupling.

Require Import PTree.Prob.Backend.SubEnumQ.Expectation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ RatSubTypes GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** Numeric continuity needed for the quotient limit constructors.  The
    proofs use ordinary real suprema and the actual finite sample weights,
    not a quotient equality or an assumed semantic continuity capability. *)
Section ScalarSuprema.
Variable R : realType.
Local Notation upper := (@countable_upper R).

Lemma countable_upper_swap (grid : nat -> nat -> R) bound :
  (forall i j, grid i j <= bound) ->
  upper (fun i => upper (grid i)) = upper (fun j => upper (fun i => grid i j)).
Proof.
  intro Hb.
  have Hrows : forall i, upper (grid i) <= bound :=
    fun i => countable_upper_le (Hb i).
  have Hcols : forall j, upper (fun i => grid i j) <= bound :=
    fun j => countable_upper_le (fun i => Hb i j).
  apply/eqP. rewrite eq_le. apply/andP. split.
  - apply countable_upper_le. intro i. apply countable_upper_le. intro j.
    eapply le_trans.
    + exact (@countable_upper_ge R (fun k => grid k j) bound i (fun k => Hb k j)).
    + exact (@countable_upper_ge R (fun k => upper (fun i => grid i k)) bound j Hcols).
  - apply countable_upper_le. intro j. apply countable_upper_le. intro i.
    eapply le_trans.
    + exact (@countable_upper_ge R (grid i) bound j (Hb i)).
    + exact (@countable_upper_ge R (fun k => upper (grid k)) bound i Hrows).
Qed.
End ScalarSuprema.

Section UpperContinuity.
Variable R : realType.
Local Notation expect := (enumQ_real_expect (R := R)).
Local Notation upper := (free_omega_upper (R := R)).

(** Scott continuity in increasing unit-interval tests holds even when
    the raw term contains arbitrary (not necessarily increasing) FOLub
    nodes.  Supremum interchange is used only for suprema, not limits. *)
Theorem free_omega_upper_continuous {A} (mu : FreeOmega SubEnumQ A)
    (tests : nat -> A -> R) :
  (forall n x, 0 <= tests n x /\ tests n x <= 1) ->
  (forall n x, tests n x <= tests (S n) x) ->
  upper mu (fun x => countable_upper (fun n => tests n x)) =
  countable_upper (fun n => upper mu (tests n)).
Proof.
  intros Hb Hi. induction mu as [x| |X node k IH|chain IH]; cbn [free_omega_upper].
  - reflexivity.
  - symmetry. apply countable_upper_constant.
  - have Hrows : (fun x => upper (k x) (fun y => countable_upper (fun n => tests n y))) =
        (fun x => countable_upper (fun n => upper (k x) (tests n))).
    { apply functional_extensionality. exact IH. }
    rewrite Hrows. apply enumQ_real_expect_countable.
    + intros n x. exact (free_omega_upper_bounds (k x) (Hb n)).
    + intros n x. apply free_omega_upper_mono; [exact (Hb (S n))|exact (Hi n)].
  - have Hrows : (fun i => upper (chain i) (fun y => countable_upper (fun n => tests n y))) =
        (fun i => countable_upper (fun n => upper (chain i) (tests n))).
    { apply functional_extensionality. exact IH. }
    rewrite Hrows. apply countable_upper_swap with (bound := 1).
    intros i n. exact (proj2 (free_omega_upper_bounds (chain i) (Hb n))).
Qed.

Theorem free_omega_sample_lub_upper {A X} (mu : SubEnumQ X)
    (chain : X -> nat -> FreeOmega SubEnumQ A) (f : A -> R) :
  enumQ_ae (subenumQ_raw mu)
    (fun x => forall n, free_omega_approx eq (chain x n) (chain x (S n))) ->
  (forall x, 0 <= f x /\ f x <= 1) ->
  upper (FOSample mu (fun x => FOLub (chain x))) f =
  upper (FOLub (fun n => FOSample mu (fun x => chain x n))) f.
Proof.
  intros Hi Hf. cbn [free_omega_upper]. apply enumQ_real_expect_countable_ae.
  - intros n x. exact (free_omega_upper_bounds (chain x n) Hf).
  - intros p x Hpx Hnz n.
    apply free_omega_upper_approx_mono; [exact (Hi p x Hpx Hnz n)|exact Hf].
Qed.

(** Numeric validation of bind's two-chain diagonal.  Arbitrary formal
    Lub nodes may occur inside each source term; only the outer source
    chain and each kernel chain must increase, as required by FOQLBindLub. *)
Theorem free_omega_bind_lub_upper {A X}
    (source : nat -> FreeOmega SubEnumQ X)
    (kernels : X -> nat -> FreeOmega SubEnumQ A) (f : A -> R) :
  (forall n, free_omega_approx eq (source n) (source (S n))) ->
  (forall x n, free_omega_approx eq (kernels x n) (kernels x (S n))) ->
  (forall x, 0 <= f x /\ f x <= 1) ->
  upper (free_omega_bind (FOLub source) (fun x => FOLub (kernels x))) f =
  upper (FOLub (fun n => free_omega_bind (source n) (fun x => kernels x n))) f.
Proof.
  intros Hsource Hkernels Hf.
  have Hrow : forall i,
      upper (free_omega_bind (source i) (fun x => FOLub (kernels x))) f =
      upper (FOLub (fun n => free_omega_bind (source i) (fun x => kernels x n))) f.
  { intro i. rewrite free_omega_upper_bind. cbn [free_omega_upper].
    rewrite (free_omega_upper_continuous (source i)
      (tests := fun n x => upper (kernels x n) f)).
    - f_equal. apply functional_extensionality=> n. symmetry. apply free_omega_upper_bind.
    - intros n x. exact (free_omega_upper_bounds (kernels x n) Hf).
    - intros n x. exact (free_omega_upper_approx_mono (Hkernels x n) Hf). }
  change (countable_upper (fun i =>
      upper (free_omega_bind (source i) (fun x => FOLub (kernels x))) f) =
      upper (FOLub (fun n => free_omega_bind (source n) (fun x => kernels x n))) f).
  rewrite (functional_extensionality _ _ Hrow).
  change (upper (FOLub (fun i => FOLub
    (fun n => free_omega_bind (source i) (fun x => kernels x n)))) f =
    upper (FOLub (fun n => free_omega_bind (source n) (fun x => kernels x n))) f).
  apply free_omega_diagonal_upper; [| |exact Hf].
  - intros i n. eapply free_omega_approx_bind with (R := eq).
    + apply free_omega_approx_refl. intro x. reflexivity.
    + intros x y ->. exact (Hkernels y n).
  - intros i n. eapply free_omega_approx_bind with (R := eq).
    + exact (Hsource i).
    + intros x y ->. apply free_omega_approx_refl. intro z. reflexivity.
Qed.
End UpperContinuity.
