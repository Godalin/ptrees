From PTree.Prob.Backend.SubEnumQ Require Import NativeLimit.
From PTree.Prob.Backend.SubEnumQ Require Import Expectation.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Arith Require Import PeanoNat.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat ssralg ssrnum order rat reals interval.
From mathcomp.classical Require Import classical_sets.
Require Import PTree.Prob.Backend.Common.FiniteAtoms PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Bind PTree.Prob.Backend.EnumQ.Iteration PTree.Prob.Backend.EnumQ.Support PTree.Prob.Backend.EnumQ.SemanticCoupling.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperExpectation PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperCoupling PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperContinuity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ PTree.Prob.Backend.EnumQ.Map GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** Observation uses a native, eventwise rational limit.  The first part
    connects this existing limit notion to real-valued upper expectations;
    no numerical consistency axiom is added to the measure interface. *)
(** Native convergence facts now belong to SubEnumQ/NativeLimit. *)


(** Full scalar consistency of the existing observation judgment, including
    formal Lub observations.  This is a theorem about the actual native
    output, not a consistency premise supplied by clients. *)
Section ObservationConsistency.
Variable R : realType.
Local Notation expect := (enumQ_real_expect (R := R)).
Local Notation upper := (free_omega_upper (R := R)).

Theorem free_omega_observes_upper {A O} (obs : A -> O)
    (mu : FreeOmega SubEnumQ A) (out : SubEnumQ O) :
  @free_omega_observes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    A O obs mu out ->
  forall f : O -> R, (forall y, 0 <= f y /\ f y <= 1) ->
    upper mu (fun x => f (obs x)) = expect f (subenumQ_raw out).
Proof.
  intro Hobs. induction Hobs as [x| |X node k front Hobs IH|chain outs out Hobs IH Hlim Hinc];
    intros f Hf.
  - change (f (obs x) = ratr (1 : rat) * f (obs x) + 0).
    by rewrite rmorph1 mul1r addr0.
  - reflexivity.
  - change (expect (fun x => upper (k x) (fun y => f (obs y))) (subenumQ_raw node) =
      expect f (bind_EnumQ (subenumQ_raw node) (fun x => subenumQ_raw (front x)))).
    rewrite enumQ_real_expect_bind. f_equal. apply functional_extensionality=> x.
    exact (IH x f Hf).
  - cbn [free_omega_upper].
    have Hrows : (fun n => upper (chain n) (fun x => f (obs x))) =
      (fun n => expect f (subenumQ_raw (outs n))).
    { apply functional_extensionality=> n. exact (IH n f Hf). }
    rewrite Hrows. apply enumQ_monotone_converges_upper; [|exact Hlim|].
    + intros P n m Hnm.
      have HP : forall y, 0 <= (if P y then (1 : R) else 0) /\
          (if P y then (1 : R) else 0) <= 1.
      { intro y. destruct (P y); split; try exact: ler01; exact: lexx. }
      have Hstep : forall i,
          expect (fun y => if P y then 1 else 0) (subenumQ_raw (outs i)) <=
          expect (fun y => if P y then 1 else 0) (subenumQ_raw (outs (S i))).
      { intro i. rewrite -(IH i _ HP) -(IH (S i) _ HP).
        apply free_omega_upper_approx_mono; [exact (Hinc i)|].
        intro x. exact (HP (obs x)). }
      have Hreal := scalar_increasing_le Hstep Hnm.
      rewrite !enumQ_real_expect_indicator ler_rat in Hreal. exact Hreal.
    + intro y. exact (proj1 (Hf y)).
Qed.

Theorem free_omega_denotes_upper {A O} (obs : A -> O)
    (mu : FreeOmega SubEnumQ A) (out : SubEnumQ O) (f : O -> R) :
  @free_omega_denotes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    A O obs mu out ->
  (forall y, 0 <= f y /\ f y <= 1) ->
  upper mu (fun x => f (obs x)) = expect f (subenumQ_raw out).
Proof.
  intros [represented [Hobs Heq]] Hf.
  rewrite (free_omega_observes_upper Hobs Hf).
  apply/eqP. rewrite eq_le. apply/andP. split.
  - eapply subenumQ_lift_real_expect; [exact Heq|]. intros x y ->. exact: lexx.
  - eapply subenumQ_lift_real_expect; [apply sem_lift_sym; exact Heq|].
    intros x y ->. exact: lexx.
Qed.
End ObservationConsistency.
