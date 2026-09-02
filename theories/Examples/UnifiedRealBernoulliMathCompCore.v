Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From mathcomp Require Import ssreflect ssrbool ssralg ssrnum reals.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import FrontierLift MathCompMeasure FreeOmegaMeasure
  MeasureIteration TwoLevelMeasure TwoLevelMeasureMathComp.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Examples Require Import RealBernoulliOracle RealBernoulliMathComp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section UnifiedRealOracle.
Context (R : realType).

Local Notation MN := (MathCompKernelMeasure R).
Local Notation MF := (MathCompBehaviorMeasure R).

Local Opaque mathcomp_oracle_transition.

Definition unified_mathcomp_oracle_approx (Anchor : Type)
    (qbit : binary_oracle) (fuel n : nat) :
    FreeOmegaAt MN Anchor bool :=
  @mixed_iter_approx MN (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R))
    nat bool fuel (mathcomp_oracle_transition R qbit) n.

Definition unified_mathcomp_oracle_out (Anchor : Type)
    (qbit : binary_oracle) : FreeOmegaAt MN Anchor bool :=
  FOLub (fun fuel => unified_mathcomp_oracle_approx Anchor qbit fuel 0).

(** Analytic support adequacy of the MathComp oracle limit.  Equality of
    limiting probabilities alone does not expose this high-universe fact;
    concrete real-measure backends discharge it from monotonicity and
    null-set reflection.  Keeping it as a named law prevents observation
    couplings from silently assuming that theorem. *)
Class MathCompOracleSupportLaws := {
  mathcomp_oracle_support : forall (Anchor : Type)
      (qbit : binary_oracle) (q : R),
    (0 <= q <= 1)%R -> mathcomp_oracle_represents qbit q ->
    @free_omega_support_lift MN (MathCompNodeSemanticMeasureInterface R)
      bool bool eq (unified_mathcomp_oracle_out Anchor qbit)
      (FOSample (mathcomp_bernoulli q) (fun b => FORet b))
}.

Lemma unified_mathcomp_oracle_step_frontier qbit n :
  @frontier real_mathcomp_coinE MN MF
    (MathCompNodeSemanticMeasureInterface R)
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R))
    (nat + bool) (observe (mathcomp_oracle_step R qbit n))
    (mixed_bind (mathcomp_oracle_transition R qbit n)
      (fun next => sem_ret (FHRet next))).
Proof.
  unfold mathcomp_oracle_step. cbn.
  rewrite -free_omega_mixed_bindE.
  apply (@UFProb real_mathcomp_coinE MN MF
    (MathCompNodeSemanticMeasureInterface R)
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R))
    (nat + bool) (nat + bool)
    (mathcomp_oracle_transition R qbit n) (fun next => Ret next)
    (fun next => FORet (FHRet next)) (fun _ => True)).
  - exact: mathcomp_kernel_ae_true.
  - intros next _. rewrite -free_omega_observable_sem_retE. apply UFRet.
Qed.

Lemma unified_mathcomp_oracle_approx_observes (Anchor : Type)
    qbit fuel n :
  @free_omega_observes MN
    (MathCompNodeSemanticMeasureInterface R)
    (MathCompNodeSemanticOmegaInterface R)
    bool bool id
    (unified_mathcomp_oracle_approx Anchor qbit fuel n)
    (mathcomp_oracle_result_approx R qbit fuel n).
Proof.
  induction fuel as [|fuel IH] in n |- *.
  - constructor.
  - unfold unified_mathcomp_oracle_approx,
      mathcomp_oracle_result_approx in *.
    cbn [mixed_iter_approx meas_iter_approx].
    rewrite free_omega_mixed_bindE.
    rewrite mathcomp_legacy_bind_semE.
    apply FOOObserveSample with
      (front := fun next =>
        match next with
        | inl n' => meas_iter_approx fuel
            (mathcomp_oracle_transition R qbit) n'
        | inr b => meas_ret b
        end).
    intros [n'|b].
    + exact (IH n').
    + rewrite mathcomp_legacy_ret_semE. constructor.
Qed.

Lemma unified_mathcomp_oracle_mixed_iter (Anchor : Type) qbit :
  @mixed_iter MN (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R))
    nat bool (mathcomp_oracle_transition R qbit) 0
    (unified_mathcomp_oracle_out Anchor qbit).
Proof.
  unfold mixed_iter, unified_mathcomp_oracle_out. cbn.
  apply FOQLStructural.
  apply FOLLub. intro n.
  change (free_omega_lift eq
    (mixed_iter_approx n (mathcomp_oracle_transition R qbit) 0)
    (mixed_iter_approx n (mathcomp_oracle_transition R qbit) 0)).
  induction (mixed_iter_approx n (mathcomp_oracle_transition R qbit) 0);
    cbn.
  - constructor. reflexivity.
  - constructor.
  - eapply FOLSample.
    + apply mathcomp_kernel_lift_refl. intros x. reflexivity.
    + intros x y ->. apply H.
  - apply FOLLub. exact H.
Qed.

End UnifiedRealOracle.
