(** One-way validation: the finite runner's returned distribution is exactly
    the same-fuel mathematical hitting approximant. Limits reuse DS4.
    Execution and maintained PTree reasoning never import this adapter. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
From PTree.Prob.Backend.EnumQ Require Import Representation.
From PTree.Prob.Backend.SubEnumQ Require Import Representation Expectation.
From PTree.Prob.Domain Require Import Expectation.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Eq.Backend Require Import StableHittingDomainSubEnumQ.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure Measure.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import Admissibility.
From PTree.Execution Require Import Runner.
From PTree.Execution.Backend Require Import FiniteDistribution UniformReplay.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Section Validation.
Variable R : realType.
Context {A : Type}.

Definition return_head_test (f : A -> rat) (h : stable_head void1 SubEnumQ A) : R :=
  match h with FHRet a => ratr (f a) | FHVis _ e k => match e with end end.

Theorem finite_runner_hitting n (t : ptree void1 SubEnumQ A) (f : A -> rat) :
  ratr (outcome_expectation n t (returned_test f)) =
  oval_eval (ptree_domain_approx R n (observe t)) (return_head_test f).
Proof.
  induction n as [|n IH] in t |- *;
    unfold outcome_expectation;
    destruct (observe t) as [a|u|X e k|X mu k] eqn:Ht;
    cbn [outcome_distribution]; rewrite Ht; try (destruct e).
  - rewrite ptree_domain_approx_ret /= mul1r addr0. reflexivity.
  - rewrite ptree_domain_approx_tau_zero /= mulr0 addr0 rmorph0. reflexivity.
  - rewrite ptree_domain_approx_prob_zero /= mulr0 addr0 rmorph0. reflexivity.
  - rewrite ptree_domain_approx_ret /= mul1r addr0. reflexivity.
  - rewrite ptree_domain_approx_tau_succ. exact: IH.
  - rewrite ptree_domain_approx_prob_succ finite_expect_app finite_expect_bind.
    rewrite /= mulr0 !addr0.
    rewrite -enumQ_real_expect_rat.
    apply finite_expect_ext=> x. exact: IH.
Qed.

Theorem replay_hitting source (Hsource : uniform_entropy source)
    n (t : ptree void1 SubEnumQ A) history f :
  ratr (replay_expectation source n t history (returned_test f)) =
  oval_eval (ptree_domain_approx R n (observe t)) (return_head_test f).
Proof. rewrite (finite_runner_distribution Hsource). exact: finite_runner_hitting. Qed.

Theorem replay_hitting_limit source (Hsource : uniform_entropy source)
    (t : ptree void1 SubEnumQ A) history f :
  oval_eval (ptree_domain_hitting R (observe t)) (return_head_test f) =
  oval_sup (fun n => ratr (replay_expectation source n t history (returned_test f))).
Proof.
  change (oval_sup (fun n => oval_eval (ptree_domain_approx R n (observe t))
      (return_head_test f)) =
    oval_sup (fun n => ratr (replay_expectation source n t history (returned_test f)))).
  apply oval_sup_ext=> n. symmetry. exact: replay_hitting.
Qed.

Lemma return_head_test_bounded f :
  (forall a, 0 <= f a <= 1) -> oval_test (return_head_test f).
Proof.
  intros H [a|X e k]; [|destruct e].
  change ((0 : R) <= ratr (f a) /\ (ratr (f a) : R) <= 1).
  have /andP [Hlo Hhi] := H a. split.
  - rewrite -(rmorph0 (ratr : {rmorphism rat -> R})) ler_rat. exact Hlo.
  - rewrite -(rmorph1 (ratr : {rmorphism rat -> R})) ler_rat. exact Hhi.
Qed.

Local Notation FI := (@FreeOmegaObservableSemanticMeasure SubEnumQ
  SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).
Local Notation FO := (@FreeOmegaObservableSemanticOmega SubEnumQ
  SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).

(** Any complete hitting witness, not merely our chosen representative.
    Rational bounded tests include indicators of arbitrary decidable events. *)
Theorem runner_stable_hitting_adequacy source (Hsource : uniform_entropy source)
    (t : ptree void1 SubEnumQ A) history out
    (Hhit : @PTreeKernel.ptree_stable_hitting void1 SubEnumQ (FreeOmega SubEnumQ)
      FI FreeOmegaMixedMeasure FO A (observe t) out)
    f (Hf : forall a, 0 <= f a <= 1) :
  oval_eval (free_omega_domain (stable_hitting_admissible R Hhit)) (return_head_test f) =
  oval_sup (fun n => ratr (replay_expectation source n t history (returned_test f))).
Proof.
  transitivity (oval_eval (ptree_domain_hitting R (observe t)) (return_head_test f)).
  - exact (stable_hitting_denotational_adequacy Hhit (return_head_test_bounded Hf)).
  - exact: replay_hitting_limit.
Qed.
End Validation.
