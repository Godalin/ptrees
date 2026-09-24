(** Finite, exact outcome laws for closed rational PTree execution.
    Lost and Timeout are explicit outcomes, not discarded probability.
    This specification is independent of entropy implementations and hitting. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq ssralg ssrnum order rat.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
From PTree.Prob.Backend.EnumQ Require Import Representation.
From PTree.Prob.Backend.SubEnumQ Require Import Representation.
From PTree.Execution Require Import Runner.
Import EnumQ GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Fixpoint outcome_distribution {A} (fuel : nat) (t : ptree void1 SubEnumQ A)
    : list (rat * outcome A) :=
  match observe t with
  | RetF a => [(1, Returned a)]
  | @VisF _ _ _ _ X e k => match e with end
  | TauF u => match fuel with
      | O => [(1, Timeout)] | S n => outcome_distribution n u end
  | @ProbF _ _ _ _ X mu k => match fuel with
      | O => [(1, Timeout)]
      | S n => finite_bind (subenumQ_data mu) (fun x => outcome_distribution n (k x)) ++
          [(1 - enumQ_mass (subenumQ_raw mu), Lost)]
      end
  end.

Definition outcome_expectation {A} n (t : ptree void1 SubEnumQ A) f :=
  finite_expect f (outcome_distribution n t).

Lemma outcome_distribution_nonnegative {A} n (t : ptree void1 SubEnumQ A) :
  finite_nonnegative (outcome_distribution n t).
Proof.
  induction n as [|n IH] in t |- *;
    destruct (observe t) as [a|u|X e k|X mu k] eqn:Ht;
    cbn [outcome_distribution]; rewrite Ht;
    try (destruct e).
  all: try (intros p x [H|[]]; inversion H; subst; exact: ler01).
  - exact: IH.
  - intros p x Hin. apply List.in_app_or in Hin. destruct Hin as [Hin|[H|[]]].
    + exact (finite_enum_nonnegative
        (finite_enum_bind (subenumQ_raw mu)
          (fun x => finite_enum_of_list (IH (k x)))) p x Hin).
    + inversion H; subst. rewrite subr_ge0. exact: subenumQ_bound.
Qed.

Lemma outcome_expectation_prob {A X} n (mu : SubEnumQ X)
    (k : X -> ptree void1 SubEnumQ A) f :
  outcome_expectation (S n) (Prob mu k) f =
    finite_expect (fun x => outcome_expectation n (k x) f) (subenumQ_data mu) +
    (1 - enumQ_mass (subenumQ_raw mu)) * f Lost.
Proof.
  rewrite /outcome_expectation /= finite_expect_app finite_expect_bind.
  by rewrite /= addr0.
Qed.

Theorem outcome_distribution_mass {A} n (t : ptree void1 SubEnumQ A) :
  outcome_expectation n t (fun _ => 1) = 1.
Proof.
  unfold outcome_expectation.
  induction n as [|n IH] in t |- *;
    destruct (observe t) as [a|u|X e k|X mu k] eqn:Ht;
    cbn [outcome_distribution]; rewrite Ht; cbn [finite_expect]; try (destruct e);
    try by rewrite mulr1 addr0.
  - exact: IH.
  - rewrite finite_expect_app finite_expect_bind /= mulr1 addr0.
    rewrite (finite_expect_ext _ (fun x => IH (k x))).
    change (enumQ_mass (subenumQ_raw mu) + (1 - enumQ_mass (subenumQ_raw mu)) = 1).
    by rewrite addrC subrK.
Qed.

Theorem outcome_distribution_no_entropy_failure {A} n (t : ptree void1 SubEnumQ A) :
  outcome_expectation n t (fun r => match r with EntropyExhausted => 1 | _ => 0 end) = 0.
Proof.
  unfold outcome_expectation.
  induction n as [|n IH] in t |- *;
    destruct (observe t) as [a|u|X e k|X mu k] eqn:Ht;
    cbn [outcome_distribution]; rewrite Ht; cbn [finite_expect]; try (destruct e);
    try by rewrite mulr0 add0r.
  - exact: IH.
  - rewrite finite_expect_app finite_expect_bind /= mulr0 !addr0.
    rewrite (finite_expect_ext _ (fun x => IH (k x))). exact: finite_expect_zero.
Qed.

Definition returned_test {A} (f : A -> rat) (r : outcome A) :=
  match r with Returned a => f a | _ => 0 end.
