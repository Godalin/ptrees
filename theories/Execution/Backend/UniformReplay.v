(** History-dependent ideal entropy laws, and their actual replay execution.
    No claim is made that a deterministic PRNG satisfies conditional uniformity.
    Histories are reversed lists of previously supplied ticket indices. *)
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
From PTree.Execution.Backend Require Import RationalTickets FiniteDistribution.
Import EnumQ GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Definition uniform_indices (d : nat) : list (rat * nat) :=
  List.map (fun i => (d%:R^-1, i)) (iota 0 d).

Lemma uniform_indices_expect d f :
  finite_expect f (uniform_indices d) = d%:R^-1 * ticket_sum f (iota 0 d).
Proof.
  unfold uniform_indices. induction (iota 0 d) as [|i xs IH]; cbn [List.map finite_expect ticket_sum];
    [by rewrite mulr0|by rewrite IH mulrDr].
Qed.

Lemma ticket_sum_ext_in {A} (xs : list A) (f g : A -> rat) :
  (forall x, List.In x xs -> f x = g x) -> ticket_sum f xs = ticket_sum g xs.
Proof.
  intro H; induction xs as [|x xs IH]; cbn; first reflexivity.
  rewrite H; last by left.
  congr (_ + _). apply IH=> y Hy. apply H. by right.
Qed.

Lemma in_iota_bound i d : List.In i (iota 0 d) -> (i < d)%N.
Proof.
  have H : forall n k, List.In i (iota n k) -> (n <= i < n+k)%N.
  { move=> n k; elim: k n=> [|k IH] n /=; first by move=> [].
    move=> [<-|Hin]; first by rewrite leqnn /= addnS ltnS leq_addr.
    have /andP [Hlo Hhi] := IH _ Hin.
    apply/andP; split; first exact: leq_trans (leqnSn n) Hlo.
    by move: Hhi; rewrite addSn addnS. }
  move=> Hin. have /andP [_ Hhi] := H 0 d Hin. exact Hhi.
Qed.

(** An explicit probability contract, not a global instance or an existence
    axiom: at every supplied history the next index has the uniform law. *)
Definition uniform_entropy (source : list nat -> nat -> list (rat * nat)) :=
  forall h d, (0 < d)%N ->
    finite_nonnegative (source h d) /\
    forall f, finite_expect f (source h d) = finite_expect f (uniform_indices d).

Lemma fresh_uniform_entropy : uniform_entropy (fun _ d => uniform_indices d).
Proof.
  intros h d Hd; split; last reflexivity.
  intros p i Hin. apply List.in_map_iff in Hin.
  destruct Hin as [j [H _]]. inversion H; subst.
  by rewrite invr_ge0 ler0n.
Qed.

Section EntropyTraces.
Variable source : list nat -> nat -> list (rat * nat).

(** Generate only the entropy actually requested by the finite execution.
    Each node has its own bound and history. Loss stops, without conditioning
    or resampling; a resource timeout requests no entropy. *)
Fixpoint trace_distribution {A} (fuel : nat) (t : ptree void1 SubEnumQ A)
    (history : list nat) : list (rat * list nat) :=
  match observe t with
  | RetF a => [(1, [])]
  | @VisF _ _ _ _ X e k => match e with end
  | TauF u => match fuel with
      | O => [(1, [])] | S n => trace_distribution n u history end
  | @ProbF _ _ _ _ X mu k => match fuel with
      | O => [(1, [])]
      | S n => finite_bind (source history (ticket_count mu)) (fun i =>
          if (i < ticket_count mu)%N then
            match draw_ticket mu i with
            | Some x => List.map (fun ws => (fst ws, i :: snd ws))
                (trace_distribution n (k x) (i :: history))
            | None => [(1, [i])]
            end
          else [(1, [i])])
      end
  end.

Definition replay_expectation {A} n (t : ptree void1 SubEnumQ A) history f :=
  finite_expect (fun trace => f (fst (run (@ticket_replay) n t trace)))
    (trace_distribution n t history).

Lemma replay_prob_cons {A X} n (mu : SubEnumQ X)
    (k : X -> ptree void1 SubEnumQ A) i tail :
  run (@ticket_replay) (S n) (Prob mu k) (i :: tail) =
    if (i < ticket_count mu)%N then
      match draw_ticket mu i with
      | Some x => run (@ticket_replay) n (k x) tail
      | None => (Lost, tail)
      end
    else (EntropyExhausted, tail).
Proof.
  cbn [run observe _observe ticket_replay ticket_sample ticket_replay_source].
  destruct (i < ticket_count mu)%N; [destruct (draw_ticket mu i)|]; reflexivity.
Qed.

Hypothesis Hsource : uniform_entropy source.

Theorem finite_runner_distribution {A} n (t : ptree void1 SubEnumQ A) history f :
  replay_expectation n t history f = outcome_expectation n t f.
Proof.
  unfold replay_expectation, outcome_expectation.
  induction n as [|n IH] in t, history |- *;
    destruct (observe t) as [a|u|X e k|X mu k] eqn:Ht;
    cbn [trace_distribution outcome_distribution run]; rewrite Ht;
    cbn [finite_expect fst snd];
    try (destruct e); try reflexivity.
  - exact: IH.
  - etransitivity; [apply finite_expect_bind|].
    etransitivity; [apply (proj2 (Hsource history
      (compile_tickets_positive (subenumQ_data mu))))|].
    etransitivity; [apply uniform_indices_expect|].
    transitivity (ticket_expectation mu
      (fun v => match v with Some x => outcome_expectation n (k x) f | None => f Lost end)).
    + rewrite /ticket_expectation ticket_sum_map.
      congr (_ * _). apply ticket_sum_ext_in.
      intros i Hi. have Hib : (i < ticket_count mu)%N.
      { exact: in_iota_bound Hi. }
      rewrite Hib. destruct (draw_ticket mu i) as [x|] eqn:Hx.
      * etransitivity; [apply finite_expect_map|].
        transitivity (replay_expectation n (k x) (i :: history) f); last exact: IH.
        apply finite_expect_ext=> tail.
        cbn [ticket_replay ticket_sample ticket_replay_source].
        by rewrite Hib Hx.
      * cbn [finite_expect].
        cbn [ticket_replay ticket_sample ticket_replay_source].
        by rewrite Hib Hx /= mul1r addr0.
    + rewrite uniform_ticket_expectation finite_expect_app finite_expect_bind.
      by rewrite /= addr0.
Qed.

Theorem trace_distribution_mass {A} n (t : ptree void1 SubEnumQ A) history :
  finite_expect (fun _ => 1) (trace_distribution n t history) = 1.
Proof.
  change (replay_expectation n t history (fun _ => 1) = 1).
  rewrite finite_runner_distribution. exact: outcome_distribution_mass.
Qed.

Corollary replay_no_entropy_failure {A} n (t : ptree void1 SubEnumQ A) history :
  replay_expectation n t history (fun r => match r with EntropyExhausted => 1 | _ => 0 end) = 0.
Proof. rewrite finite_runner_distribution. exact: outcome_distribution_no_entropy_failure. Qed.

Theorem trace_distribution_nonnegative {A} n (t : ptree void1 SubEnumQ A) history :
  finite_nonnegative (trace_distribution n t history).
Proof.
  induction n as [|n IH] in t, history |- *;
    destruct (observe t) as [a|u|X e k|X mu k] eqn:Ht;
    cbn [trace_distribution]; rewrite Ht; try (destruct e).
  all: try (intros p x [H|[]]; inversion H; subst; exact: ler01).
  - exact: IH.
  - have Hbranch : forall i, finite_nonnegative
        (if (i < ticket_count mu)%N then
          match draw_ticket mu i with
          | Some x => List.map (fun ws => (fst ws, i :: snd ws))
              (trace_distribution n (k x) (i :: history))
          | None => [(1,[i])]
          end else [(1,[i])]).
    { intro i; destruct (i < ticket_count mu)%N;
        [destruct (draw_ticket mu i) as [x|]|].
      - intros p tail Hin. apply List.in_map_iff in Hin.
        destruct Hin as [[q rest] [H Hin]]. inversion H; subst.
        exact (IH (k x) (i :: history) p rest Hin).
      - intros p tail [H|[]]; inversion H; subst; exact: ler01.
      - intros p tail [H|[]]; inversion H; subst; exact: ler01. }
    exact (finite_enum_nonnegative
      (finite_enum_bind
        (finite_enum_of_list (proj1 (Hsource history
          (compile_tickets_positive (subenumQ_data mu)))))
        (fun i => finite_enum_of_list (Hbranch i)))).
Qed.
End EntropyTraces.
