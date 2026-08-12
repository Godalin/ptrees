Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order
  rat.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import RatSubTypes DiscreteMC FrontierLift
  FrontierLiftEnum EnumBindFacts MeasureIteration MeasureIterationEnum.
From PTree.Eq Require Import PWeakAbstract PWeakUnbounded
  PWeakUnboundedEquiv.
From PTree.Examples Require Import VonNeumannUnbounded RationalBernoulli.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import GRing.Theory Num.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Unset Automatic Proposition Inductives.
Variant factoryE : Type -> Type := .

Section Factory.
Variables pfalse ptrue : nnQ.
Variable q : rat.

Definition factory_biased_coin : Enum bool :=
  [:: (pfalse, false); (ptrue, true)].

Definition factory_round_measure : Enum (unit + bool) :=
  bind_Enum factory_biased_coin (fun b1 =>
    bind_Enum factory_biased_coin (fun b2 =>
      ret_Enum (vn_round_result b1 b2))).

Definition factory_vn_step (_ : unit) :
    ptree factoryE Enum (unit + bool) :=
  Prob factory_biased_coin (fun b1 =>
    Prob factory_biased_coin (fun b2 => Ret (vn_round_result b1 b2))).

Definition factory_fair_coin : ptree factoryE Enum bool :=
  PTree.iter factory_vn_step tt.

Definition factory_fair_heads : Enum (aphead factoryE Enum bool) :=
  meas_bind vn_fair (fun b =>
    meas_ret (APHRet b : aphead factoryE Enum bool)).

Lemma factory_round_is_param_round :
  factory_round_measure = param_round_measure pfalse ptrue.
Proof. reflexivity. Qed.

Lemma factory_transition_heads :
  bind_Enum factory_round_measure (fun next =>
    ret_Enum (APHRet next : aphead factoryE Enum (unit + bool))) =
  bind_Enum factory_biased_coin (fun b1 =>
    bind_Enum factory_biased_coin (fun b2 =>
      ret_Enum (APHRet (vn_round_result b1 b2) :
        aphead factoryE Enum (unit + bool)))).
Proof.
  rewrite /factory_round_measure bind_Enum_assoc.
  apply bind_Enum_ext=> b1.
  rewrite bind_Enum_assoc.
  apply bind_Enum_ext=> b2.
  by rewrite /ret_Enum /bind_Enum /= mulr1.
Qed.

Lemma factory_vn_step_frontier i :
  apfrontier (observe (factory_vn_step i))
    (bind_Enum factory_round_measure (fun next =>
      ret_Enum (APHRet next : aphead factoryE Enum (unit + bool)))).
Proof.
  destruct i.
  change (apfrontier (observe (factory_vn_step tt))
    (bind_Enum factory_round_measure (fun next =>
      ret_Enum (APHRet next : aphead factoryE Enum (unit + bool))))).
  rewrite factory_transition_heads.
  cbn [factory_vn_step].
  change (apfrontier
    (ProbF factory_biased_coin (fun b1 =>
      Prob factory_biased_coin (fun b2 => Ret (vn_round_result b1 b2))))
    (meas_bind factory_biased_coin (fun b1 =>
      meas_bind factory_biased_coin (fun b2 =>
        meas_ret (APHRet (vn_round_result b1 b2) :
          aphead factoryE Enum (unit + bool)))))).
  apply (APFProb
    (front := fun b1 => meas_bind factory_biased_coin (fun b2 =>
      meas_ret (APHRet (vn_round_result b1 b2) :
        aphead factoryE Enum (unit + bool))))
    (Good := fun _ => True)).
  - apply meas_ae_true.
  - move=> b1 _. apply (APFProb
      (front := fun b2 =>
        meas_ret (APHRet (vn_round_result b1 b2) :
          aphead factoryE Enum (unit + bool)))
      (Good := fun _ => True)).
    + apply meas_ae_true.
    + move=> b2 _. constructor.
Qed.

Hypothesis pnormalized : Qval pfalse + Qval ptrue = 1.
Hypothesis pnontrivial : 0 < Qval pfalse * Qval ptrue.

Lemma factory_fair_coin_frontier :
  aufrontier (observe factory_fair_coin) factory_fair_heads.
Proof.
  unfold factory_fair_coin, factory_fair_heads.
  eapply (AUFIter (step := factory_vn_step)
    (transition := fun _ : unit => factory_round_measure)
    (i := tt) (out := vn_fair)).
  - exact factory_vn_step_frontier.
  - rewrite factory_round_is_param_round.
    exact (param_iteration_converges_of_normalized_bias
      (p := pfalse) (q := ptrue) pnormalized pnontrivial).
  - exact vn_fair_total.
Qed.

Definition binary_round_result (x : rat) (b : bool) : rat + bool :=
  if x < 1 / 2 then
    if b then inr false else inl (2 * x)
  else
    if b then inl (2 * x - 1) else inr true.

Lemma fair_binary_round_measure x :
  bind_Enum vn_fair (fun b => ret_Enum (binary_round_result x b)) =
  binary_coin_transition x.
Proof.
  rewrite /vn_fair /binary_round_result /binary_coin_transition.
  by case: (x < 1 / 2); rewrite /bind_Enum /ret_Enum /= !mulr1.
Qed.

Definition factory_binary_step (x : rat) :
    ptree factoryE Enum (rat + bool) :=
  PTree.bind factory_fair_coin (fun b => Ret (binary_round_result x b)).

Definition biased_to_rational_coin : ptree factoryE Enum bool :=
  PTree.iter factory_binary_step q.

Definition binary_result_front (x : rat) (b : bool) :
    Enum (aphead factoryE Enum (rat + bool)) :=
  ret_Enum (APHRet (binary_round_result x b)).

Definition binary_head_bind_kernel (x : rat)
    (h : aphead factoryE Enum bool) :
    Enum (aphead factoryE Enum (rat + bool)) :=
  aphead_bind_front
    (fun b => (Ret (binary_round_result x b) :
      ptree factoryE Enum (rat + bool)))
    (binary_result_front x) h.

Lemma factory_binary_heads_measure x :
  bind_Enum factory_fair_heads (binary_head_bind_kernel x) =
  bind_Enum (binary_coin_transition x) (fun next =>
    ret_Enum (APHRet next : aphead factoryE Enum (rat + bool))).
Proof.
  rewrite /factory_fair_heads /binary_head_bind_kernel
    /binary_result_front /aphead_bind_front /vn_fair
    /binary_round_result /binary_coin_transition
    /bind_Enum /ret_Enum /=.
  by case: (x < 1 / 2); rewrite /= !mulr1.
Qed.

Definition factory_direct_q (q0 : 0 <= q) (q1 : q <= 1) :
    ptree factoryE Enum bool :=
  Prob (rational_bernoulli_measure q0 q1) (fun b => Ret b).

Lemma factory_binary_step_frontier x :
  aufrontier (observe (factory_binary_step x))
    (bind_Enum (binary_coin_transition x) (fun next =>
      ret_Enum (APHRet next : aphead factoryE Enum (rat + bool)))).
Proof.
  unfold factory_binary_step.
  have Hbind := AUFBind
    (k := fun b => (Ret (binary_round_result x b) :
      ptree factoryE Enum (rat + bool)))
    (front := binary_result_front x)
    factory_fair_coin_frontier.
  have Hcont : forall b,
      aufrontier
        (observe (Ret (binary_round_result x b) :
          ptree factoryE Enum (rat + bool)))
        (binary_result_front x b).
  { move=> b. apply AUFFinite. constructor. }
  specialize (Hbind Hcont).
  change (aufrontier
    (observe (PTree.bind factory_fair_coin
      (fun b => Ret (binary_round_result x b))))
    (bind_Enum factory_fair_heads (binary_head_bind_kernel x))) in Hbind.
  rewrite factory_binary_heads_measure in Hbind.
  exact Hbind.
Qed.

Hypothesis q0 : 0 <= q.
Hypothesis q1 : q <= 1.

Definition factory_q_heads : Enum (aphead factoryE Enum bool) :=
  meas_bind (rational_bernoulli_measure q0 q1) (fun b =>
    meas_ret (APHRet b : aphead factoryE Enum bool)).

Lemma biased_to_rational_coin_frontier :
  aufrontier (observe biased_to_rational_coin) factory_q_heads.
Proof.
  unfold biased_to_rational_coin, factory_q_heads.
  eapply (AUFNestedIter (step := factory_binary_step)
    (transition := binary_coin_transition)
    (i := q) (out := rational_bernoulli_measure q0 q1)).
  - exact factory_binary_step_frontier.
  - exact (rational_binary_iteration_converges q0 q1).
  - exact (rational_bernoulli_total q0 q1).
Qed.

(** Both nested loops terminate almost surely: the inner loop extracts a
    fair bit from the [p]-coin, and the outer binary-interval loop consumes
    those bits until it decides the [q]-coin. *)
Theorem biased_to_rational_coin_ast :
  meas_iter_ast (fun _ : unit => factory_round_measure) tt /\
  meas_iter_ast binary_coin_transition q.
Proof.
  split.
  - rewrite factory_round_is_param_round.
    exact (param_von_neumann_almost_surely_terminates
      (p := pfalse) (q := ptrue) pnormalized pnontrivial).
  - exact (rational_binary_coin_almost_surely_terminates q0 q1).
Qed.

Lemma factory_direct_q_frontier :
  aufrontier (observe (factory_direct_q q0 q1)) factory_q_heads.
Proof.
  apply AUFFinite.
  unfold factory_direct_q, factory_q_heads.
  apply (APFProb
    (front := fun b =>
      ret_Enum (APHRet b : aphead factoryE Enum bool))
    (Good := fun _ => True)).
  - apply meas_ae_true.
  - move=> b _. constructor.
Qed.

Theorem biased_coin_simulates_rational_coin :
  auweak eq biased_to_rational_coin (factory_direct_q q0 q1).
Proof.
  apply auweak_fold.
  eapply AUWFrontier with (hs1 := factory_q_heads) (hs2 := factory_q_heads).
  - exact biased_to_rational_coin_frontier.
  - exact factory_direct_q_frontier.
  - apply meas_lift_refl.
    apply auhead_rel_refl.
    exact auweak_refl.
Qed.

Theorem biased_coin_simulates_rational_coin_auequiv :
  auequiv biased_to_rational_coin (factory_direct_q q0 q1).
Proof.
  apply auequiv_of_auweak.
  exact biased_coin_simulates_rational_coin.
Qed.

(** End-to-end specification of the executable rational Bernoulli factory.
    The source enumeration is a normalized non-trivial [p]-coin.  The first
    unbounded loop applies von Neumann extraction, and the second consumes
    fair bits using the binary expansion of [q].  Both loops are AST and the
    resulting program is equivalent to sampling the direct [q]-coin.

    [auweak] is the omega-frontier extension of [apweak]; plain [apweak]
    cannot in general expose the result of an unbounded internal loop. *)
Theorem biased_to_rational_coin_correct :
  meas_iter_ast (fun _ : unit => factory_round_measure) tt /\
  meas_iter_ast binary_coin_transition q /\
  auweak eq biased_to_rational_coin (factory_direct_q q0 q1).
Proof.
  have [Hfair Hq] := biased_to_rational_coin_ast.
  repeat split=> //.
  exact biased_coin_simulates_rational_coin.
Qed.

End Factory.

(** A closed, non-trivial executable instance: two tosses of the [1/3]
    source coin are repeatedly von-Neumann-filtered, and the resulting fair
    bits drive the binary algorithm for a [2/5] target coin. *)
Definition third_to_two_fifths : ptree factoryE Enum bool :=
  biased_to_rational_coin vn_one_third vn_two_thirds (2 / 5).

Definition direct_two_fifths : ptree factoryE Enum bool :=
  factory_direct_q vn_one_third vn_two_thirds (2 / 5)
    (ltW (divr_gt0 (ltr0Sn 2) (ltr0Sn 5)))
    (ltW (ltr_pdivrMr (ltr0Sn 5)
      (by norm_num : (2 : rat) < 1 * 5))).

Lemma third_bias_normalized :
  Qval vn_one_third + Qval vn_two_thirds = 1.
Proof. vm_compute. Qed.

Lemma third_bias_nontrivial :
  0 < Qval vn_one_third * Qval vn_two_thirds.
Proof. vm_compute. Qed.

Lemma two_fifths_nonnegative : (0 <= 2 / 5 : rat).
Proof. vm_compute. Qed.

Lemma two_fifths_at_most_one : (2 / 5 <= 1 : rat).
Proof. vm_compute. Qed.

Theorem third_coin_simulates_two_fifths_correct :
  meas_iter_ast
    (fun _ : unit =>
      factory_round_measure vn_one_third vn_two_thirds) tt /\
  meas_iter_ast binary_coin_transition (2 / 5) /\
  auweak eq third_to_two_fifths
    (factory_direct_q vn_one_third vn_two_thirds (2 / 5)
      two_fifths_nonnegative two_fifths_at_most_one).
Proof.
  exact (biased_to_rational_coin_correct
    third_bias_normalized third_bias_nontrivial
    two_fifths_nonnegative two_fifths_at_most_one).
Qed.

Theorem third_coin_simulates_two_fifths_auequiv :
  auequiv third_to_two_fifths
    (factory_direct_q vn_one_third vn_two_thirds (2 / 5)
      two_fifths_nonnegative two_fifths_at_most_one).
Proof.
  exact (biased_coin_simulates_rational_coin_auequiv
    third_bias_normalized third_bias_nontrivial
    two_fifths_nonnegative two_fifths_at_most_one).
Qed.
