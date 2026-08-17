Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Ring Field Lia FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssralg ssrnum
  order rat archimedean.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import RatSubTypes DiscreteMC EnumBindFacts FrontierLift
  FrontierLiftEnum MeasureIteration MeasureIterationEnum RatGeometric.
From PTree.Eq Require Import PWeakAbstract PWeakUnbounded
  PWeakUnboundedEquiv PWeakObservableEnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import EnumMap.
Import RatSubTypes.NonnegQNotations.
Import GRing.Theory.
Import Num.Theory.
Import Order.Theory.
#[local] Open Scope subrat_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Unset Automatic Proposition Inductives.
Variant vnE : Type -> Type := .

#[program] Definition vn_one_ninth : nnQ := [nn 1/9].
#[program] Definition vn_two_ninths : nnQ := [nn 2/9].
#[program] Definition vn_four_ninths : nnQ := [nn 4/9].
#[program] Definition vn_one_third : nnQ := [nn 1/3].
#[program] Definition vn_two_thirds : nnQ := [nn 2/3].

Lemma vn_one_ninth_val : Qval vn_one_ninth = (1 / 9 : rat).
Proof. reflexivity. Qed.

Lemma vn_two_ninths_val : Qval vn_two_ninths = (2 / 9 : rat).
Proof. reflexivity. Qed.

Lemma vn_four_ninths_val : Qval vn_four_ninths = (4 / 9 : rat).
Proof. reflexivity. Qed.

(** One von Neumann round for a coin with probability [1/3] of [false]
    and [2/3] of [true].  Equal tosses retry; unequal tosses return a bit. *)
Definition vn_transition : Enum (unit + bool) :=
  [:: (vn_one_ninth, inl tt);
      (vn_two_ninths, inr false);
      (vn_two_ninths, inr true);
      (vn_four_ninths, inl tt)].

Definition vn_compiled_step (_ : unit) : ptree vnE Enum (unit + bool) :=
  Prob vn_transition (fun next => Ret next).

Definition vn_biased_coin : Enum bool :=
  [:: (vn_one_third, false); (vn_two_thirds, true)].

Definition vn_round_result (b1 b2 : bool) : unit + bool :=
  if b1 == b2 then inl tt else inr b1.

(** The source program really performs two independent biased tosses. *)
Definition vn_step (_ : unit) : ptree vnE Enum (unit + bool) :=
  Prob vn_biased_coin (fun b1 =>
    Prob vn_biased_coin (fun b2 => Ret (vn_round_result b1 b2))).

Definition vn_round_measure : Enum (unit + bool) :=
  bind_Enum vn_biased_coin (fun b1 =>
    bind_Enum vn_biased_coin (fun b2 =>
      ret_Enum (vn_round_result b1 b2))).

Lemma vn_round_measure_eq : vn_round_measure = vn_transition.
Proof.
  rewrite /vn_round_measure /vn_biased_coin /vn_round_result
    /vn_transition /bind_Enum /ret_Enum /=.
  repeat f_equal; apply val_inj; cbn.
  all: ring_to_rat; reflexivity.
Qed.

Definition von_neumann_third : ptree vnE Enum bool :=
  PTree.iter vn_step tt.

Definition vn_fair : Enum bool :=
  [:: (one_div_two, false); (one_div_two, true)].

Lemma vn_fair_total : meas_total vn_fair.
Proof.
  change (enum_expect (fun _ : bool => 1) vn_fair = 1).
  rewrite /vn_fair /= !mulr1 addr0 -mulrDl.
  change ((2 : rat) / 2 = 1).
  by rewrite divrr // unitfE pnatr_eq0.
Qed.

Definition direct_fair : ptree vnE Enum bool :=
  Prob vn_fair (fun b => Ret b).

(** Event-polymorphic forms of the closed samplers.  Although these programs
    never emit a visible event, exposing the ambient signature is essential
    when they are used inside an interactive client.  The historical [vnE]
    definitions above remain the closed executable API. *)
Definition vn_step_in {E : Type -> Type} (_ : unit) :
    ptree E Enum (unit + bool) :=
  Prob vn_biased_coin (fun b1 =>
    Prob vn_biased_coin (fun b2 => Ret (vn_round_result b1 b2))).

Definition von_neumann_third_in {E : Type -> Type} : ptree E Enum bool :=
  PTree.iter vn_step_in tt.

Definition direct_fair_in {E : Type -> Type} : ptree E Enum bool :=
  Prob vn_fair (fun b => Ret b).

Lemma vn_step_in_closed : @vn_step_in vnE = vn_step.
Proof. reflexivity. Qed.

Lemma von_neumann_third_in_closed :
  @von_neumann_third_in vnE = von_neumann_third.
Proof. reflexivity. Qed.

Lemma direct_fair_in_closed : @direct_fair_in vnE = direct_fair.
Proof. reflexivity. Qed.

Definition indicator {A} (P : A -> bool) (x : A) : rat :=
  if P x then 1 else 0.

Lemma vn_collect (a d z s1 s2 : rat) :
  a * z + (s1 + (s2 + d * z)) =
  (a + d) * z + (s1 + s2).
Proof.
  rewrite [s2 + d * z]addrC.
  rewrite [a * z + (s1 + (d * z + s2))]addrA.
  rewrite addrACA mulrDl.
  reflexivity.
Qed.

Lemma vn_retry_weight :
  (1 / 9 : rat) + 4 / 9 = 5 / 9.
Proof.
  rewrite -mulrDl.
  change (((1%nat)%:R + (4%nat)%:R : rat) / (9%nat)%:R =
    (5%nat)%:R / (9%nat)%:R).
  by rewrite -natrD.
Qed.

Lemma vn_approx_expect_succ n (P : bool -> bool) :
  enum_expect (indicator P)
    (meas_iter_approx (S n) (fun _ => vn_transition) tt) =
  (5 / 9 : rat) * enum_expect (indicator P)
    (meas_iter_approx n (fun _ => vn_transition) tt) +
  (2 / 9 : rat) * (indicator P false + indicator P true).
Proof.
  cbn [meas_iter_approx]. rewrite enum_expect_bind.
  set z := enum_expect (fun x : bool => if P x then 1 else 0)
    (meas_iter_approx n (fun _ : unit =>
      [:: (vn_one_ninth, inl tt);
          (vn_two_ninths, inr false);
          (vn_two_ninths, inr true);
          (vn_four_ninths, inl tt)]) tt).
  rewrite /vn_transition /indicator /=.
  rewrite [1 * (if P false then 1 else 0)]mul1r.
  rewrite [1 * (if P true then 1 else 0)]mul1r.
  rewrite [(if P false then 1 else 0) + 0]addr0.
  rewrite [(if P true then 1 else 0) + 0]addr0.
  rewrite [4 / 9 * _ + 0]addr0.
  rewrite vn_collect vn_retry_weight mulrDr.
  unfold z, vn_transition, indicator. reflexivity.
Qed.

Lemma vn_fair_expect (P : bool -> bool) :
  enum_expect (indicator P) vn_fair =
    (1 / 2 : rat) * (indicator P false + indicator P true).
Proof.
  rewrite /vn_fair /indicator /=.
  by rewrite !mul1r !addr0 mulrDr.
Qed.

Lemma vn_escape_weight :
  1 - (5 / 9 : rat) = 4 / 9.
Proof.
  have Hsum : (5 / 9 : rat) + 4 / 9 = 1.
  { rewrite -mulrDl.
    change (((5%nat)%:R + (4%nat)%:R : rat) / (9%nat)%:R = 1).
    by rewrite -natrD divrr // unitfE pnatr_eq0. }
  rewrite -Hsum.
  by rewrite [(5 / 9 : rat) + 4 / 9]addrC addrK.
Qed.

Lemma vn_four_as_two_two : (4 : rat) = 2 * 2.
Proof.
  change (((4%nat)%:R : rat) = (2%nat)%:R * (2%nat)%:R).
  by rewrite -natrM.
Qed.

Lemma vn_half_escape :
  (1 - (5 / 9 : rat)) * (1 / 2) = 2 / 9.
Proof.
  rewrite vn_escape_weight.
  change (((4 : rat) * (9 : rat)^-1) *
    ((1 : rat) * (2 : rat)^-1) =
    (2 : rat) * (9 : rat)^-1).
  rewrite mul1r vn_four_as_two_two -!mulrA.
  rewrite [(9 : rat)^-1 / 2]mulrC mulrA.
  reflexivity.
Qed.

Lemma vn_geometric_step (r x z : rat) :
  r * ((1 - x) * z) + (1 - r) * z = (1 - r * x) * z.
Proof.
  rewrite mulrA -mulrDl mulrBr mulr1.
  by rewrite addrC subrKA.
Qed.

Lemma vn_success_is_escape (P : bool -> bool) :
  (2 / 9 : rat) * (indicator P false + indicator P true) =
  (1 - 5 / 9) * enum_expect (indicator P) vn_fair.
Proof.
  by rewrite vn_fair_expect mulrA vn_half_escape.
Qed.

Lemma vn_approx_closed_form n (P : bool -> bool) :
  enum_expect (indicator P)
      (meas_iter_approx n (fun _ => vn_transition) tt) =
    (1 - (5 / 9 : rat) ^+ n) * enum_expect (indicator P) vn_fair.
Proof.
  elim: n=> [|n IH].
  - rewrite /= /meas_zero /Enum_MeasureOmegaInterface /=.
    by rewrite expr0 subrr mul0r.
  - rewrite vn_approx_expect_succ IH vn_fair_expect exprS.
    rewrite -vn_fair_expect vn_success_is_escape.
    exact: vn_geometric_step.
Qed.

Lemma vn_ratio_nonnegative : 0 <= (5 / 9 : rat).
Proof. by []. Qed.

Lemma vn_ratio_le_two_thirds : (5 / 9 : rat) <= 2 / 3.
Proof. by []. Qed.

Lemma vn_two_thirds_nonnegative : 0 <= (2 / 3 : rat).
Proof. by []. Qed.

Lemma vn_rational_bound_step n :
  (2 / ((n + 2)%:R : rat)) * (2 / 3) <=
    2 / ((n + 3)%:R : rat).
Proof.
  rewrite ler_pdivlMr ?ltr0Sn //.
  rewrite ![_ / _ * _]mulrAC ler_pdivrMr ?ltr0Sn //.
  rewrite -mulrA ler_pM2l ?ltr0Sn //.
  rewrite [(2 / 3 : rat) * (n + 3)%:R]mulrC mulrA.
  rewrite ler_pdivrMr ?ltr0Sn //.
  rewrite -!natrM ler_nat.
  apply/ssrnat.leP.
  change (Peano.le (Nat.mul (Nat.add n 3) 2)
    (Nat.mul (Nat.add n 2) 3)).
  lia.
  all: by rewrite ltr0n addn_gt0 orbT.
Qed.

Lemma vn_two_thirds_bound n :
  (2 / 3 : rat) ^+ n <= 2 / ((n + 2)%:R : rat).
Proof.
  elim: n=> [|n IH].
  - rewrite expr0.
    change ((1 : rat) <= 2 / 2).
    by rewrite divrr // unitfE pnatr_eq0.
  - rewrite exprS.
    rewrite [(2 / 3 : rat) * (2 / 3) ^+ n]mulrC.
    have Hmul := ler_wpM2r vn_two_thirds_nonnegative IH.
    have Hstep := vn_rational_bound_step n.
    rewrite addSn -addnS.
    exact: Order.POrderTheory.le_trans Hmul Hstep.
Qed.

Lemma vn_ratio_bound n :
  (5 / 9 : rat) ^+ n <= 2 / ((n + 2)%:R : rat).
Proof.
  have Hpow := lerXn2r n vn_ratio_nonnegative
    vn_two_thirds_nonnegative vn_ratio_le_two_thirds.
  exact: Order.POrderTheory.le_trans Hpow (vn_two_thirds_bound n).
Qed.

Lemma vn_ratio_vanishes eps : 0 < eps ->
  exists N, forall n, Peano.le N n -> (5 / 9 : rat) ^+ n < eps.
Proof.
  move=> eps_gt0.
  pose N := Num.bound (2 / eps : rat).
  have q_ge0 : 0 <= (2 / eps : rat).
  { apply divr_ge0; [by []|exact: ltW eps_gt0]. }
  have Harch : (2 / eps : rat) < N%:R := archi_boundP q_ge0.
  exists N=> n HNn.
  apply: le_lt_trans (vn_ratio_bound n) _.
  rewrite ltr_pdivrMr; last by rewrite ltr0n addn_gt0 orbT.
  have Htwo : (2 : rat) < N%:R * eps.
  { move: Harch. by rewrite ltr_pdivrMr. }
  have Hcast : (N%:R : rat) <= n%:R.
  { rewrite ler_nat. apply/ssrnat.leP. exact HNn. }
  have Hnadd : (n%:R : rat) <= (n + 2)%:R.
  { rewrite ler_nat. apply/ssrnat.leP.
    change (Peano.le n (Nat.add n 2)). lia. }
  have HNadd : (N%:R : rat) <= (n + 2)%:R :=
    Order.POrderTheory.le_trans Hcast Hnadd.
  have Hmul := ler_wpM2r (ltW eps_gt0) HNadd.
  rewrite ![(_%:R : rat) * eps]mulrC in Htwo Hmul.
  exact: lt_le_trans Htwo Hmul.
Qed.

Lemma vn_difference (x z : rat) :
  (1 - x) * z - z = - (x * z).
Proof.
  rewrite mulrBl mul1r.
  apply: (addrI z).
  by rewrite addrC subrK.
Qed.

Lemma vn_fair_expect_norm (P : bool -> bool) :
  `|enum_expect (indicator P) vn_fair| <= 1.
Proof.
  rewrite vn_fair_expect /indicator.
  case Hf: (P false); case Ht: (P true); simpl.
  all: rewrite ?mulr1 ?mulr0 ?addr0 ?add0r.
  all: by [].
Qed.

Lemma vn_iteration_converges :
  meas_iter (fun _ : unit => vn_transition) tt vn_fair.
Proof.
  unfold meas_iter, meas_lub, Enum_MeasureOmegaInterface,
    enum_converges.
  move=> P eps eps_gt0.
  destruct (vn_ratio_vanishes eps_gt0) as [N HN].
  exists N=> n Hfuel.
  rewrite vn_approx_closed_form vn_difference normrN normrM.
  have Hpow : 0 <= (5 / 9 : rat) ^+ n :=
    exprn_ge0 n vn_ratio_nonnegative.
  rewrite (ger0_norm Hpow).
  have Hbounded := ler_wpM2l Hpow (vn_fair_expect_norm P).
  rewrite mulr1 in Hbounded.
  exact: le_lt_trans Hbounded (HN n Hfuel).
Qed.

Theorem von_neumann_third_almost_surely_terminates :
  meas_iter_ast (fun _ : unit => vn_transition) tt.
Proof.
  eapply meas_iter_total_ast.
  - exact vn_iteration_converges.
  - exact vn_fair_total.
Qed.

Definition vn_heads : Enum (aphead vnE Enum bool) :=
  meas_bind vn_fair (fun b =>
    meas_ret (APHRet b : aphead vnE Enum bool)).

Lemma vn_transition_heads :
  bind_Enum vn_transition (fun next =>
    ret_Enum (APHRet next : aphead vnE Enum (unit + bool))) =
  bind_Enum vn_biased_coin (fun b1 =>
    bind_Enum vn_biased_coin (fun b2 =>
      ret_Enum (APHRet (vn_round_result b1 b2) :
        aphead vnE Enum (unit + bool)))).
Proof.
  rewrite -vn_round_measure_eq /vn_round_measure bind_Enum_assoc.
  apply bind_Enum_ext=> b1.
  rewrite bind_Enum_assoc.
  apply bind_Enum_ext=> b2.
  by rewrite /ret_Enum /bind_Enum /= mulr1.
Qed.

Lemma vn_step_frontier i :
  apfrontier (observe (vn_step i))
    (meas_bind vn_transition (fun next =>
      meas_ret (APHRet next : aphead vnE Enum (unit + bool)))).
Proof.
  destruct i.
  change (apfrontier (observe (vn_step tt))
    (bind_Enum vn_transition (fun next =>
      ret_Enum (APHRet next : aphead vnE Enum (unit + bool))))).
  rewrite vn_transition_heads.
  cbn [vn_step].
  change (apfrontier
    (ProbF vn_biased_coin (fun b1 =>
      Prob vn_biased_coin (fun b2 => Ret (vn_round_result b1 b2))))
    (meas_bind vn_biased_coin (fun b1 =>
      meas_bind vn_biased_coin (fun b2 =>
        meas_ret (APHRet (vn_round_result b1 b2) :
          aphead vnE Enum (unit + bool)))))).
  apply (APFProb
    (front := fun b1 =>
      meas_bind vn_biased_coin (fun b2 =>
        meas_ret (APHRet (vn_round_result b1 b2) :
          aphead vnE Enum (unit + bool))))
    (Good := fun _ => True)).
  - apply meas_ae_true.
  - move=> b1 _. apply (APFProb
      (front := fun b2 =>
        meas_ret (APHRet (vn_round_result b1 b2) :
          aphead vnE Enum (unit + bool)))
      (Good := fun _ => True)).
    + apply meas_ae_true.
    + move=> b2 _. constructor.
Qed.

Lemma von_neumann_unbounded_frontier :
  aufrontier (observe von_neumann_third) vn_heads.
Proof.
  unfold von_neumann_third, vn_heads.
  eapply (AUFIter (step := vn_step)
    (transition := fun _ : unit => vn_transition)
    (i := tt) (out := vn_fair)).
  - exact vn_step_frontier.
  - exact vn_iteration_converges.
  - exact vn_fair_total.
Qed.

Lemma direct_fair_frontier :
  aufrontier (observe direct_fair) vn_heads.
Proof.
  apply AUFFinite.
  unfold direct_fair, vn_heads.
  apply (APFProb
    (front := fun b =>
      meas_ret (APHRet b : aphead vnE Enum bool))
    (Good := fun _ => True)).
  - apply meas_ae_true.
  - move=> b _. constructor.
Qed.

(** The unbounded retrying program built from a genuinely biased coin is
    weakly equivalent to one direct fair toss. *)
Theorem von_neumann_third_equivalent_to_fair :
  auweak eq von_neumann_third direct_fair.
Proof.
  apply auweak_fold.
  eapply AUWFrontier with (hs1 := vn_heads) (hs2 := vn_heads).
  - exact von_neumann_unbounded_frontier.
  - exact direct_fair_frontier.
  - apply meas_lift_refl.
    apply auhead_rel_refl.
    exact auweak_refl.
Qed.

Theorem von_neumann_third_preserves_true_probability :
  exists hs1 hs2,
    aufrontier (observe von_neumann_third) hs1 /\
    aufrontier (observe direct_fair) hs2 /\
    @meas_eq Enum Enum_MeasureInterface bool
      (emap (auhead_returns (fun b => b)) hs1)
      (emap (auhead_returns (fun b => b)) hs2).
Proof.
  exact (common_aufrontier_return_observation (fun b => b)
    von_neumann_unbounded_frontier direct_fair_frontier).
Qed.

Theorem von_neumann_third_auequiv_fair :
  auequiv von_neumann_third direct_fair.
Proof.
  apply auequiv_of_auweak.
  exact von_neumann_third_equivalent_to_fair.
Qed.

(** ** Parametric correctness layer

    The coinductive proof itself is independent of the numerical bias.  Its
    only analytic premise is that the absorbing iteration converges to the
    fair measure.  Concrete measure models can discharge that premise using
    their preferred limit theory; [vn_iteration_converges] above is one fully
    proved instance. *)
Section ParametricVonNeumann.

Variables p q : nnQ.

Definition param_biased_coin : Enum bool :=
  [:: (p, false); (q, true)].

Definition param_round_measure : Enum (unit + bool) :=
  bind_Enum param_biased_coin (fun b1 =>
    bind_Enum param_biased_coin (fun b2 =>
      ret_Enum (vn_round_result b1 b2))).

Definition param_step (_ : unit) : ptree vnE Enum (unit + bool) :=
  Prob param_biased_coin (fun b1 =>
    Prob param_biased_coin (fun b2 => Ret (vn_round_result b1 b2))).

Definition param_von_neumann : ptree vnE Enum bool :=
  PTree.iter param_step tt.

Lemma param_transition_heads :
  bind_Enum param_round_measure (fun next =>
    ret_Enum (APHRet next : aphead vnE Enum (unit + bool))) =
  bind_Enum param_biased_coin (fun b1 =>
    bind_Enum param_biased_coin (fun b2 =>
      ret_Enum (APHRet (vn_round_result b1 b2) :
        aphead vnE Enum (unit + bool)))).
Proof.
  rewrite /param_round_measure bind_Enum_assoc.
  apply bind_Enum_ext=> b1.
  rewrite bind_Enum_assoc.
  apply bind_Enum_ext=> b2.
  by rewrite /ret_Enum /bind_Enum /= mulr1.
Qed.

Lemma param_step_frontier i :
  apfrontier (observe (param_step i))
    (meas_bind param_round_measure (fun next =>
      meas_ret (APHRet next : aphead vnE Enum (unit + bool)))).
Proof.
  destruct i.
  change (apfrontier (observe (param_step tt))
    (bind_Enum param_round_measure (fun next =>
      ret_Enum (APHRet next : aphead vnE Enum (unit + bool))))).
  rewrite param_transition_heads.
  cbn [param_step].
  change (apfrontier
    (ProbF param_biased_coin (fun b1 =>
      Prob param_biased_coin (fun b2 => Ret (vn_round_result b1 b2))))
    (meas_bind param_biased_coin (fun b1 =>
      meas_bind param_biased_coin (fun b2 =>
        meas_ret (APHRet (vn_round_result b1 b2) :
          aphead vnE Enum (unit + bool)))))).
  apply (APFProb
    (front := fun b1 =>
      meas_bind param_biased_coin (fun b2 =>
        meas_ret (APHRet (vn_round_result b1 b2) :
          aphead vnE Enum (unit + bool))))
    (Good := fun _ => True)).
  - apply meas_ae_true.
  - move=> b1 _. apply (APFProb
      (front := fun b2 =>
        meas_ret (APHRet (vn_round_result b1 b2) :
          aphead vnE Enum (unit + bool)))
      (Good := fun _ => True)).
    + apply meas_ae_true.
    + move=> b2 _. constructor.
Qed.

Definition param_a : rat := Qval p.
Definition param_b : rat := Qval q.
Definition param_retry : rat := param_a * param_a + param_b * param_b.
Definition param_success : rat := param_a * param_b.

Lemma param_escape_of_normalized
    (Hsum : param_a + param_b = 1) :
  param_success = (1 - param_retry) * (1 / 2).
Proof.
  unfold param_success, param_retry.
  have Hsquare : 1 =
      (param_a + param_b) * (param_a + param_b).
  { by rewrite Hsum mulr1. }
  have Hinter :
      1 -
        (param_a * param_a + param_b * param_b) =
      param_a * param_b + param_a * param_b.
  { apply: (addIr (param_a * param_a + param_b * param_b)).
    rewrite subrK Hsquare !mulrDr !mulrDl.
    rewrite [param_b * param_a]mulrC.
    rewrite [param_a * param_b + param_b * param_b]addrC addrACA.
    exact: addrC. }
  rewrite Hinter -mulrDr.
  have Hdouble : param_b + param_b = param_b * (1 + 1 : rat).
  { by rewrite mulrDr !mulr1. }
  rewrite Hdouble !mulrA.
  rewrite mulr1.
  change (param_a * param_b =
    param_a * param_b * (2 : rat) / 2).
  by rewrite mulrK // unitfE pnatr_eq0.
Qed.

Lemma param_retry_nonnegative : 0 <= param_retry.
Proof.
  unfold param_retry, param_a, param_b.
  apply addr_ge0; apply mulr_ge0; exact: le_nnQ0.
Qed.

Lemma param_retry_strict_of_normalized
    (Hsum : param_a + param_b = 1)
    (success0 : 0 < param_success) :
  param_retry < 1.
Proof.
  have Hescape := param_escape_of_normalized Hsum.
  have Hprod : 0 < (1 - param_retry) * (1 / 2).
  { by rewrite -Hescape. }
  have half0 : 0 < (1 / 2 : rat).
  { apply divr_gt0.
    - exact ltr01.
    - exact: ltr0Sn. }
  have Hsub : 0 < 1 - param_retry.
  { have Hprod' : (0 : rat) * (1 / 2) <
        (1 - param_retry) * (1 / 2).
    { by rewrite mul0r. }
    move: Hprod'.
    by rewrite ltr_pM2r. }
  by move: Hsub; rewrite subr_gt0.
Qed.

Lemma param_collect (a b z f t : rat) :
  a * (a * z + b * f) + b * (a * t + b * z) =
  (a * a + b * b) * z + (a * b) * (f + t).
Proof.
  rewrite !mulrDr !mulrA [b * a]mulrC.
  rewrite [a * b * t + b * b * z]addrC addrACA.
  by rewrite mulrDl.
Qed.

Lemma param_round_expect (P : bool -> bool) z :
  enum_expect
    (fun next => match next with
      | inl _ => z
      | inr b => indicator P b
      end) param_round_measure =
  param_retry * z +
    param_success * (indicator P false + indicator P true).
Proof.
  rewrite /param_round_measure !enum_expect_bind
    /param_biased_coin /=.
  rewrite /param_a /param_b /param_retry /param_success.
  rewrite !mulr1 !addr0.
  exact: param_collect.
Qed.

Lemma param_approx_expect_succ n (P : bool -> bool) :
  enum_expect (indicator P)
    (meas_iter_approx (S n)
      (fun _ : unit => param_round_measure) tt) =
  param_retry * enum_expect (indicator P)
    (meas_iter_approx n (fun _ : unit => param_round_measure) tt) +
  param_success * (indicator P false + indicator P true).
Proof.
  cbn [meas_iter_approx]. rewrite enum_expect_bind.
  set z := enum_expect (indicator P)
    (meas_iter_approx n (fun _ : unit => param_round_measure) tt).
  have Hfun :
      (fun x : unit + bool =>
        enum_expect (indicator P)
          match x with
          | inl i' =>
              meas_iter_approx n
                (fun _ : unit => param_round_measure) i'
          | inr a => meas_ret a
          end) =
      (fun x => match x with
        | inl _ => z
        | inr b => indicator P b
        end).
  { apply functional_extensionality=> x.
    destruct x as [u|b].
    - destruct u. reflexivity.
    - apply enum_expect_ret. }
  rewrite Hfun. exact: param_round_expect.
Qed.

Lemma param_success_is_escape
    (Hescape : param_success = (1 - param_retry) * (1 / 2))
    (P : bool -> bool) :
  param_success * (indicator P false + indicator P true) =
  (1 - param_retry) * enum_expect (indicator P) vn_fair.
Proof.
  rewrite Hescape vn_fair_expect.
  by rewrite -mulrA.
Qed.

Lemma param_approx_closed_form
    (Hescape : param_success = (1 - param_retry) * (1 / 2))
    n (P : bool -> bool) :
  enum_expect (indicator P)
      (meas_iter_approx n
        (fun _ : unit => param_round_measure) tt) =
    (1 - param_retry ^+ n) * enum_expect (indicator P) vn_fair.
Proof.
  elim: n=> [|n IH].
  - rewrite /= /meas_zero /Enum_MeasureOmegaInterface /=.
    by rewrite expr0 subrr mul0r.
  - rewrite param_approx_expect_succ IH exprS.
    rewrite (param_success_is_escape Hescape).
    exact: vn_geometric_step.
Qed.

Lemma param_iteration_converges_of_contract
    (Hescape : param_success = (1 - param_retry) * (1 / 2))
    K (Kpos : (0 < K)%coq_nat)
    (retry0 : 0 <= param_retry)
    (Hcontract : param_retry <= (K%:R : rat) / K.+1%:R) :
  meas_iter (fun _ : unit => param_round_measure) tt vn_fair.
Proof.
  unfold meas_iter, meas_lub, Enum_MeasureOmegaInterface,
    enum_converges.
  move=> P eps eps0.
  destruct (rat_contract_vanishes Kpos retry0 Hcontract eps0)
    as [N HN].
  exists N=> n Hfuel.
  rewrite (param_approx_closed_form Hescape) vn_difference normrN normrM.
  have Hpow : 0 <= param_retry ^+ n := exprn_ge0 n retry0.
  rewrite (ger0_norm Hpow).
  have Hbounded := ler_wpM2l Hpow (vn_fair_expect_norm P).
  rewrite mulr1 in Hbounded.
  exact: le_lt_trans Hbounded (HN n Hfuel).
Qed.

Theorem von_neumann_correct_of_convergence
    (Hlimit : meas_iter (fun _ : unit => param_round_measure) tt vn_fair) :
  auweak eq param_von_neumann direct_fair.
Proof.
  apply auweak_fold.
  eapply AUWFrontier with (hs1 := vn_heads) (hs2 := vn_heads).
  - unfold param_von_neumann, vn_heads.
    eapply (AUFIter (step := param_step)
      (transition := fun _ : unit => param_round_measure)
      (i := tt) (out := vn_fair)).
    + exact param_step_frontier.
    + exact Hlimit.
    + exact vn_fair_total.
  - exact direct_fair_frontier.
  - apply meas_lift_refl.
    apply auhead_rel_refl.
    exact auweak_refl.
Qed.

Theorem von_neumann_correct_of_contract
    (Hescape : param_success = (1 - param_retry) * (1 / 2))
    K (Kpos : (0 < K)%coq_nat)
    (retry0 : 0 <= param_retry)
    (Hcontract : param_retry <= (K%:R : rat) / K.+1%:R) :
  auweak eq param_von_neumann direct_fair.
Proof.
  apply von_neumann_correct_of_convergence.
  exact (param_iteration_converges_of_contract
    Hescape Kpos retry0 Hcontract).
Qed.

(** The Archimedean property of rational weights constructs [K]
    automatically.  Thus a strict retry probability is the semantic
    hypothesis needed by the unbounded program proof. *)
Theorem von_neumann_correct_of_strict_retry
    (Hescape : param_success = (1 - param_retry) * (1 / 2))
    (retry0 : 0 <= param_retry)
    (retry1 : param_retry < 1) :
  auweak eq param_von_neumann direct_fair.
Proof.
  destruct (rat_contract_certificate retry0 retry1)
    as [K [Kpos Hcontract]].
  exact (von_neumann_correct_of_contract
    Hescape Kpos retry0 Hcontract).
Qed.

(** Direct user-facing form: normalized nonnegative weights with nonzero
    probability of seeing different outcomes implement a fair coin. *)
Theorem von_neumann_correct_of_normalized_bias
    (Hsum : param_a + param_b = 1)
    (success0 : 0 < param_success) :
  auweak eq param_von_neumann direct_fair.
Proof.
  apply von_neumann_correct_of_strict_retry.
  - exact: param_escape_of_normalized.
  - exact param_retry_nonnegative.
  - exact: param_retry_strict_of_normalized.
Qed.

Theorem param_iteration_converges_of_normalized_bias
    (Hsum : param_a + param_b = 1)
    (success0 : 0 < param_success) :
  meas_iter (fun _ : unit => param_round_measure) tt vn_fair.
Proof.
  have Hescape := param_escape_of_normalized Hsum.
  have retry1 := param_retry_strict_of_normalized Hsum success0.
  destruct (rat_contract_certificate param_retry_nonnegative retry1)
    as [K [Kpos Hcontract]].
  exact (param_iteration_converges_of_contract
    Hescape Kpos param_retry_nonnegative Hcontract).
Qed.

(** User-facing AST statement for the parametric extractor.  Positivity of
    [param_success = p*q] excludes the two deterministic endpoint coins;
    normalization then makes the retry probability strictly smaller than
    one. *)
Theorem param_von_neumann_almost_surely_terminates
    (Hsum : param_a + param_b = 1)
    (success0 : 0 < param_success) :
  meas_iter_ast (fun _ : unit => param_round_measure) tt.
Proof.
  eapply meas_iter_total_ast.
  - exact (param_iteration_converges_of_normalized_bias Hsum success0).
  - exact vn_fair_total.
Qed.

Theorem von_neumann_auequiv_of_normalized_bias
    (Hsum : param_a + param_b = 1)
    (success0 : 0 < param_success) :
  auequiv param_von_neumann direct_fair.
Proof.
  apply auequiv_of_auweak.
  exact (von_neumann_correct_of_normalized_bias Hsum success0).
Qed.

End ParametricVonNeumann.

(** The unbounded frontier remains usable below ordinary program context. *)
Definition delayed_von_neumann : ptree vnE Enum bool :=
  Tau von_neumann_third.

Lemma delayed_von_neumann_frontier :
  aufrontier (observe delayed_von_neumann) vn_heads.
Proof.
  change (aufrontier (TauF von_neumann_third) vn_heads).
  apply AUFTau. exact von_neumann_unbounded_frontier.
Qed.

Theorem delayed_von_neumann_equivalent_to_fair :
  auweak eq delayed_von_neumann direct_fair.
Proof.
  apply auweak_fold.
  eapply AUWFrontier with (hs1 := vn_heads) (hs2 := vn_heads).
  - exact delayed_von_neumann_frontier.
  - exact direct_fair_frontier.
  - apply meas_lift_refl.
    apply auhead_rel_refl. exact auweak_refl.
Qed.

Definition singleton_start : Enum unit := ret_Enum tt.

Definition sampled_von_neumann : ptree vnE Enum bool :=
  Prob singleton_start (fun _ => von_neumann_third).

Lemma scale_one_enum {A} (mu : Enum A) :
  scale_Enum (1 : nnQ) mu = mu.
Proof.
  elim: mu=> [|[w x] tl IH] //=.
  by rewrite mul1r IH.
Qed.

Lemma sampled_von_neumann_frontier :
  aufrontier (observe sampled_von_neumann)
    (meas_bind singleton_start (fun _ => vn_heads)).
Proof.
  change (aufrontier
    (ProbF singleton_start (fun _ => von_neumann_third))
    (meas_bind singleton_start (fun _ => vn_heads))).
  apply (AUFProb (front := fun _ => vn_heads)
    (Good := fun _ => True)).
  - apply meas_ae_true.
  - move=> u _. destruct u. exact von_neumann_unbounded_frontier.
Qed.

Lemma sampled_heads_eq :
  meas_bind singleton_start (fun _ => vn_heads) = vn_heads.
Proof.
  change (scale_Enum (1 : nnQ) vn_heads = vn_heads).
  exact: scale_one_enum.
Qed.

Theorem sampled_von_neumann_equivalent_to_fair :
  auweak eq sampled_von_neumann direct_fair.
Proof.
  apply auweak_fold.
  eapply AUWFrontier with
      (hs1 := meas_bind singleton_start (fun _ => vn_heads))
      (hs2 := vn_heads).
  - exact sampled_von_neumann_frontier.
  - exact direct_fair_frontier.
  - rewrite sampled_heads_eq.
    apply meas_lift_refl.
    apply auhead_rel_refl. exact auweak_refl.
Qed.
