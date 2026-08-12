Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8.

From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order
  reals boolp classical_sets.
From mathcomp.analysis Require Import ereal measure.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift MeasureIteration MathCompMeasure.
From PTree.Examples Require Import RealBernoulliMathComp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.
#[local] Open Scope classical_set_scope.
#[local] Open Scope ereal_scope.

Section MathCompVonNeumann.
Context (R : realType).
Local Notation M := (MathCompKernelMeasure R).

Definition mathcomp_vn_round_result (b1 b2 : bool) : unit + bool :=
  if b1 == b2 then inl tt else inr b1.

Definition mathcomp_p_coin (p : R) : M bool :=
  @mathcomp_bernoulli R p.

Definition mathcomp_vn_transition (p : R) : M (unit + bool) :=
  meas_bind (mathcomp_p_coin p) (fun b1 =>
    meas_bind (mathcomp_p_coin p) (fun b2 =>
      meas_ret (mathcomp_vn_round_result b1 b2))).

Definition mathcomp_vn_step (p : R) (_ : unit) :
    ptree real_mathcomp_coinE M (unit + bool) :=
  Prob (mathcomp_p_coin p) (fun b1 =>
    Prob (mathcomp_p_coin p) (fun b2 =>
      Ret (mathcomp_vn_round_result b1 b2))).

Definition mathcomp_von_neumann (p : R) :
    ptree real_mathcomp_coinE M bool :=
  PTree.iter (mathcomp_vn_step p) tt.

Definition mathcomp_vn_retry (p : R) : R :=
  p * p + (1 - p) * (1 - p).

Definition mathcomp_vn_success (p : R) : R := p * (1 - p).

Lemma mathcomp_vn_escape p :
  (1 - mathcomp_vn_retry p = 2 * mathcomp_vn_success p)%R.
Proof.
  rewrite /mathcomp_vn_retry /mathcomp_vn_success.
  ring.
Qed.

Lemma mathcomp_vn_success_pos p :
  (0 < p < 1)%R -> (0 < mathcomp_vn_success p)%R.
Proof.
  move=> /andP [p0 p1]. rewrite /mathcomp_vn_success.
  exact: mulr_gt0 p0 (subr_gt0.mpr p1).
Qed.

Lemma mathcomp_vn_retry_nonnegative p :
  (0 <= mathcomp_vn_retry p)%R.
Proof.
  rewrite /mathcomp_vn_retry.
  apply: addr_ge0; apply: sqr_ge0.
Qed.

Lemma mathcomp_vn_retry_lt1 p :
  (0 < p < 1)%R -> (mathcomp_vn_retry p < 1)%R.
Proof.
  move=> Hp.
  have Hs := mathcomp_vn_success_pos Hp.
  rewrite -subr_gt0 -mathcomp_vn_escape.
  exact: mulr_gt0 (ltr0Sn 2) Hs.
Qed.

Lemma mathcomp_vn_transition_mass p (p01 : (0 <= p <= 1)%R)
    (U : set (mc_carrier (unit + bool))) : measurable U ->
  mathcomp_kernel_root (mathcomp_vn_transition p) U =
    p%:E * (p%:E * mathcomp_kernel_root (meas_ret (inl tt)) U +
      (1 - p)%:E * mathcomp_kernel_root (meas_ret (inr true)) U) +
    (1 - p)%:E *
      (p%:E * mathcomp_kernel_root (meas_ret (inr false)) U +
       (1 - p)%:E * mathcomp_kernel_root (meas_ret (inl tt)) U).
Proof.
  move=> mU. rewrite /mathcomp_vn_transition /mathcomp_p_coin.
  rewrite !mathcomp_kernel_bind_bernoulli //.
Qed.

Lemma mathcomp_vn_true_mass p (p01 : (0 <= p <= 1)%R) :
  mathcomp_kernel_root (mathcomp_vn_transition p)
      [set MCValue (inr true)] = (mathcomp_vn_success p)%:E.
Proof.
  rewrite mathcomp_vn_transition_mass //.
  rewrite !mathcomp_kernel_root_ret /dirac /= !indicE /=.
  rewrite !mule0 !mul1e !add0e !adde0 -EFinM.
  reflexivity.
Qed.

Lemma mathcomp_vn_false_mass p (p01 : (0 <= p <= 1)%R) :
  mathcomp_kernel_root (mathcomp_vn_transition p)
      [set MCValue (inr false)] = (mathcomp_vn_success p)%:E.
Proof.
  rewrite mathcomp_vn_transition_mass //.
  rewrite !mathcomp_kernel_root_ret /dirac /= !indicE /=.
  rewrite !mule0 !mul1e !add0e !adde0 -EFinM.
  reflexivity.
Qed.

Lemma mathcomp_vn_retry_mass p (p01 : (0 <= p <= 1)%R) :
  mathcomp_kernel_root (mathcomp_vn_transition p)
      [set MCValue (inl tt)] = (mathcomp_vn_retry p)%:E.
Proof.
  rewrite mathcomp_vn_transition_mass //.
  rewrite !mathcomp_kernel_root_ret /dirac /= !indicE /=.
  rewrite !mule0 !mul1e !add0e !adde0 -!EFinM -EFinD.
  reflexivity.
Qed.

Lemma mathcomp_vn_transition_total p (p01 : (0 <= p <= 1)%R) :
  meas_total (mathcomp_vn_transition p).
Proof.
  rewrite /meas_total /MathCompKernelMeasureOmegaInterface
    /mathcomp_kernel_total mathcomp_vn_transition_mass //.
  rewrite !mathcomp_kernel_root_ret /dirac /= !indicE /= !mul1e.
  rewrite -!EFinM -!EFinD.
  congr (_%:E). ring.
Qed.

Definition mathcomp_vn_fair : M bool := @mathcomp_bernoulli R (1 / 2).

Fixpoint mathcomp_vn_result_approx
    (p : R) (fuel : nat) : M bool :=
  match fuel with
  | 0 => meas_zero
  | fuel'.+1 =>
      meas_bind (mathcomp_vn_transition p) (fun next =>
        match next with
        | inl _ => mathcomp_vn_result_approx p fuel'
        | inr b => meas_ret b
        end)
  end.

Lemma mathcomp_vn_approx_is_iter p fuel :
  mathcomp_vn_result_approx p fuel =
  meas_iter_approx fuel (fun _ : unit => mathcomp_vn_transition p) tt.
Proof. by elim: fuel=> [|fuel IH] //=; rewrite IH. Qed.

Lemma mathcomp_vn_approx_mass p (p01 : (0 <= p <= 1)%R)
    fuel (U : set (mc_carrier bool)) : measurable U ->
  mathcomp_kernel_root (mathcomp_vn_result_approx p fuel.+1) U =
    (mathcomp_vn_retry p)%:E *
      mathcomp_kernel_root (mathcomp_vn_result_approx p fuel) U +
    (mathcomp_vn_success p)%:E * mathcomp_kernel_root (meas_ret true) U +
    (mathcomp_vn_success p)%:E * mathcomp_kernel_root (meas_ret false) U.
Proof.
  move=> mU. cbn [mathcomp_vn_result_approx].
  rewrite mathcomp_kernel_root_bind.
  (* The transition has only the three returned points; integrate by first
     exposing its two Bernoulli draws. *)
  rewrite /mathcomp_vn_transition /mathcomp_p_coin.
  rewrite mathcomp_kernel_root_bind.
  rewrite (mathcomp_kernel_bind_bernoulli p p01) //.
  rewrite !(mathcomp_kernel_bind_bernoulli p p01) //.
  rewrite !mathcomp_kernel_root_ret /dirac /= !indicE /=.
  rewrite /mathcomp_vn_retry /mathcomp_vn_success.
  rewrite -!EFinM -!EFinD.
  congr (_%:E). ring.
Qed.

Lemma mathcomp_vn_fair_mass (U : set (mc_carrier bool)) : measurable U ->
  mathcomp_kernel_root mathcomp_vn_fair U =
    (1 / 2 : R)%:E * mathcomp_kernel_root (meas_ret true) U +
    (1 / 2 : R)%:E * mathcomp_kernel_root (meas_ret false) U.
Proof.
  move=> mU. apply mathcomp_kernel_bind_bernoulli=> //.
  apply/andP; split; first exact: divr_ge0.
  rewrite ler_pdivrMr; last by rewrite ltr0n.
  by rewrite mul1r ler1n.
Qed.

Lemma mathcomp_vn_success_pair p (U : set (mc_carrier bool))
    (mU : measurable U) :
  (mathcomp_vn_success p)%:E * mathcomp_kernel_root (meas_ret true) U +
  (mathcomp_vn_success p)%:E * mathcomp_kernel_root (meas_ret false) U =
  (1 - mathcomp_vn_retry p)%:E *
    mathcomp_kernel_root mathcomp_vn_fair U.
Proof.
  rewrite mathcomp_vn_fair_mass // mathcomp_vn_escape.
  rewrite -!EFinM -!EFinD.
  congr (_%:E). ring.
Qed.

Lemma mathcomp_vn_approx_closed p (p01 : (0 <= p <= 1)%R)
    fuel (U : set (mc_carrier bool)) : measurable U -> ~ U MCBottom ->
  mathcomp_kernel_root (mathcomp_vn_result_approx p fuel) U =
  (1 - mathcomp_vn_retry p ^+ fuel)%:E *
    mathcomp_kernel_root mathcomp_vn_fair U.
Proof.
  move=> mU nbot. elim: fuel=> [|fuel IH].
  - rewrite /= /meas_zero /MathCompKernelMeasureOmegaInterface
      /mathcomp_kernel_zero /mathcomp_kernel_root
      /mathcomp_source_kernel /mathcomp_source_measure
      /mathcomp_bottom_measure /dirac /= expr0 subrr EFin0 mule0.
    have Hnot : MCBottom \notin U by rewrite notin_setE.
    rewrite indicE (negbTE Hnot). reflexivity.
  - rewrite mathcomp_vn_approx_mass // IH
      (mathcomp_vn_success_pair p U mU) exprS.
    set r := mathcomp_vn_retry p.
    set z := mathcomp_kernel_root mathcomp_vn_fair U.
    rewrite -muleDl -!EFinD -!EFinM.
    congr (_%:E * z). ring.
Qed.

Lemma mathcomp_vn_scale_cvg p (Hp : (0 < p < 1)%R) :
  (fun fuel => (1 - mathcomp_vn_retry p ^+ fuel)%R)
    @ \oo --> (1 : R)%R.
Proof.
  have Hr0 := mathcomp_vn_retry_nonnegative p.
  have Hr1 := mathcomp_vn_retry_lt1 Hp.
  have Hpow : (GRing.exp (mathcomp_vn_retry p) : R ^nat)
      @ \oo --> (0 : R)%R.
  { apply: cvg_expr. rewrite ger0_norm //.
    exact: Hr1. }
  have := cvgB (cvg_cst (1 : R)%R) Hpow.
  by rewrite subr0.
Qed.

Lemma mathcomp_vn_scale_sup p (Hp : (0 < p < 1)%R) :
  ereal_sup (range (fun fuel =>
    (1 - mathcomp_vn_retry p ^+ fuel)%:E)) = 1.
Proof.
  have Hr0 := mathcomp_vn_retry_nonnegative p.
  have Hr1 := mathcomp_vn_retry_lt1 Hp.
  have Hnd : nondecreasing_seq (fun fuel =>
      (1 - mathcomp_vn_retry p ^+ fuel)%:E).
  { apply/nondecreasing_seqP=> fuel. rewrite lee_fin.
    apply: lerB; first exact: lexx.
    rewrite exprS.
    have Hrle : (mathcomp_vn_retry p <= 1)%R := ltW Hr1.
    have Hpow := exprn_ge0 fuel Hr0.
    exact: ler_wpM2r Hpow Hrle. }
  have Hsup := ereal_nondecreasing_cvgn Hnd.
  have HE : (fun fuel =>
      (1 - mathcomp_vn_retry p ^+ fuel)%:E)
      @ \oo --> (1 : R)%:E.
  { apply: cvg_EFin; first exact: nearW.
    exact: mathcomp_vn_scale_cvg. }
  exact: cvg_unique Hsup HE.
Qed.

Lemma ereal_sup_scale_finite (z : \bar R)
    (Hz : (0 <= z)%E) (Hzfin : z < +oo) p (Hp : (0 < p < 1)%R) :
  ereal_sup (range (fun fuel =>
    (1 - mathcomp_vn_retry p ^+ fuel)%:E * z)) = z.
Proof.
  have Hscale := mathcomp_vn_scale_sup Hp.
  have Hnd : nondecreasing_seq (fun fuel =>
      (1 - mathcomp_vn_retry p ^+ fuel)%:E * z).
  { apply/nondecreasing_seqP=> fuel.
    apply lee_pmul=> //.
    rewrite lee_fin. apply: lerB; first exact: lexx.
    rewrite exprS.
    have Hr0 := mathcomp_vn_retry_nonnegative p.
    have Hr1 := mathcomp_vn_retry_lt1 Hp.
    exact: ler_wpM2r (exprn_ge0 fuel Hr0) (ltW Hr1). }
  have Hsup := ereal_nondecreasing_cvgn Hnd.
  have Hcvg : (fun fuel =>
      (1 - mathcomp_vn_retry p ^+ fuel)%:E * z)
      @ \oo --> 1 * z.
  { apply: cvgM; last exact: cvg_cst.
    apply: cvg_EFin; first exact: nearW.
    exact: mathcomp_vn_scale_cvg. }
  rewrite mul1e. exact: cvg_unique Hsup Hcvg.
Qed.

Theorem mathcomp_vn_iteration_lub p (Hp : (0 < p < 1)%R) :
  meas_iter (fun _ : unit => mathcomp_vn_transition p) tt
    mathcomp_vn_fair.
Proof.
  have p01 : (0 <= p <= 1)%R := /andP [ltW Hp.1, ltW Hp.2].
  move=> U mU nbot.
  rewrite -mathcomp_vn_approx_is_iter.
  have -> : range (fun fuel => mathcomp_kernel_root
      (mathcomp_vn_result_approx p fuel) U) =
      range (fun fuel =>
        (1 - mathcomp_vn_retry p ^+ fuel)%:E *
          mathcomp_kernel_root mathcomp_vn_fair U).
  { apply/seteqP; split=> z [fuel _ <-]; exists fuel=> //.
    - symmetry. exact: mathcomp_vn_approx_closed.
    - exact: mathcomp_vn_approx_closed. }
  symmetry. apply ereal_sup_scale_finite=> //.
  - exact: measure_ge0.
  - exact: lte_le_trans (mathcomp_kernel_root_le_one _) (by rewrite ltry).
Qed.

Theorem mathcomp_von_neumann_ast p (Hp : (0 < p < 1)%R) :
  meas_iter_ast (fun _ : unit => mathcomp_vn_transition p) tt.
Proof.
  eapply meas_iter_total_ast.
  - exact: mathcomp_vn_iteration_lub Hp.
  - apply mathcomp_bernoulli_total.
    apply/andP; split; first exact: divr_ge0.
    rewrite ler_pdivrMr; last by rewrite ltr0n.
    by rewrite mul1r ler1n.
Qed.

Definition mathcomp_vn_heads : M (aphead real_mathcomp_coinE M bool) :=
  meas_bind mathcomp_vn_fair (fun b =>
    meas_ret (APHRet b : aphead real_mathcomp_coinE M bool)).

Lemma mathcomp_vn_step_frontier p i :
  apfrontier (observe (mathcomp_vn_step p i))
    (meas_bind (mathcomp_vn_transition p) (fun next =>
      meas_ret (APHRet next :
        aphead real_mathcomp_coinE M (unit + bool)))).
Proof.
  destruct i. unfold mathcomp_vn_step, mathcomp_vn_transition.
  cbn. apply (APFProb
    (front := fun b1 => meas_bind (mathcomp_p_coin p) (fun b2 =>
      meas_ret (APHRet (mathcomp_vn_round_result b1 b2) :
        aphead real_mathcomp_coinE M (unit + bool))))
    (Good := fun _ => True)); first apply meas_ae_true.
  move=> b1 _. apply (APFProb
    (front := fun b2 =>
      meas_ret (APHRet (mathcomp_vn_round_result b1 b2) :
        aphead real_mathcomp_coinE M (unit + bool)))
    (Good := fun _ => True)); first apply meas_ae_true.
  move=> b2 _. constructor.
Qed.

Theorem mathcomp_von_neumann_frontier p (Hp : (0 < p < 1)%R) :
  aufrontier (observe (mathcomp_von_neumann p)) mathcomp_vn_heads.
Proof.
  unfold mathcomp_von_neumann, mathcomp_vn_heads.
  eapply (AUFIter
    (transition := fun _ : unit => mathcomp_vn_transition p)
    (out := mathcomp_vn_fair)).
  - exact: mathcomp_vn_step_frontier.
  - exact: mathcomp_vn_iteration_lub Hp.
  - apply mathcomp_bernoulli_total.
    apply/andP; split; first exact: divr_ge0.
    rewrite ler_pdivrMr; last by rewrite ltr0n.
    by rewrite mul1r ler1n.
Qed.

End MathCompVonNeumann.
