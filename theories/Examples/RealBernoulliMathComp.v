Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Ring Field.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssralg ssrnum
  order rat reals normedtype classical_sets.
From mathcomp Require Import numfun.
From mathcomp.analysis Require Import topology sequences ereal measure.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift MeasureIteration MathCompMeasure.
From PTree.Examples Require Import RealBernoulliOracle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.Theory.
Import numFieldNormedType.Exports.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.
#[local] Open Scope classical_set_scope.

Unset Automatic Proposition Inductives.
Variant real_mathcomp_coinE : Type -> Type := .

Section RealOracleBackend.
Context (R : realType).

Local Notation M := (MathCompKernelMeasure R).

Definition mathcomp_half_coin : M bool :=
  @mathcomp_bernoulli R (1 / 2 : R).

Definition mathcomp_oracle_transition
    (qbit : binary_oracle) (n : nat) : M (nat + bool) :=
  meas_bind mathcomp_half_coin (fun random =>
    if qbit n then
      if random then meas_ret (inl n.+1) else meas_ret (inr true)
    else
      if random then meas_ret (inr false) else meas_ret (inl n.+1)).

Definition mathcomp_oracle_step
    (qbit : binary_oracle) (n : nat) :
    ptree real_mathcomp_coinE M (nat + bool) :=
  Prob (mathcomp_oracle_transition qbit n)
    (fun next : nat + bool => Ret next).

Definition mathcomp_binary_oracle_coin (qbit : binary_oracle) :
    ptree real_mathcomp_coinE M bool :=
  PTree.iter (mathcomp_oracle_step qbit) 0.

(** The direct specification program samples from MathComp's genuine
    real-valued Bernoulli probability measure. *)
Definition mathcomp_direct_bernoulli (q : R) :
    ptree real_mathcomp_coinE M bool :=
  Prob (@mathcomp_bernoulli R q) (fun b : bool => Ret b).

(** Concrete interpretation of the abstract oracle representation from
    [RealBernoulliOracle]: rational binary prefixes converge in [R]. *)
Definition mathcomp_oracle_represents
    (qbit : binary_oracle) (q : R) : Prop :=
  (fun n => ratr (oracle_prefix qbit n)) @ \oo --> q.

(** Result-valued absorbing approximants.  Unlike a frontier measure, this
    stays in [M bool] and therefore avoids raising the carrier universe; it is
    the semantic chain used for AST and the direct Bernoulli comparison. *)
Definition mathcomp_oracle_result_approx
    (qbit : binary_oracle) (fuel n : nat) : M bool :=
  meas_iter_approx fuel (mathcomp_oracle_transition qbit) n.

Definition mathcomp_binary_oracle_denotes
    (qbit : binary_oracle) (out : M bool) : Prop :=
  meas_iter (mathcomp_oracle_transition qbit) 0 out.

Definition mathcomp_binary_oracle_ast (qbit : binary_oracle) : Prop :=
  meas_iter_ast (mathcomp_oracle_transition qbit) 0.

(** A reassociated form of the same intended approximation, exposing the
    fair Bernoulli draw at the outermost bind.  Its event masses can be
    calculated directly by [mathcomp_kernel_bind_bernoulli].  Equating this
    chain with [mathcomp_oracle_result_approx] is precisely the kernel-bind
    associativity obligation. *)
Fixpoint mathcomp_oracle_unfolded_approx
    (qbit : binary_oracle) (fuel n : nat) : M bool :=
  match fuel with
  | 0 => meas_zero
  | fuel'.+1 =>
      meas_bind mathcomp_half_coin (fun random =>
        if qbit n then
          if random then
            mathcomp_oracle_unfolded_approx qbit fuel' n.+1
          else meas_ret true
        else
          if random then meas_ret false
          else mathcomp_oracle_unfolded_approx qbit fuel' n.+1)
  end.

Local Open Scope ereal_scope.

Lemma mathcomp_oracle_unfolded_mass qbit fuel n
    (U : set (mc_carrier bool)) : measurable U ->
  mathcomp_kernel_root
      (mathcomp_oracle_unfolded_approx qbit fuel.+1 n) U =
    if qbit n then
      (1 / 2 : R)%:E * mathcomp_kernel_root
        (mathcomp_oracle_unfolded_approx qbit fuel n.+1) U +
      (1 - (1 / 2 : R))%:E *
        mathcomp_kernel_root (meas_ret true) U
    else
      (1 / 2 : R)%:E * mathcomp_kernel_root (meas_ret false) U +
      (1 - (1 / 2 : R))%:E * mathcomp_kernel_root
        (mathcomp_oracle_unfolded_approx qbit fuel n.+1) U.
Proof.
  move=> mU. cbn [mathcomp_oracle_unfolded_approx].
  set k := fun random : bool =>
    if qbit n then
      if random then mathcomp_oracle_unfolded_approx qbit fuel n.+1
      else meas_ret true
    else if random then meas_ret false
      else mathcomp_oracle_unfolded_approx qbit fuel n.+1.
  change (mathcomp_kernel_root
    (mathcomp_kernel_bind mathcomp_half_coin k) U =
    if qbit n then
      (1 / 2 : R)%:E * mathcomp_kernel_root
        (mathcomp_oracle_unfolded_approx qbit fuel n.+1) U +
      (1 - (1 / 2 : R))%:E *
        mathcomp_kernel_root (meas_ret true) U
    else
      (1 / 2 : R)%:E * mathcomp_kernel_root (meas_ret false) U +
      (1 - (1 / 2 : R))%:E * mathcomp_kernel_root
        (mathcomp_oracle_unfolded_approx qbit fuel n.+1) U).
  subst k.
  rewrite /mathcomp_half_coin mathcomp_kernel_bind_bernoulli.
  - by case: (qbit n).
  - apply/andP; split; first exact: divr_ge0.
    rewrite ler_pdivrMr; last by rewrite ltr0n.
    by rewrite mul1r ler1n.
  - exact mU.
Qed.

Fixpoint mathcomp_oracle_prefix_from
    (qbit : binary_oracle) (n fuel : nat) : R :=
  match fuel with
  | 0 => 0
  | fuel'.+1 =>
      ((if qbit n then (1 / 2 : R) else 0) +
       (1 / 2 : R) * mathcomp_oracle_prefix_from qbit n.+1 fuel')%R
  end.

Fixpoint mathcomp_oracle_false_prefix_from
    (qbit : binary_oracle) (n fuel : nat) : R :=
  match fuel with
  | 0 => 0
  | fuel'.+1 =>
      ((if qbit n then 0 else (1 / 2 : R)) +
       (1 / 2 : R) *
         mathcomp_oracle_false_prefix_from qbit n.+1 fuel')%R
  end.

Lemma mathcomp_half_complement : (1 - (1 / 2 : R) = 1 / 2)%R.
Proof.
  apply/eqP. rewrite subr_eq.
  rewrite -mulrDl.
  change ((1 : R) == ((2 : R) / (2 : R)))%R.
  by rewrite divrr // unitfE pnatr_eq0.
Qed.

Lemma mathcomp_oracle_unfolded_true_mass qbit fuel n :
  mathcomp_kernel_root
      (mathcomp_oracle_unfolded_approx qbit fuel n)
      [set MCValue true] =
  (mathcomp_oracle_prefix_from qbit n fuel)%:E.
Proof.
  elim: fuel n=> [|fuel IH] n.
  - rewrite /= /mathcomp_kernel_zero /mathcomp_kernel_root
      /mathcomp_source_kernel /mathcomp_source_measure
      /mathcomp_bottom_measure /dirac /=.
    change (((\1_[set MCValue true] MCBottom : R)%:E) = 0).
    rewrite indicE.
    have Hnot : MCBottom \notin [set MCValue true] by rewrite notin_setE.
    by rewrite (negbTE Hnot).
  - rewrite mathcomp_oracle_unfolded_mass //.
    rewrite IH !mathcomp_kernel_root_ret /dirac /= !indicE /=
      mathcomp_half_complement.
    case: (qbit n)=> /=; rewrite ?mul1e ?mule0 ?adde0 ?add0e.
    all: rewrite -?EFinM -?EFinD.
    all: congr (_%:E).
    all: by rewrite ?addrC.
Qed.

Lemma mathcomp_oracle_unfolded_false_mass qbit fuel n :
  mathcomp_kernel_root
      (mathcomp_oracle_unfolded_approx qbit fuel n)
      [set MCValue false] =
  (mathcomp_oracle_false_prefix_from qbit n fuel)%:E.
Proof.
  elim: fuel n=> [|fuel IH] n.
  - rewrite /= /mathcomp_kernel_zero /mathcomp_kernel_root
      /mathcomp_source_kernel /mathcomp_source_measure
      /mathcomp_bottom_measure /dirac /=.
    change (((\1_[set MCValue false] MCBottom : R)%:E) = 0).
    rewrite indicE.
    have Hnot : MCBottom \notin [set MCValue false] by rewrite notin_setE.
    by rewrite (negbTE Hnot).
  - rewrite mathcomp_oracle_unfolded_mass //.
    rewrite IH !mathcomp_kernel_root_ret /dirac /= !indicE /=
      mathcomp_half_complement.
    case: (qbit n)=> /=; rewrite ?mul1e ?mule0 ?adde0 ?add0e.
    all: rewrite -?EFinM -?EFinD.
    all: congr (_%:E).
    all: by rewrite ?addrC.
Qed.

Lemma mathcomp_oracle_prefix_from_rat qbit fuel n :
  mathcomp_oracle_prefix_from qbit n fuel =
  ratr (oracle_prefix_from qbit n fuel).
Proof.
  elim: fuel n=> [|fuel IH] n; first by rewrite /= rmorph0.
  rewrite /= IH.
  case: (qbit n); rewrite /=.
  all: rewrite ?rmorphD ?rmorphM ?fmorph_div ?rmorph1 ?ratr_nat.
  all: reflexivity.
Qed.

Lemma mathcomp_oracle_prefix_nonnegative qbit fuel n :
  (0 <= mathcomp_oracle_prefix_from qbit n fuel)%R.
Proof.
  elim: fuel n=> [|fuel IH] n; first exact: lexx.
  rewrite /=. have Hhalf : (0 <= (1 / 2 : R))%R := divr_ge0 _ _.
  case: (qbit n)=> /=.
  - exact: addr_ge0 Hhalf (mulr_ge0 Hhalf (IH n.+1)).
  - exact: mulr_ge0 Hhalf (IH n.+1).
Qed.

Lemma mathcomp_oracle_prefix_step_le qbit fuel n :
  (mathcomp_oracle_prefix_from qbit n fuel <=
   mathcomp_oracle_prefix_from qbit n fuel.+1)%R.
Proof.
  elim: fuel n=> [|fuel IH] n.
  - exact: mathcomp_oracle_prefix_nonnegative.
  - rewrite /=. have Hhalf : (0 <= (1 / 2 : R))%R := divr_ge0 _ _.
    have Htail := ler_wpM2l Hhalf (IH n.+1).
    case: (qbit n)=> /=.
    + exact: lerD Htail.
    + exact: Htail.
Qed.

Lemma mathcomp_oracle_prefix_nondecreasing qbit n :
  nondecreasing_seq (fun fuel =>
    (mathcomp_oracle_prefix_from qbit n fuel)%:E).
Proof.
  apply/nondecreasing_seqP=> fuel.
  by rewrite lee_fin; exact: mathcomp_oracle_prefix_step_le.
Qed.

Lemma mathcomp_oracle_false_prefix_nonnegative qbit fuel n :
  (0 <= mathcomp_oracle_false_prefix_from qbit n fuel)%R.
Proof.
  elim: fuel n=> [|fuel IH] n; first exact: lexx.
  rewrite /=. have Hhalf : (0 <= (1 / 2 : R))%R := divr_ge0 _ _.
  case: (qbit n)=> /=.
  - exact: mulr_ge0 Hhalf (IH n.+1).
  - exact: addr_ge0 Hhalf (mulr_ge0 Hhalf (IH n.+1)).
Qed.

Lemma mathcomp_oracle_false_prefix_step_le qbit fuel n :
  (mathcomp_oracle_false_prefix_from qbit n fuel <=
   mathcomp_oracle_false_prefix_from qbit n fuel.+1)%R.
Proof.
  elim: fuel n=> [|fuel IH] n.
  - exact: mathcomp_oracle_false_prefix_nonnegative.
  - rewrite /=. have Hhalf : (0 <= (1 / 2 : R))%R := divr_ge0 _ _.
    have Htail := ler_wpM2l Hhalf (IH n.+1).
    case: (qbit n)=> /=.
    + exact: Htail.
    + exact: lerD Htail.
Qed.

Lemma mathcomp_oracle_false_prefix_nondecreasing qbit n :
  nondecreasing_seq (fun fuel =>
    (mathcomp_oracle_false_prefix_from qbit n fuel)%:E).
Proof.
  apply/nondecreasing_seqP=> fuel.
  by rewrite lee_fin; exact: mathcomp_oracle_false_prefix_step_le.
Qed.

Lemma mathcomp_oracle_prefix_sup qbit q :
  mathcomp_oracle_represents qbit q ->
  ereal_sup (range (fun fuel =>
    (mathcomp_oracle_prefix_from qbit 0 fuel)%:E)) = q%:E.
Proof.
  move=> Hrep.
  have Hsup := ereal_nondecreasing_cvgn
    (mathcomp_oracle_prefix_nondecreasing qbit 0).
  have Hq : (fun fuel =>
      (mathcomp_oracle_prefix_from qbit 0 fuel)%:E) @ \oo --> q%:E.
  { apply: cvg_EFin; first exact: nearW.
    change (fun fuel => mathcomp_oracle_prefix_from qbit 0 fuel)
      @ \oo --> q.
    under eq_cvg do rewrite mathcomp_oracle_prefix_from_rat.
    exact Hrep. }
  apply: cvg_lim Hsup.
  exact Hq.
Qed.

Lemma mathcomp_half_expr_step_le fuel :
  (((1 / 2 : R) ^+ fuel.+1) <= (1 / 2 : R) ^+ fuel)%R.
Proof.
  rewrite exprS.
  have Hhalf0 : (0 <= (1 / 2 : R))%R := divr_ge0 _ _.
  have Hhalf1 : ((1 / 2 : R) <= 1)%R.
  { rewrite ler_pdivrMr; last by rewrite ltr0n.
    by rewrite mul1r ler1n. }
  have H := ler_wpM2l (exprn_ge0 fuel Hhalf0) Hhalf1.
  by rewrite mulr1 in H.
Qed.

Lemma mathcomp_total_nondecreasing :
  nondecreasing_seq (fun fuel =>
    (1 - (1 / 2 : R) ^+ fuel)%:E).
Proof.
  apply/nondecreasing_seqP=> fuel. rewrite lee_fin lerBlDr subrK.
  exact: mathcomp_half_expr_step_le.
Qed.

Lemma mathcomp_total_cvg :
  (fun fuel => (1 - (1 / 2 : R) ^+ fuel)%R) @ \oo --> 1.
Proof.
  have Hpow : (GRing.exp (1 / 2 : R) : R ^nat) @ \oo --> 0.
  { apply: cvg_expr. rewrite ger0_norm; first last.
    - exact: divr_ge0.
    - rewrite ltr_pdivrMr; last by rewrite ltr0n.
      by rewrite mul1r ltr1n. }
  have := cvgB (cvg_cst (1 : R)) Hpow.
  by rewrite subr0.
Qed.

Lemma mathcomp_total_sup :
  ereal_sup (range (fun fuel =>
    (1 - (1 / 2 : R) ^+ fuel)%:E)) = 1.
Proof.
  have Hsup := ereal_nondecreasing_cvgn mathcomp_total_nondecreasing.
  have HE : (fun fuel => (1 - (1 / 2 : R) ^+ fuel)%:E)
      @ \oo --> (1 : R)%:E.
  { apply: cvg_EFin; first exact: nearW. exact mathcomp_total_cvg. }
  apply: cvg_lim Hsup. exact HE.
Qed.

Lemma mathcomp_oracle_false_prefix_sup qbit q :
  mathcomp_oracle_represents qbit q ->
  ereal_sup (range (fun fuel =>
    (mathcomp_oracle_false_prefix_from qbit 0 fuel)%:E)) =
  (1 - q)%:E.
Proof.
  move=> Hrep.
  have Hsup := ereal_nondecreasing_cvgn
    (mathcomp_oracle_false_prefix_nondecreasing qbit 0).
  have Htrue : (fun fuel => mathcomp_oracle_prefix_from qbit 0 fuel)
      @ \oo --> q.
  { under eq_cvg do rewrite mathcomp_oracle_prefix_from_rat.
    exact Hrep. }
  have Hfalse : (fun fuel =>
      mathcomp_oracle_false_prefix_from qbit 0 fuel) @ \oo --> (1 - q)%R.
  { under eq_cvg do rewrite mathcomp_oracle_false_prefixE.
    exact: cvgB mathcomp_total_cvg Htrue. }
  have HE : (fun fuel =>
      (mathcomp_oracle_false_prefix_from qbit 0 fuel)%:E)
      @ \oo --> (1 - q)%:E.
  { apply: cvg_EFin; first exact: nearW. exact Hfalse. }
  apply: cvg_lim Hsup. exact HE.
Qed.

Lemma mathcomp_kernel_ret_returned (b : bool) :
  mathcomp_kernel_root (meas_ret b) (@mc_returned bool) = 1.
Proof.
  rewrite mathcomp_kernel_root_ret /dirac /= indicE.
  have Hin : MCValue b \in (@mc_returned bool) by [].
  by rewrite asboolT.
Qed.

Lemma mathcomp_kernel_zero_returned :
  mathcomp_kernel_root (@meas_zero M _ _ bool) (@mc_returned bool) = 0.
Proof.
  rewrite /meas_zero /MathCompKernelMeasureOmegaInterface
    /mathcomp_kernel_zero /mathcomp_kernel_root
    /mathcomp_source_kernel /mathcomp_source_measure
    /mathcomp_bottom_measure /dirac /= indicE.
  have Hnot : MCBottom \notin (@mc_returned bool) by rewrite notin_setE.
  by rewrite (negbTE Hnot).
Qed.

Lemma mathcomp_half_contract a :
  ((1 / 2 : R) + (1 / 2) * (1 - a) =
    1 - (1 / 2) * a)%R.
Proof.
  rewrite mulrBr mulr1.
  rewrite [((1 / 2 : R) +
      ((1 / 2 : R) - (1 / 2 : R) * a))%R]addrC -addrA.
  rewrite [(- ((1 / 2 : R) * a) + (1 / 2 : R))%R]addrC addrA.
  have Hhalf : ((1 / 2 : R) + 1 / 2 = 1)%R.
  { rewrite -mulrDl.
    change (((2 : R) / (2 : R)) = 1)%R.
    by rewrite divrr // unitfE pnatr_eq0. }
  by rewrite Hhalf.
Qed.

Lemma mathcomp_oracle_prefix_split qbit fuel n :
  (mathcomp_oracle_prefix_from qbit n fuel +
   mathcomp_oracle_false_prefix_from qbit n fuel =
   1 - (1 / 2 : R) ^+ fuel)%R.
Proof.
  elim: fuel n=> [|fuel IH] n; first by rewrite /= expr0 subrr.
  rewrite /=. case: (qbit n)=> /=.
  - rewrite addrA -mulrDr IH exprS.
    exact: mathcomp_half_contract.
  - rewrite addrCA -mulrDr IH exprS.
    exact: mathcomp_half_contract.
Qed.

Lemma mathcomp_oracle_false_prefixE qbit fuel n :
  mathcomp_oracle_false_prefix_from qbit n fuel =
  (1 - (1 / 2 : R) ^+ fuel -
   mathcomp_oracle_prefix_from qbit n fuel)%R.
Proof.
  apply: (addrI (mathcomp_oracle_prefix_from qbit n fuel)).
  rewrite subrK.
  exact: mathcomp_oracle_prefix_split.
Qed.

Lemma mathcomp_oracle_unfolded_total_mass qbit fuel n :
  mathcomp_kernel_root
      (mathcomp_oracle_unfolded_approx qbit fuel n)
      (@mc_returned bool) =
  (1 - (1 / 2 : R) ^+ fuel)%:E.
Proof.
  elim: fuel n=> [|fuel IH] n.
  - by rewrite /= mathcomp_kernel_zero_returned expr0 subrr.
  - rewrite mathcomp_oracle_unfolded_mass // IH
      !mathcomp_kernel_ret_returned mathcomp_half_complement.
    case: (qbit n); rewrite /= ?mul1e.
    all: rewrite -?EFinM -?EFinD.
    all: congr (_%:E); rewrite exprS.
    - rewrite addrC. exact: mathcomp_half_contract.
    - exact: mathcomp_half_contract.
Qed.

Lemma mathcomp_oracle_result_unfolded_eq qbit fuel n :
  mathcomp_kernel_eq
    (mathcomp_oracle_result_approx qbit fuel n)
    (mathcomp_oracle_unfolded_approx qbit fuel n).
Proof.
  elim: fuel n=> [|fuel IH] n.
  - exact: mathcomp_kernel_eq_refl.
  - set f := fun random : bool =>
      if qbit n then
        if random then meas_ret (inl n.+1) else meas_ret (inr true)
      else if random then meas_ret (inr false) else meas_ret (inl n.+1).
    set g := fun next : nat + bool =>
      match next with
      | inl n' => mathcomp_oracle_result_approx qbit fuel n'
      | inr b => meas_ret b
      end.
    set h := fun random : bool =>
      if qbit n then
        if random then mathcomp_oracle_unfolded_approx qbit fuel n.+1
        else meas_ret true
      else if random then meas_ret false
        else mathcomp_oracle_unfolded_approx qbit fuel n.+1.
    change (mathcomp_kernel_eq
      (mathcomp_kernel_bind (mathcomp_kernel_bind mathcomp_half_coin f) g)
      (mathcomp_kernel_bind mathcomp_half_coin h)).
    eapply mathcomp_kernel_eq_trans.
    + exact: mathcomp_kernel_bind_assoc.
    + apply: mathcomp_kernel_bind_proper_k=> random.
      subst f g h. case E: (qbit n); case: random=> /=.
      * eapply mathcomp_kernel_eq_trans.
        -- exact: mathcomp_kernel_bind_ret_l.
        -- exact: IH.
      * exact: mathcomp_kernel_bind_ret_l.
      * exact: mathcomp_kernel_bind_ret_l.
      * eapply mathcomp_kernel_eq_trans.
        -- exact: mathcomp_kernel_bind_ret_l.
        -- exact: IH.
Qed.

Lemma mathcomp_oracle_result_true_mass qbit fuel n :
  mathcomp_kernel_root (mathcomp_oracle_result_approx qbit fuel n)
      [set MCValue true] =
  (mathcomp_oracle_prefix_from qbit n fuel)%:E.
Proof.
  rewrite (mathcomp_oracle_result_unfolded_eq qbit fuel n) //.
  exact: mathcomp_oracle_unfolded_true_mass.
Qed.

Lemma mathcomp_oracle_result_false_mass qbit fuel n :
  mathcomp_kernel_root (mathcomp_oracle_result_approx qbit fuel n)
      [set MCValue false] =
  (mathcomp_oracle_false_prefix_from qbit n fuel)%:E.
Proof.
  rewrite (mathcomp_oracle_result_unfolded_eq qbit fuel n) //.
  exact: mathcomp_oracle_unfolded_false_mass.
Qed.

Lemma mathcomp_oracle_result_total_mass qbit fuel n :
  mathcomp_kernel_root (mathcomp_oracle_result_approx qbit fuel n)
      (@mc_returned bool) =
  (1 - (1 / 2 : R) ^+ fuel)%:E.
Proof.
  rewrite (mathcomp_oracle_result_unfolded_eq qbit fuel n) //.
  exact: mathcomp_oracle_unfolded_total_mass.
Qed.

Lemma mathcomp_oracle_result_true_sup qbit q :
  mathcomp_oracle_represents qbit q ->
  ereal_sup (range (fun fuel => mathcomp_kernel_root
    (mathcomp_oracle_result_approx qbit fuel 0) [set MCValue true])) = q%:E.
Proof.
  move=> Hrep.
  have -> : range (fun fuel => mathcomp_kernel_root
      (mathcomp_oracle_result_approx qbit fuel 0) [set MCValue true]) =
      range (fun fuel =>
        (mathcomp_oracle_prefix_from qbit 0 fuel)%:E).
  { apply/seteqP; split=> z [fuel <-]; exists fuel=> //;
      exact: mathcomp_oracle_result_true_mass. }
  exact: mathcomp_oracle_prefix_sup Hrep.
Qed.

Lemma mathcomp_oracle_result_false_sup qbit q :
  mathcomp_oracle_represents qbit q ->
  ereal_sup (range (fun fuel => mathcomp_kernel_root
    (mathcomp_oracle_result_approx qbit fuel 0) [set MCValue false])) =
    (1 - q)%:E.
Proof.
  move=> Hrep.
  have -> : range (fun fuel => mathcomp_kernel_root
      (mathcomp_oracle_result_approx qbit fuel 0) [set MCValue false]) =
      range (fun fuel =>
        (mathcomp_oracle_false_prefix_from qbit 0 fuel)%:E).
  { apply/seteqP; split=> z [fuel <-]; exists fuel=> //;
      exact: mathcomp_oracle_result_false_mass. }
  exact: mathcomp_oracle_false_prefix_sup Hrep.
Qed.

Lemma mathcomp_oracle_result_total_sup qbit :
  ereal_sup (range (fun fuel => mathcomp_kernel_root
    (mathcomp_oracle_result_approx qbit fuel 0) (@mc_returned bool))) = 1.
Proof.
  have -> : range (fun fuel => mathcomp_kernel_root
      (mathcomp_oracle_result_approx qbit fuel 0) (@mc_returned bool)) =
      range (fun fuel => (1 - (1 / 2 : R) ^+ fuel)%:E).
  { apply/seteqP; split=> z [fuel <-]; exists fuel=> //;
      exact: mathcomp_oracle_result_total_mass. }
  exact: mathcomp_total_sup.
Qed.

(** On the result carrier for [bool], a set which excludes [MCBottom] is
    determined by its two returned points.  Keeping these finite-space
    facts opaque prevents the omega-limit proof below from carrying four
    copies of a large set-extensionality term. *)
Lemma mc_bool_set_both U :
  ~ U MCBottom -> U (MCValue true) -> U (MCValue false) ->
  U = (@mc_returned bool).
Proof.
  move=> nbot Ht Hf. apply/seteqP; split=> x Hx.
  - destruct x as [|b]; first exact: False_rect _ (nbot Hx).
    by case: b.
  - destruct x as [|b]=> //; by case: b.
Qed.

Lemma mc_bool_set_true U :
  ~ U MCBottom -> U (MCValue true) -> ~ U (MCValue false) ->
  U = [set MCValue true].
Proof.
  move=> nbot Ht Hnf. apply/seteqP; split=> x Hx.
  - destruct x as [|b]; first exact: False_rect _ (nbot Hx).
    destruct b=> //=. exact: False_rect _ (Hnf Hx).
  - move=> /=. exact Ht.
Qed.

Lemma mc_bool_set_false U :
  ~ U MCBottom -> ~ U (MCValue true) -> U (MCValue false) ->
  U = [set MCValue false].
Proof.
  move=> nbot Hnt Hf. apply/seteqP; split=> x Hx.
  - destruct x as [|b]; first exact: False_rect _ (nbot Hx).
    destruct b=> //=. exact: False_rect _ (Hnt Hx).
  - move=> /=. exact Hf.
Qed.

Lemma mc_bool_set_neither U :
  ~ U MCBottom -> ~ U (MCValue true) -> ~ U (MCValue false) ->
  U = set0.
Proof.
  move=> nbot Hnt Hnf. apply/seteqP; split=> x Hx.
  - destruct x as [|b]; first exact: False_rect _ (nbot Hx).
    destruct b; [exact: False_rect _ (Hnt Hx)|
                 exact: False_rect _ (Hnf Hx)].
  - by [].
Qed.

Lemma mathcomp_binary_oracle_lub qbit q
    (q01 : (0 <= q <= 1)%R) :
  mathcomp_oracle_represents qbit q ->
  mathcomp_binary_oracle_denotes qbit (mathcomp_bernoulli q).
Proof.
  move=> Hrep.
  change (mathcomp_kernel_lub
    (fun fuel => mathcomp_oracle_result_approx qbit fuel 0)
    (mathcomp_bernoulli q)).
  move=> U mU nbot.
  have [Ht|Hnt] := pselect (U (MCValue true)).
  - have [Hf|Hnf] := pselect (U (MCValue false)).
    + rewrite (mc_bool_set_both nbot Ht Hf) mathcomp_bernoulli_total.
      change (1 = ereal_sup (range (fun fuel =>
        mathcomp_kernel_root
          (mathcomp_oracle_result_approx qbit fuel 0)
          (@mc_returned bool)))).
      exact: esym (mathcomp_oracle_result_total_sup qbit).
    + rewrite (mc_bool_set_true nbot Ht Hnf)
        (mathcomp_bernoulli_true_mass q q01).
      change (q%:E = ereal_sup (range (fun fuel =>
        mathcomp_kernel_root
          (mathcomp_oracle_result_approx qbit fuel 0)
          [set MCValue true]))).
      exact: esym (mathcomp_oracle_result_true_sup Hrep).
  - have [Hf|Hnf] := pselect (U (MCValue false)).
    + rewrite (mc_bool_set_false nbot Hnt Hf)
        (mathcomp_bernoulli_false_mass q q01).
      change ((1 - q)%:E = ereal_sup (range (fun fuel =>
        mathcomp_kernel_root
          (mathcomp_oracle_result_approx qbit fuel 0)
          [set MCValue false]))).
      exact: esym (mathcomp_oracle_result_false_sup Hrep).
    + rewrite (mc_bool_set_neither nbot Hnt Hnf) measure0.
      change (0 = ereal_sup (range (fun _ : nat => 0))).
      have -> : range (fun _ : nat => (0 : \bar R)) = [set 0].
      { apply/seteqP; split=> z.
        - by move=> [fuel _ <-].
        - move=> ->. by exists 0. }
      by rewrite ereal_sup1.
Qed.

Theorem mathcomp_binary_oracle_is_ast qbit q
    (q01 : (0 <= q <= 1)%R) :
  mathcomp_oracle_represents qbit q ->
  mathcomp_binary_oracle_ast qbit.
Proof.
  move=> Hrep. exists (mathcomp_bernoulli q). split.
  - exact: mathcomp_binary_oracle_lub q01 Hrep.
  - exact: mathcomp_bernoulli_total.
Qed.

End RealOracleBackend.
