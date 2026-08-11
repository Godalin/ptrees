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

End RealOracleBackend.
