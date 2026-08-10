Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import PeanoNat Lia.

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum order
  rat archimedean.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Lemma rat_div_mul_div (x y a b : rat) :
  a != 0 -> b != 0 ->
  (x / a) * (y / b) = (x * y) / (a * b).
Proof.
  move=> a0 b0.
  rewrite invrM ?unitfE ?mulf_neq0 //.
  rewrite mulrACA.
  by rewrite [b^-1 * a^-1]mulrC.
Qed.

Lemma rat_contract_bound_step (K n : nat) :
  (0 < K)%coq_nat ->
  ((K%:R : rat) / (K + n)%:R) *
      ((K%:R : rat) / K.+1%:R) <=
    (K%:R : rat) / (K + n.+1)%:R.
Proof.
  move=> Kpos.
  have Kbool : (0 < K)%N by apply/ssrnat.ltP.
  have Kneq : K != 0 by rewrite -lt0n.
  have K0 : (K%:R : rat) != 0.
  { by rewrite pnatr_eq0. }
  have Kn0 : ((K + n)%:R : rat) != 0.
  { by rewrite pnatr_eq0 addn_eq0 (negPf Kneq). }
  have KS0 : (K.+1%:R : rat) != 0 by rewrite pnatr_eq0.
  have KnS0 : ((K + n.+1)%:R : rat) != 0.
  { by rewrite pnatr_eq0 addn_eq0 (negPf Kneq). }
  rewrite rat_div_mul_div //.
  rewrite ler_pdivlMr; last by rewrite ltr0n addn_gt0 orbT.
  rewrite [(_ / _) * _]mulrAC.
  rewrite ler_pdivrMr; last first.
  { apply mulr_gt0.
    - by rewrite ltr0n addn_gt0 Kbool.
    - exact: ltr0Sn. }
  rewrite -!natrM ler_nat.
  apply/ssrnat.leP.
  change (Peano.le
    (Nat.mul (Nat.mul K K) (Nat.add K (Nat.succ n)))
    (Nat.mul K (Nat.mul (Nat.add K n) (Nat.succ K)))).
  rewrite -Nat.mul_assoc.
  apply Nat.mul_le_mono_l.
  rewrite Nat.add_succ_r !Nat.mul_succ_r.
  rewrite [Nat.mul K (Nat.add K n)]Nat.mul_comm.
  apply Nat.add_le_mono_l. lia.
Qed.

Lemma rat_contract_power_bound (r : rat) (K n : nat) :
  (0 < K)%coq_nat -> 0 <= r ->
  r <= (K%:R : rat) / K.+1%:R ->
  r ^+ n <= (K%:R : rat) / (K + n)%:R.
Proof.
  move=> Kpos r0 Hr.
  elim: n=> [|n IH].
  - rewrite expr0 addn0.
    by rewrite divrr ?unitfE ?pnatr_eq0 //; apply/eqP; lia.
  - rewrite exprS.
    have rpow0 := exprn_ge0 n r0.
    have Hmul := ler_pM rpow0 r0 IH Hr.
    have Hstep := rat_contract_bound_step n Kpos.
    rewrite addnS.
    rewrite [r * r ^+ n]mulrC.
    rewrite addnS in Hstep.
    exact: le_trans Hmul Hstep.
Qed.

Lemma rat_contract_vanishes (r : rat) (K : nat) :
  (0 < K)%coq_nat -> 0 <= r ->
  r <= (K%:R : rat) / K.+1%:R ->
  forall eps, 0 < eps ->
    exists N, forall n, Peano.le N n -> r ^+ n < eps.
Proof.
  move=> Kpos r0 Hr eps eps0.
  have Kbool : (0 < K)%N by apply/ssrnat.ltP.
  pose N := Num.bound ((K%:R : rat) / eps).
  have q0 : 0 <= (K%:R : rat) / eps.
  { apply divr_ge0; [exact: ler0n|exact: ltW eps0]. }
  have Harch : (K%:R : rat) / eps < N%:R := archi_boundP q0.
  exists N=> n HN.
  apply: le_lt_trans (rat_contract_power_bound n Kpos r0 Hr) _.
  rewrite ltr_pdivrMr; last first.
  { by rewrite ltr0n addn_gt0 Kbool. }
  have HK : (K%:R : rat) < N%:R * eps.
  { move: Harch. by rewrite ltr_pdivrMr. }
  have Hcast : (N%:R : rat) <= n%:R.
  { rewrite ler_nat. apply/ssrnat.leP. exact HN. }
  have Hnadd : (n%:R : rat) <= (K + n)%:R.
  { rewrite ler_nat. apply/ssrnat.leP.
    change (Peano.le n (Nat.add K n)). lia. }
  have HNadd : (N%:R : rat) <= (K + n)%:R := le_trans Hcast Hnadd.
  have Hmul := ler_wpM2r (ltW eps0) HNadd.
  rewrite ![(_%:R : rat) * eps]mulrC in HK Hmul.
  exact: lt_le_trans HK Hmul.
Qed.

(** Every nonnegative rational strictly below one admits the elementary
    [K / (K + 1)] contraction certificate used above. *)
Lemma rat_contract_certificate (r : rat) :
  0 <= r -> r < 1 ->
  exists K : nat, (0 < K)%coq_nat /\
    r <= (K%:R : rat) / K.+1%:R.
Proof.
  move=> r0 r1.
  pose K := Num.bound (r / (1 - r)).
  have one_sub_r0 : 0 < 1 - r by rewrite subr_gt0.
  have quotient0 : 0 <= r / (1 - r).
  { exact: divr_ge0 r0 (ltW one_sub_r0). }
  have Harch : r / (1 - r) < K%:R := archi_boundP quotient0.
  have Kbool : (0 < K)%N.
  { have HK : (0 : rat) < K%:R := le_lt_trans quotient0 Harch.
    by move: HK; rewrite ltr0n. }
  have Kpos : (0 < K)%coq_nat by apply/ssrnat.ltP.
  exists K; split=> //.
  rewrite ler_pdivlMr; last exact: ltr0Sn.
  apply/ltW.
  rewrite -addn1 natrD /= mulrDr mulr1.
  have Hcross : r < (K%:R : rat) * (1 - r).
  { move: Harch. by rewrite ltr_pdivrMr. }
  rewrite mulrBr mulr1 in Hcross.
  have Hadd :
      r + (K%:R : rat) * r <
        ((K%:R : rat) - (K%:R : rat) * r) + (K%:R : rat) * r.
  { by rewrite ltrD2r. }
  rewrite subrK in Hadd.
  move: Hadd.
  by rewrite [(K%:R : rat) * r]mulrC addrC.
Qed.
