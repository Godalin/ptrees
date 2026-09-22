(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
(** Support continuity for increasing finite nonnegative enumerations.
    Mere convergence is insufficient: an early positive atom may disappear.
    Decidable equality on observed outcomes permits constructive singleton
    tests; no classical predicate-to-Boolean choice is needed. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSupport.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.FrontierLift.
Require Import PTree.Prob.Interface.Iteration.
Require Import PTree.Prob.Backend.EnumQ.Iteration.
Set Implicit Arguments.
Unset Strict Implicit.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Lemma enumQ_expect_mono {A} (mu : EnumQ A) (f g : A -> rat) :
  (forall x, f x <= g x) -> enumQ_expect f mu <= enumQ_expect g mu.
Proof. exact (finite_expect_mono (enumQ_nonnegative mu)). Qed.
Lemma enumQ_indicator_nonnegative {A} (mu : EnumQ A) (P : A -> bool) :
  0 <= enumQ_expect (fun x => if P x then 1 else 0) mu.
Proof. exact (finite_indicator_nonnegative P (enumQ_nonnegative mu)). Qed.
Lemma enumQ_indicator_positive_member {A} (mu : EnumQ A) (P : A -> bool) :
  0 < enumQ_expect (fun x => if P x then 1 else 0) mu ->
  exists w x, List.In (w,x) (enumQ_raw mu) /\ w <> 0 /\ P x.
Proof. exact: finite_indicator_positive_member. Qed.
Lemma enumQ_indicator_member_positive {A} (mu : EnumQ A) (P : A -> bool) w x :
  List.In (w,x) (enumQ_raw mu) -> w <> 0 -> P x ->
  0 < enumQ_expect (fun x => if P x then 1 else 0) mu.
Proof. exact (finite_indicator_member_positive (P := P) (enumQ_nonnegative mu)). Qed.

Definition enumQ_chain_increasing {A} (chain : nat -> EnumQ A) : Prop :=
  forall (P : A -> bool) n m, Peano.le n m ->
    enumQ_expect (fun x => if P x then 1 else 0) (chain n) <=
    enumQ_expect (fun x => if P x then 1 else 0) (chain m).

Lemma enumQ_converges_positive_limit {A} (chain : nat -> EnumQ A) out P :
  enumQ_converges chain out ->
  0 < enumQ_expect (fun x => if P x then 1 else 0) out ->
  exists n, 0 < enumQ_expect (fun x => if P x then 1 else 0) (chain n).
Proof.
  intros Hlim Hpos. destruct (Hlim P _ Hpos) as [N HN].
  exists N.
  case: (ltP 0 (enumQ_expect (fun x => if P x then 1 else 0) (chain N)))
    => [Hyes|Hno]; [by []|].
  assert (Hz : enumQ_expect (fun x => if P x then 1 else 0) (chain N) = 0).
  { apply/eqP. rewrite eq_le. apply/andP. split; [exact Hno|apply enumQ_indicator_nonnegative]. }
  specialize (HN N ltac:(lia)). rewrite Hz sub0r normrN ger0_norm in HN; [|exact (ltW Hpos)].
  rewrite ltxx in HN. discriminate.
Qed.

Lemma enumQ_converges_positive_approx {A} (chain : nat -> EnumQ A) out P n :
  enumQ_chain_increasing chain -> enumQ_converges chain out ->
  0 < enumQ_expect (fun x => if P x then 1 else 0) (chain n) ->
  0 < enumQ_expect (fun x => if P x then 1 else 0) out.
Proof.
  intros Hmono Hlim Hpos.
  case: (ltP 0 (enumQ_expect (fun x => if P x then 1 else 0) out))
    => [Hyes|Hno]; [by []|].
  assert (Hz : enumQ_expect (fun x => if P x then 1 else 0) out = 0).
  { apply/eqP. rewrite eq_le. apply/andP. split; [exact Hno|apply enumQ_indicator_nonnegative]. }
  destruct (Hlim P _ Hpos) as [N HN].
  specialize (HN (Nat.max N n) ltac:(lia)).
  rewrite Hz subr0 ger0_norm in HN; [|apply enumQ_indicator_nonnegative].
  have Hle := Hmono P n (Nat.max N n) ltac:(lia).
  have Hbad := le_lt_trans Hle HN. rewrite ltxx in Hbad. discriminate.
Qed.

Lemma enumQ_converges_ae_iff {A : eqType} (chain : nat -> EnumQ A) out :
  enumQ_chain_increasing chain -> enumQ_converges chain out ->
  forall P, enumQ_ae out P <-> forall n, enumQ_ae (chain n) P.
Proof.
  intros Hmono Hlim P. split.
  - intros HP n w x Hin Hnz.
    assert (Hpos : 0 < enumQ_expect (fun y => if y == x then 1 else 0) (chain n)).
    { eapply enumQ_indicator_member_positive; [exact Hin|exact Hnz|exact (eqxx x)]. }
    pose proof (enumQ_converges_positive_approx Hmono Hlim Hpos) as Hout.
    destruct (enumQ_indicator_positive_member Hout) as [v [y [Hy [Hv Heq]]]].
    move/eqP: Heq=> Heq. subst y. exact (HP v x Hy Hv).
  - intros HP w x Hin Hnz.
    assert (Hpos : 0 < enumQ_expect (fun y => if y == x then 1 else 0) out).
    { eapply enumQ_indicator_member_positive; [exact Hin|exact Hnz|exact (eqxx x)]. }
    destruct (enumQ_converges_positive_limit Hlim Hpos) as [n Hn].
    destruct (enumQ_indicator_positive_member Hn) as [v [y [Hy [Hv Heq]]]].
    move/eqP: Heq=> Heq. subst y. exact (HP n v x Hy Hv).
Qed.

Lemma enumQ_iter_approx_increasing {I A} (step : I -> EnumQ (I + A)) i :
  enumQ_chain_increasing (fun n => meas_iter_approx n step i).
Proof.
  assert (Hsucc : forall n i (P : A -> bool),
    enumQ_expect (fun x => if P x then 1 else 0) (meas_iter_approx n step i) <=
    enumQ_expect (fun x => if P x then 1 else 0) (meas_iter_approx (S n) step i)).
  { induction n as [|n IH]; intros x P.
    - apply enumQ_indicator_nonnegative.
    - cbn [meas_iter_approx].
      rewrite !enumQ_expect_bind. apply enumQ_expect_mono. intros [y|a].
      + apply IH.
      + exact (lexx _). }
  intros P n m Hnm. induction Hnm.
  - exact (lexx _).
  - eapply le_trans; [exact IHHnm|apply Hsucc].
Qed.
