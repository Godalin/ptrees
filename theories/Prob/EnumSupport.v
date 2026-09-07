(** Support continuity for increasing finite nonnegative enumerations.
    Mere convergence is insufficient: an early positive atom may disappear.
    Decidable equality on observed outcomes permits constructive singleton
    tests; no classical predicate-to-Boolean choice is needed. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order rat.
From PTree.Prob Require Import RatSubTypes DiscreteMC FrontierLiftEnum
  MeasureIteration MeasureIterationEnum.
Set Implicit Arguments.
Unset Strict Implicit.
Import Enum GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Lemma enum_expect_mono {A} (mu : Enum A) (f g : A -> rat) :
  (forall x, f x <= g x) -> enum_expect f mu <= enum_expect g mu.
Proof.
  intro Hfg. induction mu as [|[p x] tl IH]; [by []|].
  change (Qval p * f x + enum_expect f tl <= Qval p * g x + enum_expect g tl).
  apply lerD; [exact (ler_wpM2l (le_nnQ0 p) (Hfg x))|exact IH].
Qed.

Lemma enum_indicator_nonnegative {A} (mu : Enum A) (P : A -> bool) :
  0 <= enum_expect (fun x => if P x then 1 else 0) mu.
Proof.
  induction mu as [|[p x] tl IH]; [by []|].
  change (0 <= Qval p * (if P x then 1 else 0) + enum_expect (fun x => if P x then 1 else 0) tl).
  apply addr_ge0; [|exact IH]. apply mulr_ge0; [exact (le_nnQ0 p)|].
  destruct (P x); by [].
Qed.

Lemma enum_indicator_positive_member {A} (mu : Enum A) (P : A -> bool) :
  0 < enum_expect (fun x => if P x then 1 else 0) mu ->
  exists w x, List.In (w, x) mu /\ w <> nnQ_0 /\ P x.
Proof.
  induction mu as [|[w x] tl IH]; [by []|].
  intro Hpos. change (is_true (0 < Qval w * (if P x then 1 else 0) +
    enum_expect (fun x => if P x then 1 else 0) tl)) in Hpos.
  case Hw: (w == nnQ_0).
  - move/eqP: Hw=> Hw. rewrite Hw mul0r add0r in Hpos.
    destruct (IH Hpos) as [v [y [Hin [Hnz Hy]]]].
    exists v, y. split; [right; exact Hin|]. split; assumption.
  - case Hx: (P x).
    + exists w, x. split; [left; reflexivity|]. split; [by apply/eqP; rewrite Hw|exact Hx].
    + rewrite Hx mulr0 add0r in Hpos.
      destruct (IH Hpos) as [v [y [Hin [Hnz Hy]]]].
      exists v, y. split; [right; exact Hin|]. split; assumption.
Qed.

Lemma enum_indicator_member_positive {A} (mu : Enum A) (P : A -> bool) w x :
  List.In (w, x) mu -> w <> nnQ_0 -> P x ->
  0 < enum_expect (fun x => if P x then 1 else 0) mu.
Proof.
  induction mu as [|[v y] tl IH]; [intros H; contradiction|].
  intros [Heq|Hin] Hnz Hx.
  - inversion Heq; subst v y.
    change (0 < Qval w * (if P x then 1 else 0) +
      enum_expect (fun x => if P x then 1 else 0) tl).
    rewrite Hx mulr1. apply lt_le_trans with (y := Qval w).
    + apply (proj1 (@lt_0_nnQ_iff_ne_0 w)). apply/eqP. exact Hnz.
    + rewrite lerDl. apply enum_indicator_nonnegative.
  - change (0 < Qval v * (if P y then 1 else 0) +
      enum_expect (fun x => if P x then 1 else 0) tl).
    eapply lt_le_trans; [exact (IH Hin Hnz Hx)|].
    rewrite lerDr. apply mulr_ge0; [exact (le_nnQ0 v)|].
    destruct (P y); by [].
Qed.

Definition enum_chain_increasing {A} (chain : nat -> Enum A) : Prop :=
  forall (P : A -> bool) n m, Peano.le n m ->
    enum_expect (fun x => if P x then 1 else 0) (chain n) <=
    enum_expect (fun x => if P x then 1 else 0) (chain m).

Lemma enum_converges_positive_limit {A} (chain : nat -> Enum A) out P :
  enum_converges chain out ->
  0 < enum_expect (fun x => if P x then 1 else 0) out ->
  exists n, 0 < enum_expect (fun x => if P x then 1 else 0) (chain n).
Proof.
  intros Hlim Hpos. destruct (Hlim P _ Hpos) as [N HN].
  exists N.
  case: (ltP 0 (enum_expect (fun x => if P x then 1 else 0) (chain N)))
    => [Hyes|Hno]; [by []|].
  assert (Hz : enum_expect (fun x => if P x then 1 else 0) (chain N) = 0).
  { apply/eqP. rewrite eq_le. apply/andP. split; [exact Hno|apply enum_indicator_nonnegative]. }
  specialize (HN N ltac:(lia)). rewrite Hz sub0r normrN ger0_norm in HN; [|exact (ltW Hpos)].
  rewrite ltxx in HN. discriminate.
Qed.

Lemma enum_converges_positive_approx {A} (chain : nat -> Enum A) out P n :
  enum_chain_increasing chain -> enum_converges chain out ->
  0 < enum_expect (fun x => if P x then 1 else 0) (chain n) ->
  0 < enum_expect (fun x => if P x then 1 else 0) out.
Proof.
  intros Hmono Hlim Hpos.
  case: (ltP 0 (enum_expect (fun x => if P x then 1 else 0) out))
    => [Hyes|Hno]; [by []|].
  assert (Hz : enum_expect (fun x => if P x then 1 else 0) out = 0).
  { apply/eqP. rewrite eq_le. apply/andP. split; [exact Hno|apply enum_indicator_nonnegative]. }
  destruct (Hlim P _ Hpos) as [N HN].
  specialize (HN (Nat.max N n) ltac:(lia)).
  rewrite Hz subr0 ger0_norm in HN; [|apply enum_indicator_nonnegative].
  have Hle := Hmono P n (Nat.max N n) ltac:(lia).
  have Hbad := le_lt_trans Hle HN. rewrite ltxx in Hbad. discriminate.
Qed.

Lemma enum_converges_ae_iff {A : eqType} (chain : nat -> Enum A) out :
  enum_chain_increasing chain -> enum_converges chain out ->
  forall P, enum_ae out P <-> forall n, enum_ae (chain n) P.
Proof.
  intros Hmono Hlim P. split.
  - intros HP n w x Hin Hnz.
    assert (Hpos : 0 < enum_expect (fun y => if y == x then 1 else 0) (chain n)).
    { eapply enum_indicator_member_positive; [exact Hin|exact Hnz|exact (eqxx x)]. }
    pose proof (enum_converges_positive_approx Hmono Hlim Hpos) as Hout.
    destruct (enum_indicator_positive_member Hout) as [v [y [Hy [Hv Heq]]]].
    move/eqP: Heq=> Heq. subst y. exact (HP v x Hy Hv).
  - intros HP w x Hin Hnz.
    assert (Hpos : 0 < enum_expect (fun y => if y == x then 1 else 0) out).
    { eapply enum_indicator_member_positive; [exact Hin|exact Hnz|exact (eqxx x)]. }
    destruct (enum_converges_positive_limit Hlim Hpos) as [n Hn].
    destruct (enum_indicator_positive_member Hn) as [v [y [Hy [Hv Heq]]]].
    move/eqP: Heq=> Heq. subst y. exact (HP n v x Hy Hv).
Qed.

Lemma enum_iter_approx_increasing {I A} (step : I -> Enum (I + A)) i :
  enum_chain_increasing (fun n => meas_iter_approx n step i).
Proof.
  assert (Hsucc : forall n i (P : A -> bool),
    enum_expect (fun x => if P x then 1 else 0) (meas_iter_approx n step i) <=
    enum_expect (fun x => if P x then 1 else 0) (meas_iter_approx (S n) step i)).
  { induction n as [|n IH]; intros x P.
    - apply enum_indicator_nonnegative.
    - cbn [meas_iter_approx].
      rewrite !enum_expect_bind. apply enum_expect_mono. intros [y|a].
      + apply IH.
      + exact (lexx _). }
  intros P n m Hnm. induction Hnm.
  - exact (lexx _).
  - eapply le_trans; [exact IHHnm|apply Hsucc].
Qed.
