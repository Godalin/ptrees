Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat ssralg ssrnum order rat reals archimedean.
From mathcomp.classical Require Import classical_sets set_interval.
From mathcomp.analysis Require Import ereal sequences topology normedtype.
From PTree.Prob Require Import RatSubTypes DiscreteMC FrontierLiftEnum
  FreeOmegaMeasure FreeOmegaUpperExpectationEnum FreeOmegaUpperCouplingEnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum RatSubTypes GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

(** Monotone convergence for finite weighted sums with possibly infinite
    values.  No bound on Enum's total weight or on the chain is assumed. *)
Section ExtendedContinuity.
Variable R : realType.
Local Notation upper := (@extended_upper R).
Local Notation expect := (@enum_extended_expect R).

Lemma extended_upper_naturals : upper (fun n => (n%:R)%:E) = +oo.
Proof.
  rewrite /extended_upper.
  have E : range (fun n : nat => (n%:R : R)%:E) =
      EFin @` range (fun n : nat => (n%:R : R)).
  { rewrite -image_comp. reflexivity. }
  rewrite E. apply hasNub_ereal_sup.
  - apply/has_ubPn=> x.
    exists ((Num.bound `|x|)%:R : R); [by exists (Num.bound `|x|)|].
    exact: le_lt_trans (ler_norm x) (archi_boundP (normr_ge0 x)).
  - exists (0%R : R). by exists 0%nat.
Qed.

Lemma extended_upper_scale (f : nat -> \bar R) (p : R) :
  (0 <= p)%R -> upper (fun n => p%:E * f n) = p%:E * upper f.
Proof.
  move=> Hp. rewrite /extended_upper -ereal_supZl //.
  - congr (ereal_sup _). rewrite -image_comp. reflexivity.
  - apply/eqP=> E. have H : range f (f 0%nat) by exists 0%nat.
    by rewrite E in H.
Qed.

Lemma extended_upper_add (f g : nat -> \bar R) :
  (forall n, 0 <= f n) -> (forall n, 0 <= g n) ->
  nondecreasing_seq f -> nondecreasing_seq g ->
  upper (fun n => f n + g n) = upper f + upper g.
Proof.
  move=> Hf Hg Hfi Hgi.
  have Hsi : nondecreasing_seq (fun n => f n + g n).
  { move=> n m Hnm. exact: leeD (Hfi n m Hnm) (Hgi n m Hnm). }
  have Hsum := ereal_nondecreasing_cvgn Hsi.
  have Hfl := ereal_nondecreasing_cvgn Hfi.
  have Hgl := ereal_nondecreasing_cvgn Hgi.
  have Hdef : upper f +? upper g.
  { apply ge0_adde_def.
    - exact: le_trans (Hf 0%nat) (extended_upper_ge f 0%nat).
    - exact: le_trans (Hg 0%nat) (extended_upper_ge g 0%nat). }
  exact: cvg_unique Hsum (cvgeD Hdef Hfl Hgl).
Qed.

(** Zero-weight entries impose no continuity obligation, even when their
    tests take infinite values.  This is the form needed by SampleLub. *)
Lemma enum_extended_expect_countable_ae {A} (mu : Enum A)
    (tests : nat -> A -> \bar R) :
  (forall n x, 0 <= tests n x) ->
  enum_ae mu (fun x => nondecreasing_seq (fun n => tests n x)) ->
  expect (fun x => upper (fun n => tests n x)) mu =
    upper (fun n => expect (tests n) mu).
Proof.
  move=> Hnonneg. induction mu as [|[p x] tail IH]; move=> Hinc;
    cbn [enum_extended_expect].
  - symmetry. exact: extended_upper_constant.
  - have Htail : enum_ae tail (fun x => nondecreasing_seq (fun n => tests n x)).
    { intros q y Hy Hq. exact (Hinc q y (or_intror Hy) Hq). }
    rewrite (IH Htail).
    destruct (eqVneq p nnQ_0) as [->|Hnz].
    { cbn [Qval nnQ_0]. rewrite rmorph0 mul0e add0e.
      f_equal. apply functional_extensionality=> n. by rewrite mul0e add0e. }
    have Hx : nondecreasing_seq (fun n => tests n x).
    { apply (Hinc p x (or_introl (Logic.eq_refl (p,x)))).
      move=> Hz. move/eqP: Hnz=> Hneq. exact: Hneq Hz. }
    rewrite -extended_upper_scale; last by rewrite ler0q; apply: le_nnQ0.
    symmetry. apply extended_upper_add.
    + move=> n. apply mule_ge0; [|exact: Hnonneg].
      by rewrite lee_fin ler0q; apply: le_nnQ0.
    + move=> n. exact: enum_extended_expect_nonnegative.
    + move=> n m Hnm. apply: lee_wpmul2l (Hx n m Hnm).
      by rewrite lee_fin ler0q; apply: le_nnQ0.
    + move=> n m Hnm. apply enum_extended_expect_ae_mono.
      intros q y Hy Hq. exact (Htail q y Hy Hq n m Hnm).
Qed.

Lemma enum_extended_expect_countable {A} (mu : Enum A)
    (tests : nat -> A -> \bar R) :
  (forall n x, 0 <= tests n x) ->
  (forall x, nondecreasing_seq (fun n => tests n x)) ->
  expect (fun x => upper (fun n => tests n x)) mu =
    upper (fun n => expect (tests n) mu).
Proof.
  intros Hnonneg Hinc. apply enum_extended_expect_countable_ae; [exact Hnonneg|].
  intros p x _ _. exact (Hinc x).
Qed.

Theorem free_omega_extended_upper_continuous {A} (mu : FreeOmega Enum A)
    (tests : nat -> A -> \bar R) :
  (forall n x, 0 <= tests n x) ->
  (forall x, nondecreasing_seq (fun n => tests n x)) ->
  free_omega_extended_upper mu (fun x => upper (fun n => tests n x)) =
    upper (fun n => free_omega_extended_upper mu (tests n)).
Proof.
  move=> Hnonneg Hinc.
  induction mu as [x| |X node k IH|c IH]; cbn [free_omega_extended_upper].
  - reflexivity.
  - symmetry. exact: extended_upper_constant.
  - have Hrows :
      (fun x => free_omega_extended_upper (k x) (fun y => upper (fun n => tests n y))) =
      (fun x => upper (fun n => free_omega_extended_upper (k x) (tests n))).
    { apply functional_extensionality. exact IH. }
    rewrite Hrows. apply enum_extended_expect_countable.
    + move=> n x. exact: free_omega_extended_upper_nonnegative.
    + move=> x n m Hnm. apply free_omega_extended_upper_mono=> y. exact (Hinc y n m Hnm).
  - have Hrows :
      (fun i => free_omega_extended_upper (c i) (fun y => upper (fun n => tests n y))) =
      (fun i => upper (fun n => free_omega_extended_upper (c i) (tests n))).
    { apply functional_extensionality. exact IH. }
    rewrite Hrows. exact: extended_upper_swap.
Qed.

Theorem free_omega_sample_lub_extended_upper {A X} (mu : Enum X)
    (chain : X -> nat -> FreeOmega Enum A) (f : A -> \bar R) :
  enum_ae mu (fun x => forall n,
    free_omega_approx eq (chain x n) (chain x (S n))) ->
  (forall x, 0 <= f x) ->
  free_omega_extended_upper (FOSample mu (fun x => FOLub (chain x))) f =
    free_omega_extended_upper (FOLub (fun n => FOSample mu (fun x => chain x n))) f.
Proof.
  move=> Hinc Hf. cbn [free_omega_extended_upper].
  apply enum_extended_expect_countable_ae.
  - move=> n x. exact: free_omega_extended_upper_nonnegative.
  - intros p x Hpx Hnz. apply/nondecreasing_seqP=> n.
    eapply free_omega_approx_extended_upper; [exact (Hinc p x Hpx Hnz n)|exact Hf|].
    intros a b ->. exact: lexx.
Qed.
End ExtendedContinuity.
