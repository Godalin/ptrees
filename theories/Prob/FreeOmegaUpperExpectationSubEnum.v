Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

From Coq Require Import List Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From mathcomp.classical Require Import classical_sets.
From PTree.Prob Require Import RatSubTypes DiscreteMC MeasureIterationEnum TwoLevelMeasureSubEnum
  FreeOmegaMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum RatSubTypes GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** Internal model audit for quotient-to-native coupling realization.
    A raw FreeOmega term may contain a non-increasing FOLub.  Interpret
    such a node by a supremum, NOT by the limit of a convergent sequence.
    The resulting functional need not be additive on arbitrary raw terms.
    This file does not yet assert soundness of free_omega_qlift. *)
Section UpperExpectation.
Variable R : realType.

Fixpoint enum_real_expect {A} (f : A -> R) (mu : Enum A) : R :=
  match mu with
  | nil => 0
  | (p, x) :: tail => ratr (Qval p) * f x + enum_real_expect f tail
  end.

Lemma enum_real_expect_rat {A} (f : A -> rat) mu :
  enum_real_expect (fun x => ratr (f x)) mu = ratr (enum_expect f mu).
Proof.
  elim: mu=> [|[p x] tail IH] /=.
  - by rewrite rmorph0.
  - by rewrite rmorphD rmorphM IH.
Qed.

Lemma enum_real_expect_nonnegative {A} (f : A -> R) mu :
  (forall x, 0 <= f x) -> 0 <= enum_real_expect f mu.
Proof.
  move=> Hf. elim: mu=> [|[p x] tail IH] /=; first exact: lexx.
  apply: addr_ge0 IH. apply: mulr_ge0 (Hf x).
  by rewrite ler0q; apply: Qval_nnQ_ge0.
Qed.

Lemma enum_real_expect_mono {A} (f g : A -> R) mu :
  (forall x, f x <= g x) -> enum_real_expect f mu <= enum_real_expect g mu.
Proof.
  move=> Hfg. elim: mu=> [|[p x] tail IH] /=; first exact: lexx.
  apply lerD.
  - apply ler_wpM2l; [|exact (Hfg x)].
    by rewrite ler0q; apply: Qval_nnQ_ge0.
  - exact IH.
Qed.

Lemma subenum_real_expect_bound {A} (mu : SubEnum A) (f : A -> R) :
  (forall x, f x <= 1) -> enum_real_expect f (subenum_raw mu) <= 1.
Proof.
  move=> Hf.
  apply: le_trans (enum_real_expect_mono (subenum_raw mu) Hf) _.
  rewrite (_ : (fun _ : A => (1 : R)) = (fun _ => ratr (1 : rat)));
    last by apply functional_extensionality=> x; rewrite rmorph1.
  rewrite enum_real_expect_rat.
  rewrite -(rmorph1 (ratr : {rmorphism rat -> R})) ler_rat.
  exact (subenum_bound mu).
Qed.

Definition countable_upper (values : nat -> R) : R := sup (range values).

Lemma countable_upper_le values b :
  (forall n, values n <= b) -> countable_upper values <= b.
Proof.
  move=> Hb. apply: sup_le_ub.
  - exists (values 0%nat). by exists 0%nat.
  - apply/ubP=> x [n _ <-]. exact: Hb.
Qed.

Lemma countable_upper_ge values b n :
  (forall i, values i <= b) -> values n <= countable_upper values.
Proof.
  move=> Hb. apply: sup_ubound.
  - exists b. apply/ubP=> x [i _ <-]. exact: Hb.
  - by exists n.
Qed.

Lemma countable_upper_constant c : countable_upper (fun _ => c) = c.
Proof.
  apply/eqP. rewrite eq_le. apply/andP. split.
  - apply countable_upper_le. intro n. exact: lexx.
  - exact (@countable_upper_ge (fun _ => c) c 0%nat (fun _ => lexx c)).
Qed.

Fixpoint free_omega_upper {A} (mu : FreeOmega SubEnum A) (f : A -> R) : R :=
  match mu with
  | FORet x => f x
  | FOZero => 0
  | @FOSample _ _ X node k => enum_real_expect (fun x => free_omega_upper (k x) f)
      (subenum_raw node)
  | FOLub chain => countable_upper (fun n => free_omega_upper (chain n) f)
  end.

Lemma free_omega_upper_bounds {A} (mu : FreeOmega SubEnum A) (f : A -> R) :
  (forall x, 0 <= f x /\ f x <= 1) ->
  0 <= free_omega_upper mu f /\ free_omega_upper mu f <= 1.
Proof.
  move=> Hf. induction mu as [x| |X node k IH|chain IH]; cbn [free_omega_upper].
  - exact (Hf x).
  - split; [exact: lexx|exact: ler01].
  - split.
    + apply enum_real_expect_nonnegative. intro x. exact (proj1 (IH x)).
    + apply subenum_real_expect_bound. intro x. exact (proj2 (IH x)).
  - split.
    + apply: le_trans (proj1 (IH 0%nat)) _.
      exact (@countable_upper_ge (fun n => free_omega_upper (chain n) f)
        1 0%nat (fun n => proj2 (IH n))).
    + apply countable_upper_le. intro n. exact (proj2 (IH n)).
Qed.

Lemma free_omega_upper_mono {A} (mu : FreeOmega SubEnum A) (f g : A -> R) :
  (forall x, 0 <= g x /\ g x <= 1) ->
  (forall x, f x <= g x) -> free_omega_upper mu f <= free_omega_upper mu g.
Proof.
  move=> Hg Hfg. induction mu as [x| |X node k IH|chain IH]; cbn [free_omega_upper].
  - exact (Hfg x).
  - exact: lexx.
  - apply enum_real_expect_mono. exact IH.
  - apply countable_upper_le. intro n. apply: le_trans (IH n) _.
    exact (@countable_upper_ge (fun i => free_omega_upper (chain i) g)
      1 n (fun i => proj2 (free_omega_upper_bounds (chain i) Hg))).
Qed.

(** This identity is structural, including for arbitrary formal Lub nodes.
    It does not depend on linearity or an assumed continuity law. *)
Lemma free_omega_upper_bind {A B} (mu : FreeOmega SubEnum A)
    (k : A -> FreeOmega SubEnum B) (f : B -> R) :
  free_omega_upper (free_omega_bind mu k) f =
  free_omega_upper mu (fun x => free_omega_upper (k x) f).
Proof.
  induction mu as [x| |X node h IH|chain IH]; cbn [free_omega_bind free_omega_upper].
  - reflexivity.
  - reflexivity.
  - f_equal. apply functional_extensionality. exact IH.
  - f_equal. apply functional_extensionality. exact IH.
Qed.

Lemma enum_real_expect_zero {A} (mu : Enum A) :
  enum_real_expect (fun _ => 0) mu = 0.
Proof. elim: mu=> [|[p x] tail IH] //=. by rewrite mulr0 IH addr0. Qed.

Lemma free_omega_upper_zero {A} (mu : FreeOmega SubEnum A) :
  free_omega_upper mu (fun _ => 0) = 0.
Proof.
  induction mu as [x| |X node k IH|chain IH]; cbn [free_omega_upper]; try reflexivity.
  - rewrite (_ : (fun x => free_omega_upper (k x) (fun _ => 0)) = (fun _ => 0));
      last by apply functional_extensionality.
    apply enum_real_expect_zero.
  - rewrite (_ : (fun n => free_omega_upper (chain n) (fun _ => 0)) = (fun _ => 0));
      last by apply functional_extensionality.
    apply countable_upper_constant.
Qed.

(** On native presentations this interpretation is the actual weighted
    finite expectation, not a support-only test. *)
Lemma free_omega_upper_native_rat {A} (mu : SubEnum A) (f : A -> rat) :
  free_omega_upper (FOSample mu (fun x => FORet x)) (fun x => ratr (f x)) =
  ratr (enum_expect f (subenum_raw mu)).
Proof. exact: enum_real_expect_rat. Qed.

Lemma enum_real_expect_one {A} (mu : Enum A) :
  enum_real_expect (fun _ => 1) mu = ratr (enum_mass mu).
Proof.
  rewrite (_ : (fun _ : A => (1 : R)) = (fun _ => ratr (1 : rat)));
    last by apply functional_extensionality=> x; rewrite rmorph1.
  exact: enum_real_expect_rat.
Qed.

End UpperExpectation.
