(** Role: Independent extensional expectation domain. No PTree, FreeOmega,
    semantic-interface instance, or free completion is used in this model.
    Evaluators are identified only on [0,1]-valued tests; their values on
    unbounded functions are deliberately outside the contract. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Arith.PeanoNat Relations RelationClasses.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From mathcomp.classical Require Import classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Expectation.
Variable R : realType.

Definition oval_test {A} (f : A → R) := ∀ x, 0 <= f x ∧ f x <= 1.
Definition oval_sup (c : nat → R) : R := sup (range c).
Definition oval_pointwise_sup {A} (f : nat → A → R) :=
  λ x, oval_sup (λ n, f n x).

Lemma oval_sup_le c b : (∀ n, c n <= b) → oval_sup c <= b.
Proof.
  move=> Hb. apply: sup_le_ub.
  - exists (c 0%nat). by exists 0%nat.
  - apply/ubP=> x [n _ <-]. exact: Hb.
Qed.

Lemma oval_sup_ge c b n : (∀ i, c i <= b) → c n <= oval_sup c.
Proof.
  move=> Hb. apply: sup_ubound.
  - exists b. apply/ubP=> x [i _ <-]. exact: Hb.
  - by exists n.
Qed.

Lemma oval_sup_const c : oval_sup (λ _, c) = c.
Proof.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - apply oval_sup_le=> n. exact: lexx.
  - exact (@oval_sup_ge (λ _, c) c 0%nat (λ _, lexx c)).
Qed.

Lemma oval_sup_ext c d : (∀ n, c n = d n) → oval_sup c = oval_sup d.
Proof. move=> H; congr (oval_sup _); apply functional_extensionality; exact H. Qed.

Lemma oval_sup_mono c d b :
  (∀ n, d n <= b) → (∀ n, c n <= d n) → oval_sup c <= oval_sup d.
Proof.
  move=> Hb Hcd; apply oval_sup_le=> n.
  exact: le_trans (Hcd n) (oval_sup_ge n Hb).
Qed.

Lemma oval_increasing_le (f : nat → R) :
  (∀ n, f n <= f (S n)) →
  ∀ n m, Peano.le n m → f n <= f m.
Proof.
  intros Hi n m H; induction H; first exact: lexx.
  exact: le_trans IHle (Hi m).
Qed.

Lemma oval_sup_scale c p b :
  0 <= p → (∀ n, c n <= b) →
  oval_sup (λ n, p * c n) = p * oval_sup c.
Proof.
  move=> Hp Hb. destruct (eqVneq p 0) as [->|Hnz].
  - rewrite (_ : (λ n, (0 : R) * c n) = (λ _, 0));
      last by apply functional_extensionality=> n; rewrite mul0r.
    by rewrite oval_sup_const mul0r.
  - have Hpos : 0 < p by rewrite lt0r Hnz Hp.
    have Hscaled : ∀ n, p * c n <= p * b := λ n, ler_wpM2l Hp (Hb n).
    apply/eqP; rewrite eq_le; apply/andP; split.
    + apply oval_sup_le=> n. apply ler_wpM2l; first exact Hp.
      exact (oval_sup_ge n Hb).
    + rewrite -ler_pdivlMl //; apply oval_sup_le=> n; rewrite ler_pdivlMl //.
      exact (oval_sup_ge n Hscaled).
Qed.

Lemma oval_sup_add c d bc bd :
  (∀ n, c n <= c (S n)) → (∀ n, d n <= d (S n)) →
  (∀ n, c n <= bc) → (∀ n, d n <= bd) →
  oval_sup (λ n, c n + d n) = oval_sup c + oval_sup d.
Proof.
  move=> Hc Hd Hbc Hbd.
  have Hsc : has_sup (range c).
  { split; [exists (c 0%nat); by exists 0%nat|].
    exists bc; apply/ubP=> x [n _ <-]; exact (Hbc n). }
  have Hsd : has_sup (range d).
  { split; [exists (d 0%nat); by exists 0%nat|].
    exists bd; apply/ubP=> x [n _ <-]; exact (Hbd n). }
  have Hb : ∀ n, c n + d n <= bc + bd := λ n, lerD (Hbc n) (Hbd n).
  apply/eqP; rewrite eq_le; apply/andP; split.
  - apply oval_sup_le=> n; apply lerD.
    + exact (oval_sup_ge n Hbc).
    + exact (oval_sup_ge n Hbd).
  - change (sup (range c) + sup (range d) <= oval_sup (λ n, c n + d n)).
    rewrite -(sup_sumE Hsc Hsd); apply sup_le_ub.
    + exists (c 0%nat + d 0%nat), (c 0%nat).
      * by exists 0%nat.
      * exists (d 0%nat); [by exists 0%nat|reflexivity].
    + intros z [x [i _ <-] [y [j _ <-] <-]].
      apply: le_trans (_ : c (Nat.max i j) + d (Nat.max i j) <= _).
      * apply lerD.
        -- exact (oval_increasing_le Hc (Nat.le_max_l i j)).
        -- exact (oval_increasing_le Hd (Nat.le_max_r i j)).
      * exact (oval_sup_ge (Nat.max i j) Hb).
Qed.

Lemma oval_sup_swap (c : nat → nat → R) b :
  (∀ i j, c i j <= b) →
  oval_sup (λ i, oval_sup (c i)) =
  oval_sup (λ j, oval_sup (λ i, c i j)).
Proof.
  move=> Hb.
  have Hr : ∀ i, oval_sup (c i) <= b := λ i, oval_sup_le (Hb i).
  have Hc : ∀ j, oval_sup (λ i, c i j) <= b :=
    λ j, oval_sup_le (λ i, Hb i j).
  apply/eqP; rewrite eq_le; apply/andP; split;
    apply oval_sup_le=> i; apply oval_sup_le=> j.
  - exact: le_trans (oval_sup_ge i (λ k, Hb k j)) (oval_sup_ge j Hc).
  - exact: le_trans (oval_sup_ge i (Hb j)) (oval_sup_ge j Hr).
Qed.

Lemma oval_test_zero {A} : @oval_test A (λ _, 0).
Proof. intro x; split; [exact: lexx|exact: ler01]. Qed.
Lemma oval_test_one {A} : @oval_test A (λ _, 1).
Proof. intro x; split; [exact: ler01|exact: lexx]. Qed.
Lemma oval_test_scale {A} p (f : A → R) :
  0 <= p → p <= 1 → oval_test f → oval_test (λ x, p * f x).
Proof.
  move=> Hp Hp1 Hf x; split; first exact: mulr_ge0 Hp (proj1 (Hf x)).
  apply: le_trans (ler_wpM2l Hp (proj2 (Hf x))) _.
  by rewrite mulr1.
Qed.
Lemma oval_test_add {A} (f g : A → R) :
  oval_test f → oval_test g → (∀ x, f x + g x <= 1) →
  oval_test (λ x, f x + g x).
Proof. move=> Hf Hg Hfg x; split; [exact: addr_ge0 (proj1 (Hf x)) (proj1 (Hg x))|exact: Hfg]. Qed.
Lemma oval_test_sup {A} (f : nat → A → R) :
  (∀ n, oval_test (f n)) → oval_test (oval_pointwise_sup f).
Proof.
  move=> Hf x; split.
  - exact: le_trans (proj1 (Hf 0%nat x)) (oval_sup_ge 0%nat (λ n, proj2 (Hf n x))).
  - exact: oval_sup_le (λ n, proj2 (Hf n x)).
Qed.

(** A property of a concrete evaluator, not a semantic-interface typeclass. *)
Record OmegaValLaws {A} (eval : (A → R) → R) : Prop := {
  oval_zero : eval (λ _, 0) = 0;
  oval_mono : ∀ f g, oval_test f → oval_test g →
    (∀ x, f x <= g x) → eval f <= eval g;
  oval_scale : ∀ p f, 0 <= p → p <= 1 → oval_test f →
    eval (λ x, p * f x) = p * eval f;
  oval_add : ∀ f g, oval_test f → oval_test g →
    (∀ x, f x + g x <= 1) → eval (λ x, f x + g x) = eval f + eval g;
  oval_mass_le1 : eval (λ _, 1) <= 1;
  oval_continuous : ∀ f : nat → A → R,
    (∀ n, oval_test (f n)) →
    (∀ n x, f n x <= f (S n) x) →
    eval (oval_pointwise_sup f) = oval_sup (λ n, eval (f n))
}.

Record OmegaVal (A : Type) := {
  oval_eval : (A → R) → R;
  oval_laws : OmegaValLaws oval_eval
}.
Arguments oval_eval {A} _ _.
Arguments oval_laws {A} _.

Definition oval_eq {A} (L M : OmegaVal A) :=
  ∀ f, oval_test f → oval_eval L f = oval_eval M f.
Definition oval_le {A} (L M : OmegaVal A) :=
  ∀ f, oval_test f → oval_eval L f <= oval_eval M f.
Definition oval_increasing {A} (c : nat → OmegaVal A) :=
  ∀ n, oval_le (c n) (c (S n)).
Definition oval_mass {A} (L : OmegaVal A) := oval_eval L (λ _, 1).

Lemma oval_eval_bounds {A} (L : OmegaVal A) f :
  oval_test f → 0 <= oval_eval L f ∧ oval_eval L f <= 1.
Proof.
  move=> Hf; split.
  - rewrite -(oval_zero (oval_laws L)).
    apply (oval_mono (oval_laws L) oval_test_zero Hf); exact (λ x, proj1 (Hf x)).
  - apply: le_trans (_ : oval_eval L (λ _, 1) <= 1).
    + apply (oval_mono (oval_laws L) Hf oval_test_one); exact (λ x, proj2 (Hf x)).
    + exact (oval_mass_le1 (oval_laws L)).
Qed.

Lemma oval_eval_ext {A} (L : OmegaVal A) f g :
  (∀ x, f x = g x) → oval_eval L f = oval_eval L g.
Proof. move=> H; congr (oval_eval L _); apply functional_extensionality; exact H. Qed.

#[global] Instance oval_eq_equivalence A : Equivalence (@oval_eq A).
Proof.
  split.
  - intros L f Hf; reflexivity.
  - intros L M H f Hf; symmetry; exact (H f Hf).
  - intros L M N H1 H2 f Hf; rewrite (H1 f Hf); exact (H2 f Hf).
Qed.
Lemma oval_le_refl {A} (L : OmegaVal A) : oval_le L L.
Proof. intros f Hf; exact: lexx. Qed.
Lemma oval_le_trans {A} (L M N : OmegaVal A) :
  oval_le L M → oval_le M N → oval_le L N.
Proof. intros H1 H2 f Hf; exact: le_trans (H1 f Hf) (H2 f Hf). Qed.
Lemma oval_le_antisym {A} (L M : OmegaVal A) :
  oval_le L M → oval_le M L → oval_eq L M.
Proof. intros H1 H2 f Hf; apply/eqP; rewrite eq_le; apply/andP; split; auto. Qed.

(** Transport laws on bounded tests only. This is the independent interface
    later used to package an existing raw evaluator, without choosing a new
    representative or assuming anything about its unbounded-test values. *)
Lemma oval_laws_ext {A} (eval eval' : (A → R) → R) :
  OmegaValLaws eval →
  (∀ f, oval_test f → eval f = eval' f) → OmegaValLaws eval'.
Proof.
  intros H He; constructor.
  - rewrite -(He _ oval_test_zero); exact (oval_zero H).
  - intros f g Hf Hg Hfg; rewrite -(He f Hf) -(He g Hg).
    exact (oval_mono H Hf Hg Hfg).
  - intros p f Hp Hp1 Hf.
    rewrite -(He _ (oval_test_scale Hp Hp1 Hf)) -(He f Hf).
    exact (oval_scale H Hp Hp1 Hf).
  - intros f g Hf Hg Hfg.
    rewrite -(He _ (oval_test_add Hf Hg Hfg)) -(He f Hf) -(He g Hg).
    exact (oval_add H Hf Hg Hfg).
  - rewrite -(He _ oval_test_one); exact (oval_mass_le1 H).
  - intros f Hf Hi; rewrite -(He _ (oval_test_sup Hf)) (oval_continuous H Hf Hi).
    apply oval_sup_ext=> n; exact (He _ (Hf n)).
Qed.

Definition oval_bottom {A} : OmegaVal A.
Proof.
  refine (@Build_OmegaVal A (λ _, 0) _); constructor.
  - reflexivity.
  - intros; exact: lexx.
  - intros; by rewrite mulr0.
  - intros; by rewrite addr0.
  - exact: ler01.
  - intros; symmetry; exact: oval_sup_const.
Defined.
Definition oval_ret {A} (x : A) : OmegaVal A.
Proof.
  refine (@Build_OmegaVal A (λ f, f x) _); constructor; try reflexivity.
  - intros f g Hf Hg Hfg; exact (Hfg x).
  - exact: lexx.
Defined.

Definition oval_bind {A B} (L : OmegaVal A) (k : A → OmegaVal B) : OmegaVal B.
Proof.
  refine (@Build_OmegaVal B (λ f, oval_eval L (λ x, oval_eval (k x) f)) _).
  have Htest : ∀ f, oval_test f -> oval_test (λ x, oval_eval (k x) f).
  { intros f Hf x; exact (oval_eval_bounds (k x) Hf). }
  constructor.
  - rewrite (_ : (λ x, oval_eval (k x) (λ _, 0)) = (λ _, 0));
      last by apply functional_extensionality=> x; apply oval_zero; apply oval_laws.
    exact (oval_zero (oval_laws L)).
  - intros f g Hf Hg Hfg; apply (oval_mono (oval_laws L) (Htest f Hf) (Htest g Hg)).
    intro x; exact (oval_mono (oval_laws (k x)) Hf Hg Hfg).
  - intros p f Hp Hp1 Hf.
    rewrite (_ : (λ x, oval_eval (k x) (λ y, p * f y)) =
      (λ x, p * oval_eval (k x) f));
      last by apply functional_extensionality=> x; apply (oval_scale (oval_laws (k x))).
    exact (oval_scale (oval_laws L) Hp Hp1 (Htest f Hf)).
  - intros f g Hf Hg Hfg.
    have He : ∀ x, oval_eval (k x) (λ y, f y + g y) =
        oval_eval (k x) f + oval_eval (k x) g :=
      λ x, oval_add (oval_laws (k x)) Hf Hg Hfg.
    rewrite (_ : (λ x, oval_eval (k x) (λ y, f y + g y)) =
        (λ x, oval_eval (k x) f + oval_eval (k x) g));
      last by apply functional_extensionality.
    apply (oval_add (oval_laws L) (Htest f Hf) (Htest g Hg)).
    intro x; rewrite -(He x).
    exact (proj2 (oval_eval_bounds (k x) (oval_test_add Hf Hg Hfg))).
  - exact (proj2 (oval_eval_bounds L (Htest _ oval_test_one))).
  - intros f Hf Hi.
    rewrite (_ : (λ x, oval_eval (k x) (oval_pointwise_sup f)) =
        oval_pointwise_sup (λ n x, oval_eval (k x) (f n)));
      last by apply functional_extensionality=> x; exact (oval_continuous (oval_laws (k x)) Hf Hi).
    apply (oval_continuous (oval_laws L)).
    + intro n; exact (Htest _ (Hf n)).
    + intros n x; exact (oval_mono (oval_laws (k x)) (Hf n) (Hf (S n)) (Hi n)).
Defined.

Definition oval_lub {A} (c : nat → OmegaVal A) (Hi : oval_increasing c) : OmegaVal A.
Proof.
  refine (@Build_OmegaVal A (λ f, oval_sup (λ n, oval_eval (c n) f)) _).
  have Hb : ∀ f, oval_test f -> ∀ n, oval_eval (c n) f <= 1 :=
    λ f Hf n, proj2 (oval_eval_bounds (c n) Hf).
  constructor.
  - transitivity (oval_sup (λ _, 0)); last exact: oval_sup_const.
    apply oval_sup_ext=> n; exact (oval_zero (oval_laws (c n))).
  - intros f g Hf Hg Hfg; apply (oval_sup_mono (Hb g Hg))=> n.
    exact (oval_mono (oval_laws (c n)) Hf Hg Hfg).
  - intros p f Hp Hp1 Hf.
    transitivity (oval_sup (λ n, p * oval_eval (c n) f)).
    + apply oval_sup_ext=> n; exact (oval_scale (oval_laws (c n)) Hp Hp1 Hf).
    + exact (oval_sup_scale Hp (Hb f Hf)).
  - intros f g Hf Hg Hfg.
    transitivity (oval_sup (λ n, oval_eval (c n) f + oval_eval (c n) g)).
    + apply oval_sup_ext=> n; exact (oval_add (oval_laws (c n)) Hf Hg Hfg).
    + apply (oval_sup_add (λ n, Hi n f Hf) (λ n, Hi n g Hg) (Hb f Hf) (Hb g Hg)).
  - exact (oval_sup_le (Hb _ oval_test_one)).
  - intros f Hf Hfi.
    transitivity (oval_sup (λ i, oval_sup (λ j, oval_eval (c i) (f j)))).
    + apply oval_sup_ext=> n; exact (oval_continuous (oval_laws (c n)) Hf Hfi).
    + apply (@oval_sup_swap _ 1)=> i j; exact (Hb _ (Hf j) i).
Defined.

Lemma oval_bottom_le {A} (L : OmegaVal A) : oval_le oval_bottom L.
Proof. intros f Hf; exact (proj1 (oval_eval_bounds L Hf)). Qed.
Lemma oval_lub_upper {A} c (Hi : @oval_increasing A c) n :
  oval_le (c n) (oval_lub Hi).
Proof. intros f Hf; exact (oval_sup_ge n (λ i, proj2 (oval_eval_bounds (c i) Hf))). Qed.
Lemma oval_lub_least {A} c (Hi : @oval_increasing A c) L :
  (∀ n, oval_le (c n) L) → oval_le (oval_lub Hi) L.
Proof. intros H f Hf; exact (oval_sup_le (λ n, H n f Hf)). Qed.
Lemma oval_lub_proper {A} c d (Hc : @oval_increasing A c) (Hd : oval_increasing d) :
  (∀ n, oval_eq (c n) (d n)) → oval_eq (oval_lub Hc) (oval_lub Hd).
Proof. intros H f Hf; apply oval_sup_ext=> n; exact (H n f Hf). Qed.

Lemma oval_bind_ret_l {A B} (x : A) (k : A → OmegaVal B) :
  oval_eq (oval_bind (oval_ret x) k) (k x).
Proof. intros f Hf; reflexivity. Qed.
Lemma oval_bind_ret_r {A} (L : OmegaVal A) : oval_eq (oval_bind L (@oval_ret A)) L.
Proof. intros f Hf; reflexivity. Qed.
Lemma oval_bind_assoc {A B C} (L : OmegaVal A) (k : A → OmegaVal B) (h : B → OmegaVal C) :
  oval_eq (oval_bind (oval_bind L k) h) (oval_bind L (λ x, oval_bind (k x) h)).
Proof. intros f Hf; reflexivity. Qed.
Lemma oval_bind_mono {A B} (L M : OmegaVal A) (k h : A → OmegaVal B) :
  oval_le L M → (∀ x, oval_le (k x) (h x)) →
  oval_le (oval_bind L k) (oval_bind M h).
Proof.
  intros HLM Hkh f Hf; cbn.
  apply: le_trans (HLM _ (λ x, oval_eval_bounds (k x) Hf)) _.
  apply (oval_mono (oval_laws M)); [intro x; exact (oval_eval_bounds (k x) Hf)|
    intro x; exact (oval_eval_bounds (h x) Hf)|intro x; exact (Hkh x f Hf)].
Qed.
Lemma oval_bind_proper {A B} (L M : OmegaVal A) (k h : A → OmegaVal B) :
  oval_eq L M → (∀ x, oval_eq (k x) (h x)) →
  oval_eq (oval_bind L k) (oval_bind M h).
Proof.
  intros HLM Hkh f Hf; cbn.
  rewrite (HLM _ (λ x, oval_eval_bounds (k x) Hf)).
  apply oval_eval_ext=> x; exact (Hkh x f Hf).
Qed.

Lemma oval_bind_chain_l {A B} c (Hi : @oval_increasing A c) (k : A → OmegaVal B) :
  oval_increasing (λ n, oval_bind (c n) k).
Proof. intro n; apply oval_bind_mono; [exact (Hi n)|intro x; apply oval_le_refl]. Qed.
Lemma oval_bind_chain_r {A B} (L : OmegaVal A) (k : nat → A → OmegaVal B) :
  (∀ x, oval_increasing (λ n, k n x)) →
  oval_increasing (λ n, oval_bind L (k n)).
Proof. intros Hi n; apply oval_bind_mono; [apply oval_le_refl|intro x; exact (Hi x n)]. Qed.
Lemma oval_bind_lub_l {A B} c (Hi : @oval_increasing A c) (k : A → OmegaVal B) :
  oval_eq (oval_bind (oval_lub Hi) k) (oval_lub (oval_bind_chain_l Hi k)).
Proof. intros f Hf; reflexivity. Qed.
Lemma oval_bind_lub_r {A B} (L : OmegaVal A) (k : nat → A → OmegaVal B)
    (Hi : ∀ x, oval_increasing (λ n, k n x)) :
  oval_eq (oval_bind L (λ x, oval_lub (Hi x)))
          (oval_lub (oval_bind_chain_r L Hi)).
Proof.
  intros f Hf; cbn; apply (oval_continuous (oval_laws L)).
  - intros n x; exact (oval_eval_bounds (k n x) Hf).
  - intros n x; exact (Hi x n f Hf).
Qed.

Lemma oval_bind_chain_diagonal {A B} c (Hc : @oval_increasing A c)
    (k : nat → A → OmegaVal B) (Hk : ∀ x, oval_increasing (λ n, k n x)) :
  oval_increasing (λ n, oval_bind (c n) (k n)).
Proof. intro n; apply oval_bind_mono; [exact (Hc n)|intro x; exact (Hk x n)]. Qed.

Lemma oval_bind_double_diagonal {A B} c (Hc : @oval_increasing A c)
    (k : nat → A → OmegaVal B) (Hk : ∀ x, oval_increasing (λ n, k n x)) :
  oval_eq (oval_bind (oval_lub Hc) (λ x, oval_lub (Hk x)))
    (oval_lub (oval_bind_chain_diagonal Hc Hk)).
Proof.
  intros f Hf.
  have Hb : ∀ i j, oval_eval (oval_bind (c i) (k j)) f <= 1 :=
    λ i j, proj2 (oval_eval_bounds _ Hf).
  have Hrow : ∀ i, oval_eval (c i) (λ x, oval_sup (λ j, oval_eval (k j x) f)) =
      oval_sup (λ j, oval_eval (oval_bind (c i) (k j)) f).
  { intro i; apply (oval_continuous (oval_laws (c i))).
    - intros j x; exact (oval_eval_bounds (k j x) Hf).
    - intros j x; exact (Hk x j f Hf). }
  change (oval_sup (λ i, oval_eval (c i) (λ x, oval_sup (λ j, oval_eval (k j x) f))) =
    oval_sup (λ n, oval_eval (oval_bind (c n) (k n)) f)).
  rewrite (oval_sup_ext Hrow).
  apply/eqP; rewrite eq_le; apply/andP; split.
  - apply oval_sup_le=> i; apply oval_sup_le=> j.
    apply: le_trans (_ : oval_eval (oval_bind (c (Nat.max i j)) (k (Nat.max i j))) f <= _).
    + apply: le_trans (_ : oval_eval (oval_bind (c (Nat.max i j)) (k j)) f <= _).
      * apply (oval_increasing_le (λ n, oval_bind_chain_l Hc (k j) n Hf) (Nat.le_max_l i j)).
      * apply (oval_increasing_le (λ n, oval_bind_chain_r (c (Nat.max i j)) Hk n Hf) (Nat.le_max_r i j)).
    + exact (oval_sup_ge (Nat.max i j) (λ n, Hb n n)).
  - apply oval_sup_le=> n.
    apply: le_trans (oval_sup_ge n (Hb n)) _.
    exact (oval_sup_ge n (λ i, oval_sup_le (Hb i))).
Qed.

(** An empty result carrier admits only missing mass.  State the law for
    any empty type, without fixing a particular empty datatype. *)
Lemma oval_empty_eq_bottom {A} (empty : A → False) (L : OmegaVal A) :
  oval_eq L oval_bottom.
Proof.
  intros f Hf. change (oval_eval L f = 0).
  rewrite (oval_eval_ext L (f := f) (g := λ _, 0));
    [exact (oval_zero (oval_laws L))|intro x; destruct (empty x)].
Qed.

Corollary oval_empty_mass {A} (empty : A → False) (L : OmegaVal A) :
  oval_mass L = 0.
Proof. exact (oval_empty_eq_bottom empty L (oval_test_one)). Qed.

Lemma oval_bottom_not_ret {A} (x : A) : ¬ oval_eq oval_bottom (oval_ret x).
Proof.
  intro H; have H01 := H (λ _, 1) (@oval_test_one A).
  change (0 = (1 : R)) in H01.
  have Hneq : (1 : R) != 0 by apply oner_neq0.
  by rewrite -H01 eqxx in Hneq.
Qed.
End Expectation.

(** Opt-in external-model order. It compares bounded expectations, not
    syntax or record fields. No semantic-interface instance is selected. *)
Declare Scope omegaval_scope.
Delimit Scope omegaval_scope with ov.
Module OmegaValNotations.
Notation "L '≤ᵥ' M" := (oval_le L M)
  (at level 70, no associativity) : omegaval_scope.
End OmegaValNotations.
