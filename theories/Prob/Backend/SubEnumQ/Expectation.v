(** Role: Finite weighted expectation and native coupling/continuity facts.
    Shared by the native SubEnumQ domain adapter and raw FreeOmega evaluators.
    No FreeOmega syntax or external domain is used here. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Program Require Import Equality.
From Coq.Arith Require Import PeanoNat.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat ssralg ssrnum order rat reals.
From mathcomp.classical Require Import classical_sets.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteAtoms FiniteScalarMap.
From PTree.Prob.Backend.EnumQ Require Import
  Representation Map Bind Coupling SemanticCoupling Measure FrontierLift Iteration.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Interface Require Import Measure Subprobability AE Coupling Omega Mixed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling
  GRing.Theory Num.Theory Order.Theory.
Import EnumQCouplingClassical.
Local Open Scope ring_scope.

Section FiniteExpectation.
Variable R : realType.

Definition enumQ_real_expect {A} (f : A -> R) (mu : EnumQ A) : R :=
  finite_expect f (finite_map_weights (ratr : {rmorphism rat -> R}) (enumQ_raw mu)).
Lemma enumQ_real_weights_nonnegative {A} (mu : EnumQ A) :
  finite_nonnegative (finite_map_weights (ratr : {rmorphism rat -> R}) (enumQ_raw mu)).
Proof.
  apply finite_map_weights_nonnegative; last exact (enumQ_nonnegative mu).
  move=> x y H; by rewrite ler_rat.
Qed.
Lemma enumQ_real_expect_rat {A} (f : A -> rat) mu :
  enumQ_real_expect (fun x => ratr (f x)) mu = ratr (enumQ_expect f mu).
Proof. exact: finite_map_weights_expect. Qed.
Lemma enumQ_real_expect_nonnegative {A} (f : A -> R) mu :
  (forall x, 0 <= f x) -> 0 <= enumQ_real_expect f mu.
Proof. apply finite_expect_nonnegative; exact: enumQ_real_weights_nonnegative. Qed.
Lemma enumQ_real_expect_mono {A} (f g : A -> R) mu :
  (forall x, f x <= g x) -> enumQ_real_expect f mu <= enumQ_real_expect g mu.
Proof. move=> H; apply finite_expect_mono; [exact: enumQ_real_weights_nonnegative|exact H]. Qed.
Lemma enumQ_real_expect_cons {A} (f : A -> R) p (Hp : 0 <= p) x mu :
  enumQ_real_expect f (enumQ_cons Hp x mu) = ratr p * f x + enumQ_real_expect f mu.
Proof. reflexivity. Qed.
Lemma enumQ_real_expect_ret {A} (f : A -> R) x :
  enumQ_real_expect f (ret_EnumQ x) = f x.
Proof. by rewrite /enumQ_real_expect /= rmorph1 mul1r addr0. Qed.

Lemma subenumQ_real_expect_bound {A} (mu : SubEnumQ A) (f : A -> R) :
  (forall x, f x <= 1) -> enumQ_real_expect f (subenumQ_raw mu) <= 1.
Proof.
  move=> Hf.
  apply: le_trans (enumQ_real_expect_mono (subenumQ_raw mu) Hf) _.
  rewrite (_ : (fun _ : A => (1 : R)) = (fun _ => ratr (1 : rat)));
    last by apply functional_extensionality=> x; rewrite rmorph1.
  rewrite enumQ_real_expect_rat.
  rewrite -(rmorph1 (ratr : {rmorphism rat -> R})) ler_rat.
  exact (subenumQ_bound mu).
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

Lemma enumQ_real_expect_zero {A} (mu : EnumQ A) :
  enumQ_real_expect (fun _ => 0) mu = 0.
Proof. exact: finite_expect_zero. Qed.

Lemma enumQ_real_expect_one {A} (mu : EnumQ A) :
  enumQ_real_expect (fun _ => 1) mu = ratr (enumQ_mass mu).
Proof.
  rewrite (_ : (fun _ : A => (1 : R)) = (fun _ => ratr (1 : rat)));
    last by apply functional_extensionality=> x; rewrite rmorph1.
  exact: enumQ_real_expect_rat.
Qed.

End FiniteExpectation.

(** Weighted numeric soundness of native coupling.  These lemmas compare
    arbitrary real-valued tests, not only rational tests or supports.
    Classical equality is confined to the native realization bridge. *)
Section NativeScalarCoupling.
Variable F : realType.
Local Notation expect := (enumQ_real_expect (R := F)).

Lemma enumQ_real_expect_app {A} (f : A -> F) mu nu :
  expect f (enumQ_app mu nu) = expect f mu + expect f nu.
Proof.
  change (finite_expect f (finite_map_weights (ratr : {rmorphism rat -> F})
    (enumQ_raw mu ++ enumQ_raw nu)) = expect f mu + expect f nu).
  by rewrite finite_map_weights_app finite_expect_app.
Qed.
Lemma enumQ_real_expect_scale {A} (f : A -> F) p (Hp : 0 <= p) mu :
  expect f (scale_EnumQ Hp mu) = ratr p * expect f mu.
Proof.
  change (finite_expect f (finite_map_weights (ratr : {rmorphism rat -> F})
    (finite_weight_map p (enumQ_raw mu))) = ratr p * expect f mu).
  by rewrite finite_map_weights_scale finite_expect_weight_map.
Qed.
Lemma enumQ_real_expect_bind {A B} (f : B -> F) (mu : EnumQ A) (k : A -> EnumQ B) :
  expect f (bind_EnumQ mu k) = expect (fun x => expect f (k x)) mu.
Proof.
  change (finite_expect f (finite_map_weights (ratr : {rmorphism rat -> F})
    (finite_bind (enumQ_raw mu) (fun x => enumQ_raw (k x)))) =
    expect (fun x => expect f (k x)) mu).
  by rewrite finite_map_weights_bind finite_expect_bind.
Qed.
Lemma enumQ_real_expect_filter_split {A : eqType} (f : A -> F) mu a :
  expect f mu = ratr (acc_mass a mu) * f a +
    expect f (enumQ_filter (fun px => px.2 != a) mu).
Proof.
  rewrite /enumQ_real_expect (finite_expect_atom_split _ f a) finite_map_weights_atom.
  change (ratr (acc_mass a mu)*f a + finite_expect f
    (List.filter (fun px => px.2 != a) (finite_map_weights (ratr : {rmorphism rat -> F}) (enumQ_raw mu))) =
    ratr (acc_mass a mu)*f a + finite_expect f
    (finite_map_weights (ratr : {rmorphism rat -> F}) (List.filter (fun px => px.2 != a) (enumQ_raw mu)))).
  by rewrite (finite_map_weights_filter (ratr : {rmorphism rat -> F}) (fun x : A => x != a) (enumQ_raw mu)).
Qed.
Lemma enumQ_real_expect_mass_zero {A : eqType} (f : A -> F) mu :
  (forall a, acc_mass a mu = 0) -> expect f mu = 0.
Proof.
  move=> H; change (expect f mu = finite_expect f nil).
  apply finite_expect_atoms_eq=> x.
  rewrite finite_map_weights_atom.
  change ((ratr (acc_mass x mu) : F) = 0); by rewrite (H x) rmorph0.
Qed.
Lemma enumQ_real_expect_eqenum {A : eqType} (f : A -> F) mu nu :
  mu ==EnumQ nu -> expect f mu = expect f nu.
Proof.
  move=> H; apply finite_expect_atoms_eq=> x.
  rewrite !finite_map_weights_atom.
  change ((ratr (acc_mass x mu) : F) = ratr (acc_mass x nu)); by rewrite (H x).
Qed.
Lemma enumQ_real_expect_emap {A B} (k : A -> B) (f : B -> F) mu :
  expect f (emap k mu) = expect (fun x => f (k x)) mu.
Proof.
  change (finite_expect f (finite_map_weights (ratr : {rmorphism rat -> F})
    (List.map (fun px => (px.1,k px.2)) (enumQ_raw mu))) = expect (fun x => f (k x)) mu).
  by rewrite finite_map_weights_map finite_expect_map.
Qed.
Lemma enumQ_real_expect_ae_mono {A} (f g : A -> F) mu :
  enumQ_ae mu (fun x => f x <= g x) -> expect f mu <= expect g mu.
Proof.
  move=> H; apply finite_expect_ae_mono; first exact: enumQ_real_weights_nonnegative.
  move=> p x /List.in_map_iff [[q y] [He Hin]] Hnz; inversion He; subst p y.
  apply (H q x Hin)=> Hq; apply Hnz; by rewrite Hq rmorph0.
Qed.

Lemma enumQ_coupling_real_expect {A B : eqType} (T : A -> B -> Prop)
    (mu : EnumQ A) (nu : EnumQ B) (f : A -> F) (g : B -> F) :
  coupling T mu nu -> (forall x y, T x y -> f x <= g y) ->
  expect f mu <= expect g nu.
Proof.
  intros [joint Hl Hr Hrel] Hfg.
  rewrite -(enumQ_real_expect_eqenum f Hl) -(enumQ_real_expect_eqenum g Hr).
  rewrite !enumQ_real_expect_emap. apply enumQ_real_expect_ae_mono.
  intros p [x y] Hin Hnz. apply Hfg, Hrel.
  exact (enumQ_entry_mass_nonzero Hin Hnz).
Qed.

Lemma subenumQ_lift_real_expect_eqtype {A B : eqType} (T : A -> B -> Prop)
    (mu : SubEnumQ A) (nu : SubEnumQ B) (f : A -> F) (g : B -> F) :
  sem_lift T mu nu -> (forall x y, T x y -> f x <= g y) ->
  expect f (subenumQ_raw mu) <= expect g (subenumQ_raw nu).
Proof. intro H. apply enumQ_coupling_real_expect. exact (enumQ_sem_lift_to_coupling H). Qed.

Theorem subenumQ_lift_real_expect {A B : Type} (T : A -> B -> Prop)
    (mu : SubEnumQ A) (nu : SubEnumQ B) (f : A -> F) (g : B -> F) :
  sem_lift T mu nu -> (forall x y, T x y -> f x <= g y) ->
  expect f (subenumQ_raw mu) <= expect g (subenumQ_raw nu).
Proof.
  exact (@subenumQ_lift_real_expect_eqtype
    (@Equality.Pack (EnumQCouplingClassical.carrier A)
      (Equality.on (EnumQCouplingClassical.carrier A)))
    (@Equality.Pack (EnumQCouplingClassical.carrier B)
      (Equality.on (EnumQCouplingClassical.carrier B))) T mu nu f g).
Qed.
End NativeScalarCoupling.

Section FiniteSuprema.
Variable R : realType.
Local Notation upper := (@countable_upper R).

Lemma scalar_increasing_le (f : nat -> R) :
  (forall n, f n <= f (S n)) ->
  forall n m, Peano.le n m -> f n <= f m.
Proof.
  intros Hinc n m Hle. induction Hle.
  - exact: lexx.
  - eapply le_trans; [exact IHHle|exact (Hinc m)].
Qed.

Lemma countable_upper_scale (f : nat -> R) p bound :
  0 <= p -> (forall n, f n <= bound) ->
  upper (fun n => p * f n) = p * upper f.
Proof.
  intros Hp Hb. destruct (eqVneq p 0) as [->|Hnz].
  - have Hz : (fun n => (0 : R) * f n) = (fun _ => 0).
    { apply functional_extensionality=> n. exact: mul0r. }
    by rewrite Hz countable_upper_constant mul0r.
  - have Hpos : 0 < p by rewrite lt0r Hnz Hp.
    have Hscaled : forall n, p * f n <= p * bound :=
      fun n => ler_wpM2l Hp (Hb n).
    apply/eqP. rewrite eq_le. apply/andP. split.
    + apply countable_upper_le. intro n. apply ler_wpM2l; [exact Hp|].
      exact (@countable_upper_ge R f bound n Hb).
    + rewrite -ler_pdivlMl //.
      apply countable_upper_le. intro n. rewrite ler_pdivlMl //.
      exact (@countable_upper_ge R (fun i => p * f i) (p * bound) n Hscaled).
Qed.

Lemma countable_upper_add (f g : nat -> R) bf bg :
  (forall n, f n <= f (S n)) -> (forall n, g n <= g (S n)) ->
  (forall n, f n <= bf) -> (forall n, g n <= bg) ->
  upper (fun n => f n + g n) = upper f + upper g.
Proof.
  intros Hf Hg Hbf Hbg.
  have Hsf : has_sup (range f).
  { split; [exists (f 0%nat); by exists 0%nat|].
    exists bf. apply/ubP=> x [n _ <-]. exact (Hbf n). }
  have Hsg : has_sup (range g).
  { split; [exists (g 0%nat); by exists 0%nat|].
    exists bg. apply/ubP=> x [n _ <-]. exact (Hbg n). }
  have Hsum : forall n, f n + g n <= bf + bg := fun n => lerD (Hbf n) (Hbg n).
  apply/eqP. rewrite eq_le. apply/andP. split.
  - apply countable_upper_le. intro n. apply lerD.
    + exact (@countable_upper_ge R f bf n Hbf).
    + exact (@countable_upper_ge R g bg n Hbg).
  - change (sup (range f) + sup (range g) <= upper (fun n => f n + g n)).
    rewrite -(sup_sumE Hsf Hsg). apply sup_le_ub.
    + exists (f 0%nat + g 0%nat), (f 0%nat).
      * by exists 0%nat.
      * exists (g 0%nat); [by exists 0%nat|reflexivity].
    + intros z [x [i _ <-] [y [j _ <-] <-]].
      eapply le_trans with (y := f (Nat.max i j) + g (Nat.max i j)).
      * apply lerD.
        -- exact (scalar_increasing_le Hf (Nat.le_max_l i j)).
        -- exact (scalar_increasing_le Hg (Nat.le_max_r i j)).
      * exact (@countable_upper_ge R (fun n => f n + g n) (bf+bg) (Nat.max i j) Hsum).
Qed.

End FiniteSuprema.

Section FiniteContinuity.
Variable R : realType.
Local Notation expect := (enumQ_real_expect (R := R)).

Lemma enumQ_real_expect_countable_ae {A} (mu : EnumQ A) (tests : nat -> A -> R) :
  (forall n x, 0 <= tests n x /\ tests n x <= 1) ->
  enumQ_ae mu (fun x => forall n, tests n x <= tests (S n) x) ->
  expect (fun x => countable_upper (fun n => tests n x)) mu =
  countable_upper (fun n => expect (tests n) mu).
Proof.
  intro Hb; apply (enumQ_ind_raw (P := fun mu =>
    enumQ_ae mu (fun x => forall n, tests n x <= tests (S n) x) ->
    expect (fun x => countable_upper (fun n => tests n x)) mu =
    countable_upper (fun n => expect (tests n) mu))).
  - move=> _; symmetry; exact: countable_upper_constant.
  - move=> p Hp x tail IH Hi; rewrite enumQ_real_expect_cons.
    have Htail : enumQ_ae tail (fun x => forall n, tests n x <= tests (S n) x).
    { intros q y Hy Hq; exact (Hi q y (or_intror Hy) Hq). }
    rewrite (IH Htail).
    have Heval : (fun n => expect (tests n) (enumQ_cons Hp x tail)) =
      (fun n => ratr p * tests n x + expect (tests n) tail).
    { reflexivity. }
    rewrite Heval; case Hzero: (p == 0).
    + move/eqP: Hzero=> Hzero.
      rewrite Hzero rmorph0 mul0r add0r.
      f_equal; apply functional_extensionality=> n; by rewrite mul0r add0r.
    + have Hx : forall n, tests n x <= tests (S n) x.
      { apply (Hi p x (or_introl (Logic.eq_refl _))); by apply/eqP; rewrite Hzero. }
      have Hreal : (0 : R) <= ratr p by rewrite ler0q.
      rewrite -(@countable_upper_scale R (fun n => tests n x) (ratr p) 1
        Hreal (fun n => proj2 (Hb n x))).
      symmetry; apply countable_upper_add with (bf := ratr p) (bg := ratr (enumQ_mass tail)).
      * move=> n; exact (ler_wpM2l Hreal (Hx n)).
      * move=> n; apply enumQ_real_expect_ae_mono=> q y Hy Hq; exact (Htail q y Hy Hq n).
      * move=> n; exact (ler_piMr Hreal (proj2 (Hb n x))).
      * move=> n; rewrite -enumQ_real_expect_one.
        apply enumQ_real_expect_mono=> y; exact (proj2 (Hb n y)).
  - move=> a b He IH; move: IH; by rewrite /enumQ_ae /enumQ_real_expect He.
Qed.

Lemma enumQ_real_expect_countable {A} (mu : EnumQ A) (tests : nat -> A -> R) :
  (forall n x, 0 <= tests n x /\ tests n x <= 1) ->
  (forall n x, tests n x <= tests (S n) x) ->
  expect (fun x => countable_upper (fun n => tests n x)) mu =
  countable_upper (fun n => expect (tests n) mu).
Proof.
  intros Hb Hi. apply enumQ_real_expect_countable_ae; [exact Hb|].
  intros p x _ _ n. exact (Hi n x).
Qed.

End FiniteContinuity.
