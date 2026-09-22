(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Program Require Import Equality.
From Coq.Arith Require Import PeanoNat.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat ssralg ssrnum order rat reals.
From mathcomp.analysis Require Import ereal.
Require Import PTree.Prob.Backend.Common.FiniteAtoms PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Bind PTree.Prob.Backend.EnumQ.Coupling PTree.Prob.Backend.EnumQ.SemanticCoupling.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.EnumQ.FrontierLift.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.EnumQ.FreeOmega.UpperExpectation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling GRing.Theory Num.Theory Order.Theory.
Import EnumQCouplingClassical.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section NativeExtendedCoupling.
Variable F : realType.
Local Notation expect := (@enumQ_extended_expect F).

Lemma enumQ_extended_expect_filter_split {A : eqType} (f : A -> \bar F) mu a :
  expect f mu = (ratr (acc_mass a mu))%:E * f a +
    expect f (enumQ_filter (fun h => snd h != a) mu).
Proof.
  apply (enumQ_ind_raw (P := fun mu =>
    expect f mu = (ratr (acc_mass a mu))%:E*f a+
      expect f (enumQ_filter (fun h => snd h != a) mu))).
  - by rewrite /enumQ_extended_expect /acc_mass /= rmorph0 mul0e add0e.
  - move=> p Hp x tail IH.
    change ((ratr p)%:E*f x+expect f tail =
      (ratr (acc_mass a (enumQ_cons Hp x tail)))%:E*f a+
      enumQ_extended_raw f (List.filter (fun h => snd h != a) ((p,x)::enumQ_raw tail))).
    rewrite acc_mass_cons /=.
    case Hxa: (x == a).
    + move/eqP: Hxa=> Hxa; subst x; rewrite /= IH.
      rewrite rmorphD EFinD ge0_muleDl; last 2 first.
      * rewrite lee_fin ler0q; exact: finite_atom_nonnegative (enumQ_nonnegative tail).
      * by rewrite lee_fin ler0q.
      by rewrite addeA [(_ * f a + _ * f a)]addeC.
    + by rewrite addr0 IH /= addeCA.
  - move=> b c He IH; move: IH; unfold enumQ_raw in He.
    by rewrite /enumQ_extended_expect /acc_mass /enumQ_filter /enumQ_raw /= He.
Qed.

Lemma enumQ_extended_expect_mass_zero {A : eqType} (f : A -> \bar F) mu :
  (forall a, acc_mass a mu = 0%R) -> expect f mu = 0.
Proof.
  apply (enumQ_ind_raw (P := fun mu =>
    (forall a, acc_mass a mu = 0%R) -> expect f mu = 0)).
  - reflexivity.
  - move=> p Hp x tail IH Hzero.
    have Hx := Hzero x; rewrite acc_mass_cons eq_refl in Hx.
    have Hatom : (0 <= acc_mass x tail)%R := finite_atom_nonnegative x (enumQ_nonnegative tail).
    have Hpzero : p = 0%R.
    { apply/eqP; have Hsum : (acc_mass x tail + p == 0)%R by rewrite Hx.
      rewrite paddr_eq0 // in Hsum; exact (proj2 (andP Hsum)). }
    change ((ratr p)%:E*f x+expect f tail=0).
    rewrite Hpzero rmorph0 mul0e add0e; apply IH=> a.
    have Ha := Hzero a; rewrite acc_mass_cons Hpzero in Ha.
    by case: (x == a) in Ha; rewrite addr0 in Ha.
  - move=> b c He IH; move: IH; by rewrite /enumQ_extended_expect /acc_mass He.
Qed.

Lemma enumQ_extended_expect_eqenum {A : eqType} (f : A -> \bar F) mu nu :
  mu ==EnumQ nu -> expect f mu = expect f nu.
Proof.
  move: mu nu; refine (enumQ_size_induction (P := fun mu => forall nu,
    mu ==EnumQ nu -> expect f mu = expect f nu) _).
  move=> mu IH nu Hmn; case Hraw: (enumQ_raw mu)=> [|[p a] tail].
  - have Hz : expect f mu = 0 by rewrite /enumQ_extended_expect Hraw.
    rewrite Hz; symmetry; apply enumQ_extended_expect_mass_zero=> x.
    rewrite -(Hmn x) /acc_mass Hraw; reflexivity.
  - rewrite (enumQ_extended_expect_filter_split f mu a)
      (enumQ_extended_expect_filter_split f nu a) (Hmn a).
    congr (_+_); apply IH.
    + change (List.length (List.filter (fun px => snd px != a) (enumQ_raw mu)) < List.length (enumQ_raw mu))%coq_nat.
      rewrite Hraw /= eq_refl /=; apply Nat.lt_succ_r; apply List.filter_length_le.
    + exact: (enumQ_filter_proper (fun x : A => x != a) Hmn).
Qed.

Lemma enumQ_extended_expect_emap {A B} (k : A -> B) (f : B -> \bar F) mu :
  expect f (emap k mu) = expect (fun x => f (k x)) mu.
Proof.
  change (enumQ_extended_raw f (List.map (fun px => (fst px,k(snd px))) (enumQ_raw mu)) =
    enumQ_extended_raw (fun x => f(k x)) (enumQ_raw mu)).
  by elim: (enumQ_raw mu)=> [|[p x] tail IH] //=; rewrite IH.
Qed.

Lemma enumQ_extended_expect_ae_mono {A} (f g : A -> \bar F) mu :
  enumQ_ae mu (fun x => f x <= g x) -> expect f mu <= expect g mu.
Proof.
  apply (enumQ_ind_raw (P := fun mu =>
    enumQ_ae mu (fun x => f x <= g x) -> expect f mu <= expect g mu)).
  - move=> _; exact: lexx.
  - move=> p Hp x tail IH Hae.
    have Htail : enumQ_ae tail (fun y => f y <= g y).
    { intros q y Hy Hq; exact (Hae q y (or_intror Hy) Hq). }
    change ((ratr p)%:E*f x+expect f tail <= (ratr p)%:E*g x+expect g tail).
    case Hzero: (p == 0%R).
    + move/eqP: Hzero=> ->; rewrite rmorph0 !mul0e !add0e; exact: IH.
    + apply: leeD (IH Htail); apply: lee_wpmul2l.
      * by rewrite lee_fin ler0q.
      * apply (Hae p x (or_introl (Logic.eq_refl _)))=> Hz.
        by rewrite Hz eq_refl in Hzero.
  - move=> b c He IH; move: IH; by rewrite /enumQ_ae /enumQ_extended_expect He.
Qed.

Lemma enumQ_coupling_extended_expect {A B : eqType} (T : A -> B -> Prop)
    (mu : EnumQ A) (nu : EnumQ B) (f : A -> \bar F) (g : B -> \bar F) :
  coupling T mu nu -> (forall x y, T x y -> f x <= g y) ->
  expect f mu <= expect g nu.
Proof.
  intros [joint Hl Hr Hrel] Hfg.
  rewrite -(enumQ_extended_expect_eqenum f Hl) -(enumQ_extended_expect_eqenum g Hr).
  rewrite !enumQ_extended_expect_emap. apply enumQ_extended_expect_ae_mono.
  intros p [x y] Hin Hnz. apply Hfg, Hrel.
  exact (enumQ_entry_mass_nonzero Hin Hnz).
Qed.

Lemma enumQ_lift_extended_expect_eqtype {A B : eqType} (T : A -> B -> Prop)
    (mu : EnumQ A) (nu : EnumQ B) (f : A -> \bar F) (g : B -> \bar F) :
  sem_lift T mu nu -> (forall x y, T x y -> f x <= g y) ->
  expect f mu <= expect g nu.
Proof. intro H. apply enumQ_coupling_extended_expect. exact (enumQ_sem_lift_to_coupling H). Qed.

Theorem enumQ_lift_extended_expect {A B : Type} (T : A -> B -> Prop)
    (mu : EnumQ A) (nu : EnumQ B) (f : A -> \bar F) (g : B -> \bar F) :
  sem_lift T mu nu -> (forall x y, T x y -> f x <= g y) ->
  expect f mu <= expect g nu.
Proof.
  exact (@enumQ_lift_extended_expect_eqtype
    (@Equality.Pack (EnumQCouplingClassical.carrier A)
      (Equality.on (EnumQCouplingClassical.carrier A)))
    (@Equality.Pack (EnumQCouplingClassical.carrier B)
      (Equality.on (EnumQCouplingClassical.carrier B))) T mu nu f g).
Qed.
End NativeExtendedCoupling.

Section RawExtendedCoupling.
Variable F : realType.
Local Notation upper := (@free_omega_extended_upper F).

Theorem free_omega_approx_extended_upper {A B} (T : A -> B -> Prop)
    (mu : FreeOmega EnumQ A) (nu : FreeOmega EnumQ B)
    (f : A -> \bar F) (g : B -> \bar F) :
  free_omega_approx T mu nu -> (forall y, 0 <= g y) ->
  (forall x y, T x y -> f x <= g y) -> upper mu f <= upper nu g.
Proof.
  intros Happrox Hg Hfg. induction Happrox; cbn [free_omega_extended_upper].
  - exact: free_omega_extended_upper_nonnegative.
  - exact (Hfg x y H).
  - apply (enumQ_lift_extended_expect H). exact H1.
  - apply extended_upper_mono. exact H0.
Qed.

Theorem free_omega_extended_upper_ae_mono {A} (mu : FreeOmega EnumQ A)
    (f g : A -> \bar F) :
  free_omega_ae (fun x => f x <= g x) mu -> upper mu f <= upper mu g.
Proof.
  induction mu as [x| |X node k IH|c IH]; intro Hae; cbn [free_omega_extended_upper].
  - dependent destruction Hae. assumption.
  - exact: lexx.
  - apply enumQ_extended_expect_ae_mono.
    change (@sem_ae EnumQ EnumQ_SemanticMeasure X node
      (fun x => upper (k x) f <= upper (k x) g)).
    eapply sem_ae_mono; [|exact (free_omega_ae_sample_inv Hae)].
    intros x Hx. exact (IH x Hx).
  - dependent destruction Hae. apply extended_upper_mono=> n. exact (IH n (H n)).
Qed.

Theorem free_omega_extended_upper_ae_ext {A} (mu : FreeOmega EnumQ A)
    (f g : A -> \bar F) :
  free_omega_ae (fun x => f x = g x) mu -> upper mu f = upper mu g.
Proof.
  intro Hae. apply/eqP. rewrite eq_le. apply/andP; split;
    apply free_omega_extended_upper_ae_mono;
    eapply free_omega_ae_mono; [|exact Hae| |exact Hae];
    intros x Hx; rewrite Hx; exact: lexx.
Qed.
Lemma free_omega_extended_upper_approx_mono {A}
    (mu nu : FreeOmega EnumQ A) (f : A -> \bar F) :
  free_omega_approx eq mu nu -> (forall x, 0 <= f x) -> upper mu f <= upper nu f.
Proof.
  intros H Hf. eapply free_omega_approx_extended_upper; [exact H|exact Hf|].
  intros x y ->. exact: lexx.
Qed.

Theorem free_omega_structural_extended_upper {A B} (T : A -> B -> Prop)
    (mu : FreeOmega EnumQ A) (nu : FreeOmega EnumQ B)
    (f : A -> \bar F) (g : B -> \bar F) :
  free_omega_lift T mu nu -> (forall y, 0 <= g y) ->
  (forall x y, T x y -> f x <= g y) -> upper mu f <= upper nu g.
Proof.
  intro H. apply free_omega_approx_extended_upper.
  exact (free_omega_lift_to_approx H).
Qed.

Theorem free_omega_cofinal_extended_upper_le {A B} (T : A -> B -> Prop)
    (left : nat -> FreeOmega EnumQ A) (right : nat -> FreeOmega EnumQ B)
    (f : A -> \bar F) (g : B -> \bar F) :
  (forall n, exists m, free_omega_approx T (left n) (right m)) ->
  (forall y, 0 <= g y) -> (forall x y, T x y -> f x <= g y) ->
  upper (FOLub left) f <= upper (FOLub right) g.
Proof.
  intros Hcover Hg Hfg. cbn [free_omega_extended_upper]. apply extended_upper_le=> n.
  destruct (Hcover n) as [m Hnm].
  eapply le_trans; [exact (free_omega_approx_extended_upper Hnm Hg Hfg)|].
  exact (extended_upper_ge (fun i => upper (right i) g) m).
Qed.

Theorem free_omega_diagonal_extended_upper {A}
    (grid : nat -> nat -> FreeOmega EnumQ A) (f : A -> \bar F) :
  (forall i j, free_omega_approx eq (grid i j) (grid i (S j))) ->
  (forall i j, free_omega_approx eq (grid i j) (grid (S i) j)) ->
  (forall x, 0 <= f x) ->
  upper (FOLub (fun i => FOLub (grid i))) f = upper (FOLub (fun n => grid n n)) f.
Proof.
  intros Hrow Hcol Hf.
  have Hcover : forall i j, free_omega_approx eq (grid i j)
      (grid (Nat.add i j) (Nat.add i j)).
  { intros i j. eapply free_omega_approx_trans with (nu := grid i (Nat.add i j)).
    - pose proof (free_omega_approx_steps (Hrow i) j i) as Hr.
      rewrite (Nat.add_comm j i) in Hr. exact Hr.
    - exact (free_omega_approx_steps (fun k => Hcol k (Nat.add i j)) i j). }
  apply/eqP. rewrite eq_le. apply/andP; split; cbn [free_omega_extended_upper].
  - apply extended_upper_le=> i. apply extended_upper_le=> j.
    eapply le_trans; [exact (free_omega_extended_upper_approx_mono (Hcover i j) Hf)|].
    exact (extended_upper_ge (fun n => upper (grid n n) f) (Nat.add i j)).
  - apply extended_upper_le=> n. eapply le_trans.
    + exact (extended_upper_ge (fun j => upper (grid n j) f) n).
    + exact (extended_upper_ge (fun i => extended_upper (fun j => upper (grid i j) f)) n).
Qed.
End RawExtendedCoupling.
