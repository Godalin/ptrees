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
From PTree.Prob.Backend Require Import RatSubTypes DiscreteMC EnumMap EnumBindFacts Coupling SemanticCouplingEnum.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.Backend Require Import TwoLevelMeasureEnum FrontierLiftEnum.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Prob.Backend.FreeOmega Require Import FreeOmegaUpperExpectationEnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum EnumMap Coupling RatSubTypes GRing.Theory Num.Theory Order.Theory.
Import EnumCouplingClassical.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section NativeExtendedCoupling.
Variable F : realType.
Local Notation expect := (@enum_extended_expect F).

Lemma enum_extended_expect_filter_split {A : eqType} (f : A -> \bar F) mu a :
  expect f mu = (ratr (Qval (acc_mass a mu)))%:E * f a +
    expect f [seq h <- mu | snd h != a].
Proof.
  induction mu as [|[p x] tail IH]; cbn [enum_extended_expect filter].
  - by rewrite /= rmorph0 mul0e add0e.
  - rewrite acc_mass_cons. destruct (x == a) eqn:Hxa.
    + move/eqP: Hxa=> Hxa. subst x. cbn. rewrite IH eq_refl /=.
      change ((ratr (Qval p))%:E * f a +
        ((ratr (Qval (acc_mass a tail)))%:E * f a + expect f [seq h <- tail | snd h != a]) =
        (ratr (Qval (acc_mass a tail) + Qval p))%:E * f a +
          expect f [seq h <- tail | snd h != a]).
      rewrite rmorphD EFinD ge0_muleDl; last 2 first;
        try by rewrite lee_fin ler0q; apply: le_nnQ0.
      rewrite !addeA. congr (_ + _). exact: addeC.
    + rewrite Hxa /= IH addr0. exact: addeCA.
Qed.

Lemma enum_extended_expect_mass_zero {A : eqType} (f : A -> \bar F) mu :
  (forall a, acc_mass a mu = 0%R) -> expect f mu = 0.
Proof.
  elim: mu=> [|[p x] tail IH] Hzero //=.
  have Hp : p = 0%R.
  { have Hx := Hzero x. rewrite acc_mass_cons eq_refl in Hx.
    apply/eqP. have Hsum : (acc_mass x tail + p == 0)%R by rewrite Hx.
    have Hparts : (acc_mass x tail == 0%R) && (p == 0%R).
    { rewrite -paddr_eq0 ?le_nnQ0 //. }
    exact (proj2 (andP Hparts)). }
  rewrite Hp /= rmorph0 mul0e add0e. apply IH=> a.
  move: (Hzero a). rewrite (@acc_mass_cons_zero _ tail a (p, x) Hp). exact.
Qed.

Lemma enum_extended_expect_eqenum {A : eqType} (f : A -> \bar F) mu nu :
  mu ==Enum nu -> expect f mu = expect f nu.
Proof.
  move: mu nu. refine (seq_strong_induction (P := fun mu => forall nu,
    mu ==Enum nu -> expect f mu = expect f nu) _).
  move=> mu IH nu Hmn. destruct mu as [|[p a] tail].
  - symmetry. apply enum_extended_expect_mass_zero=> x.
    symmetry. move: (Hmn x). cbn. exact.
  - rewrite (enum_extended_expect_filter_split f ((p,a) :: tail) a).
    rewrite (enum_extended_expect_filter_split f nu a) (Hmn a).
    congr (_ + _). apply IH.
    + apply/ssrnat.ltP. rewrite size_filter /= eq_refl /=.
      apply/ssrnat.ltP. exact: leq_ltn_trans (count_size _ _) (ltnSn _).
    + exact: (enum_filter_proper (fun x : A => x != a) Hmn).
Qed.

Lemma enum_extended_expect_emap {A B} (k : A -> B) (f : B -> \bar F) mu :
  expect f (emap k mu) = expect (fun x => f (k x)) mu.
Proof. by elim: mu=> [|[p x] tail IH] //=; rewrite IH. Qed.

Lemma enum_extended_expect_ae_mono {A} (f g : A -> \bar F) mu :
  enum_ae mu (fun x => f x <= g x) -> expect f mu <= expect g mu.
Proof.
  induction mu as [|[p x] tail IH]; intro Hae; cbn [enum_extended_expect].
  - exact: lexx.
  - destruct (p == nnQ_0) eqn:Hp.
    + move/eqP: Hp=> ->. cbn [Qval nnQ_0]. rewrite rmorph0 !mul0e !add0e.
      apply IH. intros q y Hy Hq. apply (Hae q y (or_intror Hy) Hq).
    + have Htail : enum_ae tail (fun y => f y <= g y).
      { intros q y Hy Hq. apply (Hae q y (or_intror Hy) Hq). }
      apply: leeD (IH Htail).
      have Hpx : f x <= g x.
      { apply (Hae p x (or_introl (Logic.eq_refl (p,x)))).
        intro Hz. rewrite Hz eq_refl in Hp. discriminate. }
      apply: lee_wpmul2l Hpx.
      by rewrite lee_fin ler0q; apply le_nnQ0.
Qed.

Lemma enum_coupling_extended_expect {A B : eqType} (T : A -> B -> Prop)
    (mu : Enum A) (nu : Enum B) (f : A -> \bar F) (g : B -> \bar F) :
  coupling T mu nu -> (forall x y, T x y -> f x <= g y) ->
  expect f mu <= expect g nu.
Proof.
  intros [joint Hl Hr Hrel] Hfg.
  rewrite -(enum_extended_expect_eqenum f Hl) -(enum_extended_expect_eqenum g Hr).
  rewrite !enum_extended_expect_emap. apply enum_extended_expect_ae_mono.
  intros p [x y] Hin Hnz. apply Hfg, Hrel.
  exact (enum_entry_mass_nonzero Hin Hnz).
Qed.

Lemma enum_lift_extended_expect_eqtype {A B : eqType} (T : A -> B -> Prop)
    (mu : Enum A) (nu : Enum B) (f : A -> \bar F) (g : B -> \bar F) :
  sem_lift T mu nu -> (forall x y, T x y -> f x <= g y) ->
  expect f mu <= expect g nu.
Proof. intro H. apply enum_coupling_extended_expect. exact (enum_sem_lift_to_coupling H). Qed.

Theorem enum_lift_extended_expect {A B : Type} (T : A -> B -> Prop)
    (mu : Enum A) (nu : Enum B) (f : A -> \bar F) (g : B -> \bar F) :
  sem_lift T mu nu -> (forall x y, T x y -> f x <= g y) ->
  expect f mu <= expect g nu.
Proof.
  exact (@enum_lift_extended_expect_eqtype
    (@Equality.Pack (EnumCouplingClassical.carrier A)
      (Equality.on (EnumCouplingClassical.carrier A)))
    (@Equality.Pack (EnumCouplingClassical.carrier B)
      (Equality.on (EnumCouplingClassical.carrier B))) T mu nu f g).
Qed.
End NativeExtendedCoupling.

Section RawExtendedCoupling.
Variable F : realType.
Local Notation upper := (@free_omega_extended_upper F).

Theorem free_omega_approx_extended_upper {A B} (T : A -> B -> Prop)
    (mu : FreeOmega Enum A) (nu : FreeOmega Enum B)
    (f : A -> \bar F) (g : B -> \bar F) :
  free_omega_approx T mu nu -> (forall y, 0 <= g y) ->
  (forall x y, T x y -> f x <= g y) -> upper mu f <= upper nu g.
Proof.
  intros Happrox Hg Hfg. induction Happrox; cbn [free_omega_extended_upper].
  - exact: free_omega_extended_upper_nonnegative.
  - exact (Hfg x y H).
  - apply (enum_lift_extended_expect H). exact H1.
  - apply extended_upper_mono. exact H0.
Qed.

Theorem free_omega_extended_upper_ae_mono {A} (mu : FreeOmega Enum A)
    (f g : A -> \bar F) :
  free_omega_ae (fun x => f x <= g x) mu -> upper mu f <= upper mu g.
Proof.
  induction mu as [x| |X node k IH|c IH]; intro Hae; cbn [free_omega_extended_upper].
  - dependent destruction Hae. assumption.
  - exact: lexx.
  - apply enum_extended_expect_ae_mono.
    change (@sem_ae Enum Enum_SemanticMeasure X node
      (fun x => upper (k x) f <= upper (k x) g)).
    eapply sem_ae_mono; [|exact (free_omega_ae_sample_inv Hae)].
    intros x Hx. exact (IH x Hx).
  - dependent destruction Hae. apply extended_upper_mono=> n. exact (IH n (H n)).
Qed.

Theorem free_omega_extended_upper_ae_ext {A} (mu : FreeOmega Enum A)
    (f g : A -> \bar F) :
  free_omega_ae (fun x => f x = g x) mu -> upper mu f = upper mu g.
Proof.
  intro Hae. apply/eqP. rewrite eq_le. apply/andP; split;
    apply free_omega_extended_upper_ae_mono;
    eapply free_omega_ae_mono; [|exact Hae| |exact Hae];
    intros x Hx; rewrite Hx; exact: lexx.
Qed.
Lemma free_omega_extended_upper_approx_mono {A}
    (mu nu : FreeOmega Enum A) (f : A -> \bar F) :
  free_omega_approx eq mu nu -> (forall x, 0 <= f x) -> upper mu f <= upper nu f.
Proof.
  intros H Hf. eapply free_omega_approx_extended_upper; [exact H|exact Hf|].
  intros x y ->. exact: lexx.
Qed.

Theorem free_omega_structural_extended_upper {A B} (T : A -> B -> Prop)
    (mu : FreeOmega Enum A) (nu : FreeOmega Enum B)
    (f : A -> \bar F) (g : B -> \bar F) :
  free_omega_lift T mu nu -> (forall y, 0 <= g y) ->
  (forall x y, T x y -> f x <= g y) -> upper mu f <= upper nu g.
Proof.
  intro H. apply free_omega_approx_extended_upper.
  exact (free_omega_lift_to_approx H).
Qed.

Theorem free_omega_cofinal_extended_upper_le {A B} (T : A -> B -> Prop)
    (left : nat -> FreeOmega Enum A) (right : nat -> FreeOmega Enum B)
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
    (grid : nat -> nat -> FreeOmega Enum A) (f : A -> \bar F) :
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
