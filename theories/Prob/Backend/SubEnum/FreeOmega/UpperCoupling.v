(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Program Require Import Equality.
From Coq.Arith Require Import PeanoNat.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat ssralg ssrnum order rat reals.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.Enum.Representation PTree.Prob.Backend.Enum.Map PTree.Prob.Backend.Enum.Bind PTree.Prob.Backend.Enum.Coupling PTree.Prob.Backend.Enum.SemanticCoupling.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.Enum.Measure PTree.Prob.Backend.SubEnum.Measure PTree.Prob.Backend.Enum.FrontierLift.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnum.FreeOmega.UpperExpectation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum PTree.Prob.Backend.Enum.Map PTree.Prob.Backend.Enum.Coupling RatSubTypes GRing.Theory Num.Theory Order.Theory.
Import EnumCouplingClassical.
Local Open Scope ring_scope.

(** Weighted numeric soundness of native coupling.  These lemmas compare
    arbitrary real-valued tests, not only rational tests or supports.
    Classical equality is confined to the native realization bridge. *)
Section NativeScalarCoupling.
Variable F : realType.
Local Notation expect := (enum_real_expect (R := F)).

Lemma enum_real_expect_app {A} (f : A -> F) mu nu :
  expect f (mu ++ nu) = expect f mu + expect f nu.
Proof. by elim: mu=> [|[p x] tail IH] /=; rewrite ?add0r ?IH ?addrA. Qed.

Lemma enum_real_expect_scale {A} (f : A -> F) p mu :
  expect f (scale_Enum p mu) = ratr (Qval p) * expect f mu.
Proof.
  elim: mu=> [|[q x] tail IH] /=; first by rewrite mulr0.
  rewrite IH mulrDr. congr (_ + _).
  change (ratr (Qval p * Qval q) * f x = ratr (Qval p) * (ratr (Qval q) * f x)).
  by rewrite rmorphM mulrA.
Qed.

Lemma enum_real_expect_bind {A B} (f : B -> F) (mu : Enum A) (k : A -> Enum B) :
  expect f (bind_Enum mu k) = expect (fun x => expect f (k x)) mu.
Proof.
  by elim: mu=> [|[p x] tail IH] //=; rewrite enum_real_expect_app enum_real_expect_scale IH.
Qed.

Lemma enum_real_expect_filter_split {A : eqType} (f : A -> F) mu a :
  expect f mu = ratr (Qval (acc_mass a mu)) * f a +
    expect f [seq h <- mu | snd h != a].
Proof.
  induction mu as [|[p x] tail IH]; cbn [enum_real_expect filter].
  - by rewrite /= rmorph0 mul0r add0r.
  - rewrite acc_mass_cons. destruct (x == a) eqn:Hxa.
    + move/eqP: Hxa=> Hxa. subst x. cbn. rewrite IH eq_refl /=.
      change (ratr (Qval p) * f a +
        (ratr (Qval (acc_mass a tail)) * f a + expect f [seq h <- tail | snd h != a]) =
        ratr (Qval (acc_mass a tail) + Qval p) * f a +
          expect f [seq h <- tail | snd h != a]).
      rewrite rmorphD mulrDl !addrA. congr (_ + _). exact: addrC.
    + rewrite Hxa /= IH addr0. exact: addrCA.
Qed.

Lemma enum_real_expect_mass_zero {A : eqType} (f : A -> F) mu :
  (forall a, acc_mass a mu = 0) -> expect f mu = 0.
Proof.
  elim: mu=> [|[p x] tail IH] Hzero //=.
  have Hp : p = 0.
  { have Hx := Hzero x. rewrite acc_mass_cons eq_refl in Hx.
    apply/eqP. have Hsum : acc_mass x tail + p == 0 by rewrite Hx.
    have Hparts : (acc_mass x tail == 0) && (p == 0).
    { rewrite -paddr_eq0 ?le_nnQ0 //. }
    exact (proj2 (andP Hparts)). }
  rewrite Hp /= rmorph0 mul0r add0r. apply IH=> a.
  move: (Hzero a). rewrite (@acc_mass_cons_zero _ tail a (p, x) Hp). exact.
Qed.

Lemma enum_real_expect_eqenum {A : eqType} (f : A -> F) mu nu :
  mu ==Enum nu -> expect f mu = expect f nu.
Proof.
  move: mu nu. refine (seq_strong_induction (P := fun mu => forall nu,
    mu ==Enum nu -> expect f mu = expect f nu) _).
  move=> mu IH nu Hmn. destruct mu as [|[p a] tail].
  - symmetry. apply enum_real_expect_mass_zero=> x.
    symmetry. move: (Hmn x). cbn. exact.
  - rewrite (enum_real_expect_filter_split f ((p,a) :: tail) a).
    rewrite (enum_real_expect_filter_split f nu a) (Hmn a).
    congr (_ + _). apply IH.
    + apply/ssrnat.ltP. rewrite size_filter /= eq_refl /=.
      apply/ssrnat.ltP. exact: leq_ltn_trans (count_size _ _) (ltnSn _).
    + exact: (enum_filter_proper (fun x : A => x != a) Hmn).
Qed.

Lemma enum_real_expect_emap {A B} (k : A -> B) (f : B -> F) mu :
  expect f (emap k mu) = expect (fun x => f (k x)) mu.
Proof. by elim: mu=> [|[p x] tail IH] //=; rewrite IH. Qed.

Lemma enum_real_expect_ae_mono {A} (f g : A -> F) mu :
  enum_ae mu (fun x => f x <= g x) -> expect f mu <= expect g mu.
Proof.
  induction mu as [|[p x] tail IH]; intro Hae; cbn [enum_real_expect].
  - exact: lexx.
  - destruct (p == nnQ_0) eqn:Hp.
    + move/eqP: Hp=> ->. cbn [Qval nnQ_0]. rewrite rmorph0 !mul0r !add0r.
      apply IH. intros q y Hy Hq. apply (Hae q y (or_intror Hy) Hq).
    + apply lerD.
      * apply ler_wpM2l; [by rewrite ler0q; apply Qval_nnQ_ge0|].
        apply (Hae p x (or_introl (Logic.eq_refl (p,x)))).
        intro Hz. rewrite Hz eq_refl in Hp. discriminate.
      * apply IH. intros q y Hy Hq. apply (Hae q y (or_intror Hy) Hq).
Qed.

Lemma enum_coupling_real_expect {A B : eqType} (T : A -> B -> Prop)
    (mu : Enum A) (nu : Enum B) (f : A -> F) (g : B -> F) :
  coupling T mu nu -> (forall x y, T x y -> f x <= g y) ->
  expect f mu <= expect g nu.
Proof.
  intros [joint Hl Hr Hrel] Hfg.
  rewrite -(enum_real_expect_eqenum f Hl) -(enum_real_expect_eqenum g Hr).
  rewrite !enum_real_expect_emap. apply enum_real_expect_ae_mono.
  intros p [x y] Hin Hnz. apply Hfg, Hrel.
  exact (enum_entry_mass_nonzero Hin Hnz).
Qed.

Lemma subenum_lift_real_expect_eqtype {A B : eqType} (T : A -> B -> Prop)
    (mu : SubEnum A) (nu : SubEnum B) (f : A -> F) (g : B -> F) :
  sem_lift T mu nu -> (forall x y, T x y -> f x <= g y) ->
  expect f (subenum_raw mu) <= expect g (subenum_raw nu).
Proof. intro H. apply enum_coupling_real_expect. exact (enum_sem_lift_to_coupling H). Qed.

Theorem subenum_lift_real_expect {A B : Type} (T : A -> B -> Prop)
    (mu : SubEnum A) (nu : SubEnum B) (f : A -> F) (g : B -> F) :
  sem_lift T mu nu -> (forall x y, T x y -> f x <= g y) ->
  expect f (subenum_raw mu) <= expect g (subenum_raw nu).
Proof.
  exact (@subenum_lift_real_expect_eqtype
    (@Equality.Pack (EnumCouplingClassical.carrier A)
      (Equality.on (EnumCouplingClassical.carrier A)))
    (@Equality.Pack (EnumCouplingClassical.carrier B)
      (Equality.on (EnumCouplingClassical.carrier B))) T mu nu f g).
Qed.
End NativeScalarCoupling.

(** Raw finite-subbehavior order is numerically monotone even on arbitrary
    formal Lub terms.  This is a proved bridge to the numeric model, not
    a new order/reflection capability imposed on the backend. *)
Section RawScalarCoupling.
Variable F : realType.
Local Notation upper := (free_omega_upper (R := F)).

Theorem free_omega_sample_bind_upper {A X Y} (mu : SubEnum X)
    (k : X -> SubEnum Y) (h : Y -> FreeOmega SubEnum A) (f : A -> F) :
  upper (FOSample mu (fun x => FOSample (k x) h)) f =
  upper (FOSample (subenum_bind mu k) h) f.
Proof. cbn [free_omega_upper subenum_bind subenum_raw]. symmetry. apply enum_real_expect_bind. Qed.

Theorem free_omega_approx_upper {A B} (T : A -> B -> Prop)
    (mu : FreeOmega SubEnum A) (nu : FreeOmega SubEnum B)
    (f : A -> F) (g : B -> F) :
  free_omega_approx T mu nu ->
  (forall y, 0 <= g y /\ g y <= 1) ->
  (forall x y, T x y -> f x <= g y) -> upper mu f <= upper nu g.
Proof.
  intros Happrox Hg Hfg. induction Happrox; cbn [free_omega_upper].
  - exact (proj1 (free_omega_upper_bounds nu Hg)).
  - exact (Hfg x y H).
  - apply (subenum_lift_real_expect H). exact H1.
  - apply countable_upper_le. intro n. apply: le_trans (H0 n) _.
    exact (@countable_upper_ge F (fun i => upper (d i) g) 1 n
      (fun i => proj2 (free_omega_upper_bounds (d i) Hg))).
Qed.

Theorem free_omega_structural_upper {A B} (T : A -> B -> Prop)
    (mu : FreeOmega SubEnum A) (nu : FreeOmega SubEnum B)
    (f : A -> F) (g : B -> F) :
  free_omega_lift T mu nu ->
  (forall y, 0 <= g y /\ g y <= 1) ->
  (forall x y, T x y -> f x <= g y) -> upper mu f <= upper nu g.
Proof. intro H. apply free_omega_approx_upper. exact (free_omega_lift_to_approx H). Qed.

Theorem free_omega_upper_ae_mono {A} (mu : FreeOmega SubEnum A)
    (f g : A -> F) :
  (forall y, 0 <= g y /\ g y <= 1) ->
  free_omega_ae (fun x => f x <= g x) mu -> upper mu f <= upper mu g.
Proof.
  intro Hg. induction mu as [x| |X node k IH|chain IH]; intro Hae;
    cbn [free_omega_upper].
  - dependent destruction Hae. assumption.
  - exact: lexx.
  - apply enum_real_expect_ae_mono.
    change (@sem_ae SubEnum SubEnum_SemanticMeasure X node
      (fun x => upper (k x) f <= upper (k x) g)).
    eapply sem_ae_mono; [|exact (free_omega_ae_sample_inv Hae)].
    intros x Hx. exact (IH x Hx).
  - dependent destruction Hae. apply countable_upper_le. intro n.
    apply: le_trans (IH n (H n)) _.
    exact (@countable_upper_ge F (fun i => upper (chain i) g) 1 n
      (fun i => proj2 (free_omega_upper_bounds (chain i) Hg))).
Qed.

Theorem free_omega_upper_ae_ext {A} (mu : FreeOmega SubEnum A)
    (f g : A -> F) :
  (forall x, 0 <= f x /\ f x <= 1) ->
  (forall y, 0 <= g y /\ g y <= 1) ->
  free_omega_ae (fun x => f x = g x) mu -> upper mu f = upper mu g.
Proof.
  intros Hf Hg Hae. apply/eqP. rewrite eq_le. apply/andP. split.
  - apply free_omega_upper_ae_mono; [exact Hg|].
    eapply free_omega_ae_mono; [|exact Hae].
    intros x Hx. rewrite Hx. exact: lexx.
  - apply free_omega_upper_ae_mono; [exact Hf|].
    eapply free_omega_ae_mono; [|exact Hae].
    intros x Hx. rewrite Hx. exact: lexx.
Qed.

Lemma free_omega_upper_approx_mono {A} (mu nu : FreeOmega SubEnum A) (f : A -> F) :
  free_omega_approx eq mu nu ->
  (forall x, 0 <= f x /\ f x <= 1) -> upper mu f <= upper nu f.
Proof.
  intros H Hf. eapply free_omega_approx_upper; [exact H|exact Hf|].
  intros x y ->. exact: lexx.
Qed.

(** One-sided cofinal domination already suffices for the corresponding
    numeric inequality; mutual domination gives equality below.  No
    quotient conclusion is used in either proof. *)
Theorem free_omega_cofinal_upper_le {A B} (T : A -> B -> Prop)
    (left : nat -> FreeOmega SubEnum A) (right : nat -> FreeOmega SubEnum B)
    (f : A -> F) (g : B -> F) :
  (forall n, exists m, free_omega_approx T (left n) (right m)) ->
  (forall y, 0 <= g y /\ g y <= 1) ->
  (forall x y, T x y -> f x <= g y) ->
  upper (FOLub left) f <= upper (FOLub right) g.
Proof.
  intros Hcover Hg Hfg. cbn [free_omega_upper]. apply countable_upper_le. intro n.
  destruct (Hcover n) as [m Hnm].
  eapply le_trans; [exact (free_omega_approx_upper Hnm Hg Hfg)|].
  exact (@countable_upper_ge F (fun i => upper (right i) g) 1 m
    (fun i => proj2 (free_omega_upper_bounds (right i) Hg))).
Qed.

Theorem free_omega_cofinal_upper_eq {A}
    (left right : nat -> FreeOmega SubEnum A) (f : A -> F) :
  free_omega_chains_cofinal eq left right ->
  (forall x, 0 <= f x /\ f x <= 1) ->
  upper (FOLub left) f = upper (FOLub right) f.
Proof.
  intros [Hl Hr] Hf. apply/eqP. rewrite eq_le. apply/andP. split.
  - eapply free_omega_cofinal_upper_le; [exact Hl|exact Hf|].
    intros x y ->. exact: lexx.
  - eapply free_omega_cofinal_upper_le; [exact Hr|exact Hf|].
    intros x y ->. exact: lexx.
Qed.

(** Numeric validation of the same monotone-grid hypothesis used by
    FOQLDoubleDiagonal.  Suprema commute with the diagonal because every
    grid cell is dominated by a later diagonal cell, not because arbitrary
    convergent double sequences may be exchanged. *)
Theorem free_omega_diagonal_upper {A}
    (grid : nat -> nat -> FreeOmega SubEnum A) (f : A -> F) :
  (forall i j, free_omega_approx eq (grid i j) (grid i (S j))) ->
  (forall i j, free_omega_approx eq (grid i j) (grid (S i) j)) ->
  (forall x, 0 <= f x /\ f x <= 1) ->
  upper (FOLub (fun i => FOLub (grid i))) f =
  upper (FOLub (fun n => grid n n)) f.
Proof.
  intros Hrow Hcol Hf.
  have Hbound : forall i j, upper (grid i j) f <= 1 :=
    fun i j => proj2 (free_omega_upper_bounds (grid i j) Hf).
  have Hcover : forall i j, free_omega_approx eq (grid i j)
      (grid (Nat.add i j) (Nat.add i j)).
  { intros i j. eapply free_omega_approx_trans with (nu := grid i (Nat.add i j)).
    - pose proof (free_omega_approx_steps (Hrow i) j i) as Hr.
      rewrite (Nat.add_comm j i) in Hr. exact Hr.
    - exact (free_omega_approx_steps (fun k => Hcol k (Nat.add i j)) i j). }
  apply/eqP. rewrite eq_le. apply/andP. split; cbn [free_omega_upper].
  - apply countable_upper_le. intro i. apply countable_upper_le. intro j.
    eapply le_trans; [exact (free_omega_upper_approx_mono (Hcover i j) Hf)|].
    exact (@countable_upper_ge F (fun n => upper (grid n n) f) 1 (Nat.add i j)
      (fun n => Hbound n n)).
  - apply countable_upper_le. intro n.
    eapply le_trans.
    + exact (@countable_upper_ge F (fun j => upper (grid n j) f) 1 n (Hbound n)).
    + exact (@countable_upper_ge F
        (fun i => countable_upper (fun j => upper (grid i j) f)) 1 n
        (fun i => countable_upper_le (Hbound i))).
Qed.
End RawScalarCoupling.
