Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import List.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg order rat.
From PTree.Prob Require Import RatSubTypes DiscreteMC Coupling IndexedCoupling
  EnumBindFacts EnumMap FrontierLift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum Coupling IndexedCoupling.
Import GRing.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Lemma nnq_mul_ne_zero (p q : nnQ) :
  p != RatSubTypes.nnQ_0 -> q != RatSubTypes.nnQ_0 ->
  p * q != RatSubTypes.nnQ_0.
Proof.
  rewrite !RatSubTypes.lt_0_nnQ_iff_ne_0.
  move=> Hp Hq. apply RatSubTypes.lt_nnQ_of_lt_Q.
  exact: ssrnum.Num.Theory.mulr_gt0 Hp Hq.
Qed.

Fixpoint enum_prune {A} (mu : Enum A) : Enum A :=
  match mu with
  | [::] => [::]
  | (p, x) :: tl =>
      if p == RatSubTypes.nnQ_0
      then enum_prune tl
      else (p, x) :: enum_prune tl
  end.

Lemma enum_prune_app {A} (mu nu : Enum A) :
  enum_prune (mu ++ nu) = enum_prune mu ++ enum_prune nu.
Proof.
  elim: mu=> [//=|[p x] mu IH] //=.
  by case: (p == RatSubTypes.nnQ_0); rewrite IH.
Qed.

Lemma enum_prune_emap {A B} (f : A -> B) (mu : Enum A) :
  enum_prune (emap f mu) = emap f (enum_prune mu).
Proof.
  elim: mu=> [|[p a] mu IH] //=.
  by case: (p == RatSubTypes.nnQ_0); rewrite /= IH.
Qed.

Lemma enum_prune_eqenum {A : eqType} (mu : Enum A) :
  enum_prune mu ==Enum mu.
Proof.
  move=> a. elim: mu=> [|[p x] mu IH] //=.
  case Hp: (p == RatSubTypes.nnQ_0).
  - have Hp0 : p = 0.
    { rewrite (eqP Hp). apply val_inj. reflexivity. }
    rewrite (@acc_mass_cons_zero A mu a (p, x) Hp0). exact IH.
  - rewrite !acc_mass_cons IH. reflexivity.
Qed.

Lemma enum_prune_scale_zero {A} (mu : Enum A) :
  enum_prune (scale_Enum RatSubTypes.nnQ_0 mu) = [::].
Proof.
  elim: mu=> [//=|[p x] mu IH] //=.
  have Hz : RatSubTypes.nnQ_0 * p = RatSubTypes.nnQ_0.
    apply val_inj. cbn. exact: mul0r (Qval p).
  by rewrite Hz eq_refl IH.
Qed.

Lemma enum_prune_scale {A} (p : nnQ) (mu : Enum A) :
  enum_prune (scale_Enum p mu) =
  if p == RatSubTypes.nnQ_0 then [::]
  else scale_Enum p (enum_prune mu).
Proof.
  case Hp: (p == RatSubTypes.nnQ_0).
  - move/eqP: Hp=> ->. exact: enum_prune_scale_zero mu.
  - elim: mu=> [//=|[q x] mu IH] //=.
    case Hq: (q == RatSubTypes.nnQ_0).
    + move/eqP: Hq=> Hq0.
      have Hpq0 : p * q = RatSubTypes.nnQ_0.
      { rewrite Hq0. apply val_inj. cbn. exact: mulr0 (Qval p). }
      rewrite Hpq0 eq_refl. exact IH.
    + have Hpn : p != RatSubTypes.nnQ_0 by rewrite Hp.
      have Hqn : q != RatSubTypes.nnQ_0 by rewrite Hq.
      have Hpq := nnq_mul_ne_zero Hpn Hqn.
      rewrite (negPf Hpq) IH. reflexivity.
Qed.

(** Almost-everywhere for a finite enumeration: a property is required only
    at entries carrying non-zero mass.  This definition needs no equality on
    the sampled type. *)
Definition enum_ae {A} (mu : Enum A) (P : A -> Prop) : Prop :=
  forall p x, List.In (p, x) mu -> p <> RatSubTypes.nnQ_0 -> P x.

(** The operational instance is fully generic in its carriers.  Its
    [meas_lift] is the existing position-indexed coupling, which avoids an
    [eqType] requirement on values such as event continuations. *)
Definition enum_meas_eq {A} (mu nu : Enum A) : Prop :=
  indexed_coupling eq (enum_prune mu) (enum_prune nu).

(** Literal list equality is only representation equality.  The semantic
    equality below is insensitive to zero entries, ordering, duplicates and
    splitting a weight into several entries. *)
Definition enum_repr_eq {A} (mu nu : Enum A) : Prop := mu = nu.

Lemma enum_meas_eq_of_eqenum {A : eqType} (mu nu : Enum A) :
  mu ==Enum nu -> enum_meas_eq mu nu.
Proof.
  move=> Hmn. apply indexed_coupling_of_coupling.
  apply coupling_of_enum_eq.
  eapply enum_eq_trans; first exact: enum_prune_eqenum.
  eapply enum_eq_trans; first exact Hmn.
  apply enum_eq_sym. exact: enum_prune_eqenum.
Qed.

Lemma enum_repr_eq_implies_meas_eq {A} (mu nu : Enum A) :
  enum_repr_eq mu nu -> enum_meas_eq mu nu.
Proof. move=> ->. apply indexed_coupling_refl. reflexivity. Qed.

#[global] Instance Enum_MeasureInterface : MeasureInterface Enum := {
  meas_ret := @ret_Enum;
  meas_bind := @bind_Enum;
  meas_eq := @enum_meas_eq;
  meas_ae := @enum_ae;
  meas_lift := fun A B R mu nu =>
    indexed_coupling R (enum_prune mu) (enum_prune nu)
}.

#[global] Instance Enum_MeasureCoreLaws :
    @MeasureCoreLaws Enum Enum_MeasureInterface.
Proof.
  constructor.
  - move=> A mu P Q HPQ Hae p x Hin Hnz.
    exact: HPQ (Hae p x Hin Hnz).
  - move=> A B R S mu nu HRS Hlift.
    exact: indexed_coupling_mono HRS Hlift.
  - move=> A R mu HR.
    exact: indexed_coupling_refl HR.
  - move=> A B R x y Hxy. cbn.
    eapply coupling_mono; [|apply coupling_refl].
    move=> i j Hij. subst j. destruct i as [|i].
    + split.
      * move=> p a Hi. cbn in Hi. inversion Hi; subst.
        eexists; exists y. split=> //.
      * move=> q b Hj. cbn in Hj. inversion Hj; subst.
        eexists; exists x. split=> //.
    + split; move=> p a Hbad; cbn in Hbad;
        destruct i; discriminate.
Qed.

#[global] Instance Enum_MeasureLaws :
    @MeasureLaws Enum Enum_MeasureInterface Enum_MeasureCoreLaws.
Proof.
  constructor.
  - move=> A mu. cbn. apply indexed_coupling_refl. reflexivity.
  - move=> A mu nu H. cbn in H |- *.
    exact: indexed_coupling_sym H.
  - move=> A mu nu xi H1 H2. cbn in H1, H2 |- *.
    eapply indexed_coupling_mono.
    + move=> x z [y [-> ->]]. reflexivity.
    + exact: indexed_coupling_comp H1 H2.
  - move=> A mu p x Hin Hnz. exact I.
  - move=> A mu P Q HP HQ p x Hin Hnz.
    split; [exact: HP p x Hin Hnz|exact: HQ p x Hin Hnz].
  - move=> A B R mu mu' nu Hmu Hlift.
    cbn in Hmu, Hlift |- *.
    have Hcomp := indexed_coupling_comp Hmu Hlift.
    eapply indexed_coupling_mono; [|exact Hcomp].
    move=> x y [z [-> Hzy]]. exact Hzy.
  - move=> A B R mu nu nu' Hnu Hlift.
    cbn in Hnu, Hlift |- *.
    have Hcomp := indexed_coupling_comp Hlift Hnu.
    eapply indexed_coupling_mono; [|exact Hcomp].
    move=> x y [z [Hxz ->]]. exact Hxz.
  - move=> A B R mu nu H. exact: indexed_coupling_sym H.
  - move=> A B C R S mu nu xi H1 H2.
    exact: indexed_coupling_comp H1 H2.
Qed.

Lemma enum_prune_bind_ae {A B} (mu : Enum A) (k1 k2 : A -> Enum B) :
  enum_ae mu (fun x => enum_prune (k1 x) = enum_prune (k2 x)) ->
  enum_prune (bind_Enum mu k1) = enum_prune (bind_Enum mu k2).
Proof.
  move=> Hae. elim: mu Hae=> [|[p x] mu IH] Hae //=.
  rewrite !enum_prune_app !enum_prune_scale.
  have Htail : enum_ae mu
      (fun y => enum_prune (k1 y) = enum_prune (k2 y)).
  { move=> q y Hin Hq. exact: Hae q y (or_intror Hin) Hq. }
  rewrite (IH Htail).
  case Hp: (p == RatSubTypes.nnQ_0)=> //=.
  have Hpn : p <> RatSubTypes.nnQ_0.
    move=> Heq. subst p. by rewrite eq_refl in Hp.
  have Hhead := Hae p x
    (or_introl (Logic.eq_refl (p, x))) Hpn.
  by rewrite Hhead.
Qed.

(** Pruning commutes exactly with finite Kleisli extension.  This exposes a
    bind as a concatenation of non-zero blocks, which is the normal form used
    by position-indexed couplings. *)
Lemma enum_prune_bind {A B} (mu : Enum A) (k : A -> Enum B) :
  enum_prune (bind_Enum mu k) =
  bind_Enum (enum_prune mu) (fun x => enum_prune (k x)).
Proof.
  elim: mu=> [|[p x] mu IH] //=.
  rewrite enum_prune_app enum_prune_scale IH.
  case Hp: (p == RatSubTypes.nnQ_0)=> //=.
Qed.

Lemma scale_entry_preimage {A} (p w : nnQ) (x : A) (mu : Enum A) :
  List.In (w, x) (scale_Enum p mu) ->
  exists q, List.In (q, x) mu /\ w = p * q.
Proof.
  elim: mu=> [//|[q y] mu IH] /=.
  move=> [Hhead|Htail].
  - inversion Hhead; subst. exists q; split=> //.
    left. reflexivity.
  - move: (IH Htail)=> [r [Hin ->]].
    exists r; split=> //. right. exact Hin.
Qed.

Lemma bind_entry_preimage {A B} (mu : Enum A) (k : A -> Enum B)
    (w : nnQ) (b : B) :
  List.In (w, b) (bind_Enum mu k) ->
  exists p a q,
    List.In (p, a) mu /\ List.In (q, b) (k a) /\ w = p * q.
Proof.
  elim: mu=> [//|[p a] mu IH] /=.
  rewrite List.in_app_iff. move=> [Hhead|Htail].
  - move: (scale_entry_preimage Hhead)=> [q [Hq ->]].
    exists p, a, q. repeat split=> //.
    left. reflexivity.
  - move: (IH Htail)=> [q [x [r [Hq [Hr ->]]]]].
    exists q, x, r. repeat split=> //. right. exact Hq.
Qed.

Lemma nnq_mul_nonzero_left p q :
  p * q != RatSubTypes.nnQ_0 -> p != RatSubTypes.nnQ_0.
Proof.
  apply: contra=> /eqP Hp. subst p.
  have Hz : RatSubTypes.nnQ_0 * q = RatSubTypes.nnQ_0.
    apply val_inj. cbn. exact: mul0r (Qval q).
  by rewrite Hz eq_refl.
Qed.

Lemma nnq_mul_nonzero_right p q :
  p * q != RatSubTypes.nnQ_0 -> q != RatSubTypes.nnQ_0.
Proof.
  apply: contra=> /eqP Hq. subst q.
  have Hz : p * RatSubTypes.nnQ_0 = RatSubTypes.nnQ_0.
    apply val_inj. cbn. exact: mulr0 (Qval p).
  by rewrite Hz eq_refl.
Qed.

#[global] Instance Enum_MeasureAEKleisliLaws :
    @MeasureAEKleisliLaws Enum Enum_MeasureInterface.
Proof.
  constructor. move=> A B mu k P Q Hmu Hk w b Hin Hw.
  move: (bind_entry_preimage Hin)=> [p [a [q [Hp [Hq HwEq]]]]].
  subst w.
  have HwB : p * q != RatSubTypes.nnQ_0.
  { apply/negP=> /eqP Heq. exact: Hw Heq. }
  have HpB := nnq_mul_nonzero_left HwB.
  have HqB := nnq_mul_nonzero_right HwB.
  have Hp0 : p <> RatSubTypes.nnQ_0.
  { move=> Heq. subst p. by rewrite eq_refl in HpB. }
  have Hq0 : q <> RatSubTypes.nnQ_0.
  { move=> Heq. subst q. by rewrite eq_refl in HqB. }
  exact: Hk a (Hmu p a Hp Hp0) q b Hq Hq0.
Qed.

#[global] Instance Enum_MeasureBindLaws :
    @MeasureBindLaws Enum Enum_MeasureInterface.
Proof.
  constructor. move=> A B mu k1 k2 Hae.
  exact: enum_prune_bind_ae Hae.
Qed.

#[global] Instance Enum_MeasureCongruenceLaws :
    @MeasureCongruenceLaws Enum Enum_MeasureInterface.
Proof.
  constructor.
  - move=> A x y ->. apply indexed_coupling_refl. reflexivity.
  - move=> A B mu nu k h Hmn Hkh. cbn in Hmn, Hkh |- *.
    rewrite !enum_prune_bind.
    eapply indexed_coupling_bind.
    + exact Hmn.
    + move=> x y ->. exact: Hkh.
  - move=> A mu nu P Hmn. cbn in Hmn |- *.
    split.
    + move=> Hmu p y Hy Hp.
      have Hy' : List.In (p, y) (enum_prune nu).
      { clear -Hy Hp. induction nu as [|[q z] nu IH]=> //=.
        destruct Hy as [H|H].
        - inversion H; subst q z. rewrite (negPf Hp). left; reflexivity.
        - case Hq: (q == RatSubTypes.nnQ_0).
          + exact: IH H.
          + right. exact: IH H. }
      move: (In_nth_error _ _ Hy')=> [j Hj].
      have Hjmass : acc_mass j (indexed (enum_prune nu)) != 0.
      { apply entry_nonzero_acc_mass with p.
        - rewrite /indexed. clear -Hj.
          move: Hj. generalize 0%N. induction (enum_prune nu)
            as [|[q z] tl IH]=> n [|j] //= Hnth.
          - inversion Hnth; subst. left. reflexivity.
          - right. exact: IH n.+1 j Hnth.
        - exact Hp. }
      destruct Hmn as [joint HL HR Hrel].
      rewrite -HR in Hjmass.
      move: (emap_nonzero_preimage snd joint j Hjmass)
        => [i [Hijmass Hij]]. subst j.
      have Hirel := Hrel i (snd (i, i)) Hijmass.
      move: (joint_nonzero_marginals Hijmass)=> [Himass _].
      rewrite HL in Himass.
      move: (indexed_nonzero_nth Himass)=> [q [x Hi]].
      have [Hleft _] := Hirel.
      move: (Hleft q x Hi)=> [r [z [Hj' Hxz]]].
      rewrite Hj in Hj'. inversion Hj'; subst r z. subst y.
      apply Hmu with q.
      * apply nth_error_In in Hi.
        clear -Hi. induction mu as [|[r z] mu IH]=> //=.
        case Hr: (r == RatSubTypes.nnQ_0).
        -- right. exact: IH Hi.
        -- destruct Hi as [Hi|Hi].
           ++ left. exact Hi.
           ++ right. exact: IH Hi.
      * move=> Hq. subst q. rewrite eq_refl in Himass. discriminate.
    + move=> Hnu. apply (proj1
        (@Enum_MeasureCongruenceLaws _ _ _ mu nu P
          (indexed_coupling_sym Hmn))). exact Hnu.
Qed.

#[global] Instance Enum_MeasureCommutativeLaws :
    @MeasureCommutativeLaws Enum Enum_MeasureInterface.
Proof.
  constructor.
  move=> A B C D R mu nu f g Hfg.
  set xy : Enum (A * B) :=
    bind_Enum mu (fun x =>
      bind_Enum nu (fun y => ret_Enum (x, y))).
  set yx : Enum (A * B) :=
    bind_Enum nu (fun y =>
      bind_Enum mu (fun x => ret_Enum (x, y))).
  have Hxy : xy ==Enum yx.
  { exact: enum_Fubini_Tonelli. }
  have Hprune : enum_prune xy ==Enum enum_prune yx.
  { eapply enum_eq_trans.
    - exact: enum_prune_eqenum.
    - eapply enum_eq_trans; [exact Hxy|].
      apply enum_eq_sym. exact: enum_prune_eqenum. }
  have Hidx : indexed_coupling eq (enum_prune xy) (enum_prune yx).
  { apply indexed_coupling_of_coupling.
    exact: coupling_of_enum_eq Hprune. }
  have Hmap := indexed_coupling_emap
    (R := R)
    (f := fun xy : A * B => f (fst xy) (snd xy))
    (g := fun xy : A * B => g (snd xy) (fst xy))
    (fun x y (H : x = y) =>
      match H with Logic.eq_refl => Hfg (fst x) (snd x) end)
    Hidx.
  cbn [Enum_MeasureInterface].
  have Hleft :
      bind_Enum mu (fun x =>
      bind_Enum nu (fun y => ret_Enum (f x y))) =
      emap (fun xy : A * B => f (fst xy) (snd xy)) xy.
  { rewrite /xy emap_bind. apply bind_Enum_ext=> x.
    rewrite emap_bind. apply bind_Enum_ext=> y. reflexivity. }
  have Hright :
      bind_Enum nu (fun y =>
      bind_Enum mu (fun x => ret_Enum (g y x))) =
      emap (fun xy : A * B => g (snd xy) (fst xy)) yx.
  { rewrite /yx emap_bind. apply bind_Enum_ext=> y.
    rewrite emap_bind. apply bind_Enum_ext=> x. reflexivity. }
  change (indexed_coupling R
    (enum_prune (bind_Enum mu (fun x =>
      bind_Enum nu (fun y => ret_Enum (f x y)))))
    (enum_prune (bind_Enum nu (fun y =>
      bind_Enum mu (fun x => ret_Enum (g y x)))))).
  rewrite Hleft Hright !enum_prune_emap.
  exact Hmap.
Qed.

#[global] Instance Enum_MeasureKleisliCommutativeLaws :
    @MeasureKleisliCommutativeLaws Enum Enum_MeasureInterface.
Proof.
  constructor.
  move=> A B C D R mu nu k1 k2 Hk.
  cbn [Enum_MeasureInterface].
  rewrite !enum_prune_bind.
  apply indexed_coupling_bind
    with (S := fun x y => indexed_coupling R
      (enum_prune (k1 x y)) (enum_prune (k2 y x))).
  - set xy : Enum (A * B) :=
      bind_Enum (enum_prune mu) (fun x =>
        bind_Enum (enum_prune nu) (fun y => ret_Enum (x, y))).
    set yx : Enum (A * B) :=
      bind_Enum (enum_prune nu) (fun y =>
        bind_Enum (enum_prune mu) (fun x => ret_Enum (x, y))).
    have Hxy : xy ==Enum yx by exact: enum_Fubini_Tonelli.
    have Hidx := indexed_coupling_of_coupling
      (R := eq) (coupling_of_enum_eq Hxy).
    have Hmap := indexed_coupling_emap
      (R := fun x y => indexed_coupling R
        (enum_prune (k1 (fst x) (snd x)))
        (enum_prune (k2 (fst y) (snd y))))
      (f := fun xy : A * B => xy)
      (g := fun yx : A * B => (snd yx, fst yx))
      (fun x y H => match H with Logic.eq_refl => Hk (fst x) (snd x) end)
      Hidx.
    cbn in Hmap.
    exact Hmap.
  - move=> [x y] [x' y'] Hxy.
    exact Hxy.
Qed.
