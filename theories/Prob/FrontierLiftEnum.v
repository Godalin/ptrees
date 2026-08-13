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
Proof.
  unfold enum_repr_eq. move=> H. subst nu.
  apply indexed_coupling_refl. intros x. reflexivity.
Qed.

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
  - move=> A mu. cbn. apply indexed_coupling_refl. intros x. reflexivity.
  - move=> A mu nu H. cbn in H |- *.
    eapply indexed_coupling_mono.
    + move=> x y Hyx. symmetry. exact Hyx.
    + exact: indexed_coupling_sym H.
  - move=> A mu nu xi H1 H2. cbn in H1, H2 |- *.
    have Hcomp := @indexed_coupling_comp A A A eq eq
      (enum_prune mu) (enum_prune nu) (enum_prune xi) H1 H2.
    eapply indexed_coupling_mono; [|exact Hcomp].
    move=> x z [y [Hxy Hyz]]. subst. reflexivity.
  - move=> A mu p x Hin Hnz. exact I.
  - move=> A mu P Q HP HQ p x Hin Hnz.
    split; [exact: HP p x Hin Hnz|exact: HQ p x Hin Hnz].
  - move=> A B R mu mu' nu Hmu Hlift.
    cbn in Hmu, Hlift |- *.
    have Hmu0 := indexed_coupling_sym Hmu.
    have Hmu' : indexed_coupling eq (enum_prune mu') (enum_prune mu).
    { eapply indexed_coupling_mono; [|exact Hmu0].
      move=> x y Hyx. symmetry. exact Hyx. }
    have Hcomp := @indexed_coupling_comp A A B eq R
      (enum_prune mu') (enum_prune mu) (enum_prune nu) Hmu' Hlift.
    eapply indexed_coupling_mono; [|exact Hcomp].
    move=> x y [z [Hxz Hzy]]. subst. exact Hzy.
  - move=> A B R mu nu nu' Hnu Hlift.
    cbn in Hnu, Hlift |- *.
    have Hcomp := @indexed_coupling_comp A B B R eq
      (enum_prune mu) (enum_prune nu) (enum_prune nu') Hlift Hnu.
    eapply indexed_coupling_mono; [|exact Hcomp].
    move=> x y [z [Hxz Hzy]]. subst. exact Hxz.
  - move=> A B R mu nu H. exact: (@indexed_coupling_sym
      A B R (enum_prune mu) (enum_prune nu) H).
  - move=> A B C R S mu nu xi H1 H2.
    exact: (@indexed_coupling_comp A B C R S
      (enum_prune mu) (enum_prune nu) (enum_prune xi) H1 H2).
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

Lemma enum_prune_in_source {A} (mu : Enum A) p x :
  List.In (p, x) (enum_prune mu) ->
  List.In (p, x) mu /\ p <> RatSubTypes.nnQ_0.
Proof.
  elim: mu=> [//|[q y] mu IH] //=.
  case Hq: (q == RatSubTypes.nnQ_0).
  - move=> Hin. have [Hs Hnz] := IH Hin. split=> //; right; exact Hs.
  - move=> [Heq|Hin].
    + inversion Heq; subst. split; first by left.
      move=> Hp. subst p. by rewrite eq_refl in Hq.
    + have [Hs Hnz] := IH Hin. split=> //; right; exact Hs.
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
  cbn in Hae |- *. unfold enum_meas_eq. rewrite !enum_prune_bind.
  eapply indexed_coupling_bind_ae
    with (P := fun x => enum_meas_eq (k1 x) (k2 x))
         (Q := fun x => enum_meas_eq (k1 x) (k2 x)).
  - apply indexed_coupling_refl. intros x. reflexivity.
  - move=> p x Hin. have [Hsrc Hnz] := enum_prune_in_source Hin.
    exact: Hae p x Hsrc Hnz.
  - move=> p x Hin. have [Hsrc Hnz] := enum_prune_in_source Hin.
    exact: Hae p x Hsrc Hnz.
  - move=> x y -> Hx _. exact Hx.
Qed.

#[global] Instance Enum_MeasureLiftBindLaws :
    @MeasureLiftBindLaws Enum Enum_MeasureInterface.
Proof.
  constructor. move=> A B C D R S mu nu k h Hmn Hkh.
  cbn in Hmn, Hkh |- *. rewrite !enum_prune_bind.
  eapply indexed_coupling_bind; [exact Hmn|].
  move=> x y Hxy. exact (Hkh x y Hxy).
Qed.

#[global] Instance Enum_MeasureLiftAELaws :
    @MeasureLiftAELaws Enum Enum_MeasureInterface.
Proof.
  constructor.
  - move=> A B R mu nu P Hmn Hmu p y Hy Hp.
    have Hpb : p != RatSubTypes.nnQ_0.
    { apply/eqP=> Heq. exact: Hp Heq. }
    have Hy' : List.In (p, y) (enum_prune nu).
    { clear -Hy Hpb. induction nu as [|[q z] nu IH]=> //=.
      destruct Hy as [H|H].
      - inversion H; subst q z. rewrite (negPf Hpb). left; reflexivity.
      - case Hq: (q == RatSubTypes.nnQ_0); [exact: IH H|].
        right. exact: IH H. }
    move: (@In_nth_error _ (enum_prune nu) (p, y) Hy')=> [j Hj].
    have Hjmass := @indexed_nth_nonzero B
      (enum_prune nu) j p y Hj Hpb.
    destruct Hmn as [joint HL HR Hrel]. rewrite -HR in Hjmass.
    move: (@emap_nonzero_preimage _ _ snd joint j Hjmass)
      => [[i j'] [Hijmass Hij]]. cbn in Hij. subst j'.
    have Hirel := Hrel i j Hijmass.
    have [Himass _] := joint_nonzero_marginals Hijmass.
    rewrite HL in Himass.
    move: (indexed_nonzero_nth Himass)=> [q [x Hi]].
    have [Hleft _] := Hirel.
    move: (Hleft q x Hi)=> [r [z [Hj' Hxz]]].
    rewrite Hj in Hj'. inversion Hj'; subst r z.
    exists x. split=> //.
    have Hinprune := @nth_error_In _ (enum_prune mu) i (q, x) Hi.
    have [Hinsrc Hqnz] := enum_prune_in_source Hinprune.
    exact: Hmu q x Hinsrc Hqnz.
  - move=> A B C D R S mu nu k h P Q Hmn HP HQ Hkh.
    cbn in Hmn, HP, HQ, Hkh |- *. rewrite !enum_prune_bind.
    eapply indexed_coupling_bind_ae
      with (P := P) (Q := Q); [exact Hmn|..].
    + move=> p x Hin. have [Hsrc Hnz] := enum_prune_in_source Hin.
      exact: HP p x Hsrc Hnz.
    + move=> q y Hin. have [Hsrc Hnz] := enum_prune_in_source Hin.
      exact: HQ q y Hsrc Hnz.
    + move=> x y Hxy Hpx Hqy. exact: Hkh Hxy Hpx Hqy.
Qed.

#[global] Instance Enum_MeasureCongruenceLaws :
    @MeasureCongruenceLaws Enum Enum_MeasureInterface.
Proof.
  have ae_transport : forall A (mu nu : Enum A) (P : A -> Prop),
      enum_meas_eq mu nu -> enum_ae mu P -> enum_ae nu P.
  { move=> A mu nu P Hmn Hmu p y Hy Hp.
    have Hpb : p != RatSubTypes.nnQ_0.
    { apply/eqP=> Heq. exact: Hp Heq. }
    have Hy' : List.In (p, y) (enum_prune nu).
    { clear -Hy Hpb. induction nu as [|[q z] nu IH]=> //=.
      destruct Hy as [H|H].
      - inversion H; subst q z. rewrite (negPf Hpb). left; reflexivity.
      - case Hq: (q == RatSubTypes.nnQ_0); [exact: IH H|].
        right. exact: IH H. }
    move: (@In_nth_error _ (enum_prune nu) (p, y) Hy')=> [j Hj].
    have Hjmass := @indexed_nth_nonzero A
      (enum_prune nu) j p y Hj Hpb.
    destruct Hmn as [joint HL HR Hrel]. rewrite -HR in Hjmass.
    move: (@emap_nonzero_preimage _ _ snd joint j Hjmass)
      => [[i j'] [Hijmass Hij]]. cbn in Hij. subst j'.
    have Hirel := Hrel i j Hijmass.
    have [Himass _] := joint_nonzero_marginals Hijmass.
    rewrite HL in Himass.
    move: (indexed_nonzero_nth Himass)=> [q [x Hi]].
    have [Hleft _] := Hirel.
    move: (Hleft q x Hi)=> [r [z [Hj' Hxz]]].
    rewrite Hj in Hj'. inversion Hj'; subst r z. subst y.
    have Hinprune := @nth_error_In _ (enum_prune mu) i (q, x) Hi.
    have [Hinsrc Hqnz] := enum_prune_in_source Hinprune.
    exact: Hmu q x Hinsrc Hqnz. }
  constructor.
  - move=> A x y ->. apply indexed_coupling_refl. intros z. reflexivity.
  - move=> A B mu nu k h Hmn Hkh. cbn in Hmn, Hkh |- *.
    unfold enum_meas_eq in Hmn |- *. rewrite !enum_prune_bind.
    eapply indexed_coupling_bind.
    + exact Hmn.
    + move=> x y ->. exact: Hkh.
  - move=> A mu nu P Hmn. cbn in Hmn |- *.
    split.
    + exact: ae_transport Hmn.
    + move=> Hnu. apply (@ae_transport A nu mu P)=> //.
      eapply indexed_coupling_mono; [|exact: indexed_coupling_sym Hmn].
      move=> x y Hyx. symmetry. exact Hyx.
Qed.

#[global] Instance Enum_MeasureMonadLaws :
    @MeasureMonadLaws Enum Enum_MeasureInterface.
Proof.
  constructor.
  - move=> A x P Hx p y Hin Hnz. cbn in Hin.
    destruct Hin as [Hin|Hin]; last contradiction.
    inversion Hin; subst. exact Hx.
  - move=> A B x k. cbn [Enum_MeasureInterface].
    unfold enum_meas_eq. cbn.
    have Hone : scale_Enum (fst (1, x)) (k x) = k x.
    { induction (k x) as [|[p y] tl IH]=> //=.
      rewrite IH. congr ((_ , _) :: _). apply val_inj.
      exact: mul1r (Qval p). }
    rewrite Hone cats0. apply indexed_coupling_refl.
    intros z. reflexivity.
  - move=> A B C mu k h. cbn [Enum_MeasureInterface].
    unfold enum_meas_eq.
    change (indexed_coupling eq
      (enum_prune (bind_Enum (bind_Enum mu k) h))
      (enum_prune (bind_Enum mu (fun x => bind_Enum (k x) h)))).
    rewrite bind_Enum_assoc.
    apply indexed_coupling_refl. intros z. reflexivity.
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

(** The representation-level Fubini theorem above proves the Dirac-terminal
    [MeasureCommutativeLaws] instance.  A full relational Fubini theorem for
    arbitrary continuation couplings additionally needs a product-joint
    flattening/gluing argument.  The previous attempted instance confused
    its coupling on paired samples with a coupling of [mu] and [nu], so it
    was unsound and is intentionally not registered.  Developments needing
    [MeasureKleisliCommutativeLaws] must currently assume that law explicitly. *)
