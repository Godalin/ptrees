(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import List.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg order rat.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Coupling PTree.Prob.Backend.EnumQ.IndexedCoupling PTree.Prob.Backend.EnumQ.Bind PTree.Prob.Backend.EnumQ.Map.
From PTree.Prob.Interface Require Import FrontierLift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ PTree.Prob.Backend.EnumQ.Coupling IndexedCoupling.
Import GRing.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Lemma nnq_mul_ne_zero (p q : nnQ) :
  p != PTree.Prob.Backend.Common.RatSubTypes.nnQ_0 -> q != PTree.Prob.Backend.Common.RatSubTypes.nnQ_0 ->
  p * q != PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
Proof.
  rewrite !PTree.Prob.Backend.Common.RatSubTypes.lt_0_nnQ_iff_ne_0.
  move=> Hp Hq. apply PTree.Prob.Backend.Common.RatSubTypes.lt_nnQ_of_lt_Q.
  exact: ssrnum.Num.Theory.mulr_gt0 Hp Hq.
Qed.

Fixpoint enumQ_prune {A} (mu : EnumQ A) : EnumQ A :=
  match mu with
  | [::] => [::]
  | (p, x) :: tl =>
      if p == PTree.Prob.Backend.Common.RatSubTypes.nnQ_0
      then enumQ_prune tl
      else (p, x) :: enumQ_prune tl
  end.

Lemma enumQ_prune_app {A} (mu nu : EnumQ A) :
  enumQ_prune (mu ++ nu) = enumQ_prune mu ++ enumQ_prune nu.
Proof.
  elim: mu=> [//=|[p x] mu IH] //=.
  by case: (p == PTree.Prob.Backend.Common.RatSubTypes.nnQ_0); rewrite IH.
Qed.

Lemma enumQ_prune_emap {A B} (f : A -> B) (mu : EnumQ A) :
  enumQ_prune (emap f mu) = emap f (enumQ_prune mu).
Proof.
  elim: mu=> [|[p a] mu IH] //=.
  by case: (p == PTree.Prob.Backend.Common.RatSubTypes.nnQ_0); rewrite /= IH.
Qed.

Lemma enumQ_prune_eqenum {A : eqType} (mu : EnumQ A) :
  enumQ_prune mu ==EnumQ mu.
Proof.
  move=> a. elim: mu=> [|[p x] mu IH] //=.
  case Hp: (p == PTree.Prob.Backend.Common.RatSubTypes.nnQ_0).
  - have Hp0 : p = 0.
    { rewrite (eqP Hp). apply val_inj. reflexivity. }
    rewrite (@acc_mass_cons_zero A mu a (p, x) Hp0). exact IH.
  - rewrite !acc_mass_cons IH. reflexivity.
Qed.

Lemma enumQ_prune_scale_zero {A} (mu : EnumQ A) :
  enumQ_prune (scale_EnumQ PTree.Prob.Backend.Common.RatSubTypes.nnQ_0 mu) = [::].
Proof.
  elim: mu=> [//=|[p x] mu IH] //=.
  have Hz : PTree.Prob.Backend.Common.RatSubTypes.nnQ_0 * p = PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
    apply val_inj. cbn. exact: mul0r (Qval p).
  by rewrite Hz eq_refl IH.
Qed.

Lemma enumQ_prune_scale {A} (p : nnQ) (mu : EnumQ A) :
  enumQ_prune (scale_EnumQ p mu) =
  if p == PTree.Prob.Backend.Common.RatSubTypes.nnQ_0 then [::]
  else scale_EnumQ p (enumQ_prune mu).
Proof.
  case Hp: (p == PTree.Prob.Backend.Common.RatSubTypes.nnQ_0).
  - move/eqP: Hp=> ->. exact: enumQ_prune_scale_zero mu.
  - elim: mu=> [//=|[q x] mu IH] //=.
    case Hq: (q == PTree.Prob.Backend.Common.RatSubTypes.nnQ_0).
    + move/eqP: Hq=> Hq0.
      have Hpq0 : p * q = PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
      { rewrite Hq0. apply val_inj. cbn. exact: mulr0 (Qval p). }
      rewrite Hpq0 eq_refl. exact IH.
    + have Hpn : p != PTree.Prob.Backend.Common.RatSubTypes.nnQ_0 by rewrite Hp.
      have Hqn : q != PTree.Prob.Backend.Common.RatSubTypes.nnQ_0 by rewrite Hq.
      have Hpq := nnq_mul_ne_zero Hpn Hqn.
      rewrite (negPf Hpq) IH. reflexivity.
Qed.

(** Almost-everywhere for a finite enumeration: a property is required only
    at entries carrying non-zero mass.  This definition needs no equality on
    the sampled type. *)
Definition enumQ_ae {A} (mu : EnumQ A) (P : A -> Prop) : Prop :=
  forall p x, List.In (p, x) mu -> p <> PTree.Prob.Backend.Common.RatSubTypes.nnQ_0 -> P x.

(** The operational instance is fully generic in its carriers.  Its
    [meas_lift] is the existing position-indexed coupling, which avoids an
    [eqType] requirement on values such as event continuations. *)
Definition enumQ_meas_eq {A} (mu nu : EnumQ A) : Prop :=
  indexed_coupling eq (enumQ_prune mu) (enumQ_prune nu).

(** Literal list equality is only representation equality.  The semantic
    equality below is insensitive to zero entries, ordering, duplicates and
    splitting a weight into several entries. *)
Definition enumQ_repr_eq {A} (mu nu : EnumQ A) : Prop := mu = nu.

Lemma enumQ_meas_eq_of_eqenum {A : eqType} (mu nu : EnumQ A) :
  mu ==EnumQ nu -> enumQ_meas_eq mu nu.
Proof.
  move=> Hmn. apply indexed_coupling_of_coupling.
  apply coupling_of_enumQ_eq.
  eapply enumQ_eq_trans; first exact: enumQ_prune_eqenum.
  eapply enumQ_eq_trans; first exact Hmn.
  apply enumQ_eq_sym. exact: enumQ_prune_eqenum.
Qed.

Lemma enumQ_repr_eq_implies_meas_eq {A} (mu nu : EnumQ A) :
  enumQ_repr_eq mu nu -> enumQ_meas_eq mu nu.
Proof.
  unfold enumQ_repr_eq. move=> H. subst nu.
  apply indexed_coupling_refl. intros x. reflexivity.
Qed.

#[global] Instance EnumQ_MeasureInterface : MeasureInterface EnumQ := {
  meas_ret := @ret_EnumQ;
  meas_bind := @bind_EnumQ;
  meas_eq := @enumQ_meas_eq;
  meas_ae := @enumQ_ae;
  meas_lift := fun A B R mu nu =>
    indexed_coupling R (enumQ_prune mu) (enumQ_prune nu)
}.

(** Every Boolean observation respected by a coupling has the same
    extensional distribution on both marginals.  Unlike [acc_mass], this
    statement does not require decidable equality on the original carriers;
    observable heads may therefore contain functions and dependent events. *)
Lemma enumQ_meas_lift_observe {A B} (R : A -> B -> Prop)
    (obsA : A -> bool) (obsB : B -> bool) (mu : EnumQ A) (nu : EnumQ B) :
  (forall x y, R x y -> obsA x = obsB y) ->
  @meas_lift EnumQ EnumQ_MeasureInterface A B R mu nu ->
  @meas_eq EnumQ EnumQ_MeasureInterface bool
    (emap obsA mu) (emap obsB nu).
Proof.
  move=> Hobs Hlift.
  cbn in Hlift |- *. unfold enumQ_meas_eq in Hlift |- *.
  rewrite !enumQ_prune_emap.
  exact: indexed_coupling_emap Hobs Hlift.
Qed.

#[global] Instance EnumQ_MeasureZeroInterface : MeasureZeroInterface EnumQ := {
  meas_empty := fun A => [::]
}.

#[global] Instance EnumQ_MeasureCoreLaws :
    @MeasureCoreLaws EnumQ EnumQ_MeasureInterface.
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

#[global] Instance EnumQ_MeasureLaws :
    @MeasureLaws EnumQ EnumQ_MeasureInterface EnumQ_MeasureCoreLaws.
Proof.
  constructor.
  - move=> A mu. cbn. apply indexed_coupling_refl. intros x. reflexivity.
  - move=> A mu nu H. cbn in H |- *.
    eapply indexed_coupling_mono.
    + move=> x y Hyx. symmetry. exact Hyx.
    + exact: indexed_coupling_sym H.
  - move=> A mu nu xi H1 H2. cbn in H1, H2 |- *.
    have Hcomp := @indexed_coupling_comp A A A eq eq
      (enumQ_prune mu) (enumQ_prune nu) (enumQ_prune xi) H1 H2.
    eapply indexed_coupling_mono; [|exact Hcomp].
    move=> x z [y [Hxy Hyz]]. subst. reflexivity.
  - move=> A mu p x Hin Hnz. exact I.
  - move=> A mu P Q HP HQ p x Hin Hnz.
    split; [exact: HP p x Hin Hnz|exact: HQ p x Hin Hnz].
  - move=> A B R mu mu' nu Hmu Hlift.
    cbn in Hmu, Hlift |- *.
    have Hmu0 := indexed_coupling_sym Hmu.
    have Hmu' : indexed_coupling eq (enumQ_prune mu') (enumQ_prune mu).
    { eapply indexed_coupling_mono; [|exact Hmu0].
      move=> x y Hyx. symmetry. exact Hyx. }
    have Hcomp := @indexed_coupling_comp A A B eq R
      (enumQ_prune mu') (enumQ_prune mu) (enumQ_prune nu) Hmu' Hlift.
    eapply indexed_coupling_mono; [|exact Hcomp].
    move=> x y [z [Hxz Hzy]]. subst. exact Hzy.
  - move=> A B R mu nu nu' Hnu Hlift.
    cbn in Hnu, Hlift |- *.
    have Hcomp := @indexed_coupling_comp A B B R eq
      (enumQ_prune mu) (enumQ_prune nu) (enumQ_prune nu') Hlift Hnu.
    eapply indexed_coupling_mono; [|exact Hcomp].
    move=> x y [z [Hxz Hzy]]. subst. exact Hxz.
  - move=> A B R mu nu H. exact: (@indexed_coupling_sym
      A B R (enumQ_prune mu) (enumQ_prune nu) H).
  - move=> A B C R S mu nu xi H1 H2.
    exact: (@indexed_coupling_comp A B C R S
      (enumQ_prune mu) (enumQ_prune nu) (enumQ_prune xi) H1 H2).
Qed.

Lemma enumQ_prune_bind_ae {A B} (mu : EnumQ A) (k1 k2 : A -> EnumQ B) :
  enumQ_ae mu (fun x => enumQ_prune (k1 x) = enumQ_prune (k2 x)) ->
  enumQ_prune (bind_EnumQ mu k1) = enumQ_prune (bind_EnumQ mu k2).
Proof.
  move=> Hae. elim: mu Hae=> [|[p x] mu IH] Hae //=.
  rewrite !enumQ_prune_app !enumQ_prune_scale.
  have Htail : enumQ_ae mu
      (fun y => enumQ_prune (k1 y) = enumQ_prune (k2 y)).
  { move=> q y Hin Hq. exact: Hae q y (or_intror Hin) Hq. }
  rewrite (IH Htail).
  case Hp: (p == PTree.Prob.Backend.Common.RatSubTypes.nnQ_0)=> //=.
  have Hpn : p <> PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
    move=> Heq. subst p. by rewrite eq_refl in Hp.
  have Hhead := Hae p x
    (or_introl (Logic.eq_refl (p, x))) Hpn.
  by rewrite Hhead.
Qed.

(** Pruning commutes exactly with finite Kleisli extension.  This exposes a
    bind as a concatenation of non-zero blocks, which is the normal form used
    by position-indexed couplings. *)
Lemma enumQ_prune_bind {A B} (mu : EnumQ A) (k : A -> EnumQ B) :
  enumQ_prune (bind_EnumQ mu k) =
  bind_EnumQ (enumQ_prune mu) (fun x => enumQ_prune (k x)).
Proof.
  elim: mu=> [|[p x] mu IH] //=.
  rewrite enumQ_prune_app enumQ_prune_scale IH.
  case Hp: (p == PTree.Prob.Backend.Common.RatSubTypes.nnQ_0)=> //=.
Qed.

Lemma enumQ_prune_in_source {A} (mu : EnumQ A) p x :
  List.In (p, x) (enumQ_prune mu) ->
  List.In (p, x) mu /\ p <> PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
Proof.
  elim: mu=> [//|[q y] mu IH] //=.
  case Hq: (q == PTree.Prob.Backend.Common.RatSubTypes.nnQ_0).
  - move=> Hin. have [Hs Hnz] := IH Hin. split=> //; right; exact Hs.
  - move=> [Heq|Hin].
    + inversion Heq; subst. split; first by left.
      move=> Hp. subst p. by rewrite eq_refl in Hq.
    + have [Hs Hnz] := IH Hin. split=> //; right; exact Hs.
Qed.

Lemma scale_entry_preimage {A} (p w : nnQ) (x : A) (mu : EnumQ A) :
  List.In (w, x) (scale_EnumQ p mu) ->
  exists q, List.In (q, x) mu /\ w = p * q.
Proof.
  elim: mu=> [//|[q y] mu IH] /=.
  move=> [Hhead|Htail].
  - inversion Hhead; subst. exists q; split=> //.
    left. reflexivity.
  - move: (IH Htail)=> [r [Hin ->]].
    exists r; split=> //. right. exact Hin.
Qed.

Lemma bind_entry_preimage {A B} (mu : EnumQ A) (k : A -> EnumQ B)
    (w : nnQ) (b : B) :
  List.In (w, b) (bind_EnumQ mu k) ->
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
  p * q != PTree.Prob.Backend.Common.RatSubTypes.nnQ_0 -> p != PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
Proof.
  apply: contra=> /eqP Hp. subst p.
  have Hz : PTree.Prob.Backend.Common.RatSubTypes.nnQ_0 * q = PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
    apply val_inj. cbn. exact: mul0r (Qval q).
  by rewrite Hz eq_refl.
Qed.

Lemma nnq_mul_nonzero_right p q :
  p * q != PTree.Prob.Backend.Common.RatSubTypes.nnQ_0 -> q != PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
Proof.
  apply: contra=> /eqP Hq. subst q.
  have Hz : p * PTree.Prob.Backend.Common.RatSubTypes.nnQ_0 = PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
    apply val_inj. cbn. exact: mulr0 (Qval p).
  by rewrite Hz eq_refl.
Qed.

#[global] Instance EnumQ_MeasureAEKleisliLaws :
    @MeasureAEKleisliLaws EnumQ EnumQ_MeasureInterface.
Proof.
  constructor. move=> A B mu k P Q Hmu Hk w b Hin Hw.
  move: (bind_entry_preimage Hin)=> [p [a [q [Hp [Hq HwEq]]]]].
  subst w.
  have HwB : p * q != PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
  { apply/negP=> /eqP Heq. exact: Hw Heq. }
  have HpB := nnq_mul_nonzero_left HwB.
  have HqB := nnq_mul_nonzero_right HwB.
  have Hp0 : p <> PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
  { move=> Heq. subst p. by rewrite eq_refl in HpB. }
  have Hq0 : q <> PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
  { move=> Heq. subst q. by rewrite eq_refl in HqB. }
  exact: Hk a (Hmu p a Hp Hp0) q b Hq Hq0.
Qed.

#[global] Instance EnumQ_MeasureBindLaws :
    @MeasureBindLaws EnumQ EnumQ_MeasureInterface.
Proof.
  constructor. move=> A B mu k1 k2 Hae.
  cbn in Hae |- *. unfold enumQ_meas_eq. rewrite !enumQ_prune_bind.
  eapply indexed_coupling_bind_ae
    with (P := fun x => enumQ_meas_eq (k1 x) (k2 x))
         (Q := fun x => enumQ_meas_eq (k1 x) (k2 x)).
  - apply indexed_coupling_refl. intros x. reflexivity.
  - move=> p x Hin. have [Hsrc Hnz] := enumQ_prune_in_source Hin.
    exact: Hae p x Hsrc Hnz.
  - move=> p x Hin. have [Hsrc Hnz] := enumQ_prune_in_source Hin.
    exact: Hae p x Hsrc Hnz.
  - move=> x y -> Hx _. exact Hx.
Qed.

#[global] Instance EnumQ_MeasureLiftBindLaws :
    @MeasureLiftBindLaws EnumQ EnumQ_MeasureInterface.
Proof.
  constructor. move=> A B C D R S mu nu k h Hmn Hkh.
  cbn in Hmn, Hkh |- *. rewrite !enumQ_prune_bind.
  eapply indexed_coupling_bind; [exact Hmn|].
  move=> x y Hxy. exact (Hkh x y Hxy).
Qed.

#[global] Instance EnumQ_MeasureLiftAELaws :
    @MeasureLiftAELaws EnumQ EnumQ_MeasureInterface.
Proof.
  constructor.
  - move=> A B R mu nu P Hmn Hmu p y Hy Hp.
    have Hpb : p != PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
    { apply/eqP=> Heq. exact: Hp Heq. }
    have Hy' : List.In (p, y) (enumQ_prune nu).
    { clear -Hy Hpb. induction nu as [|[q z] nu IH]=> //=.
      destruct Hy as [H|H].
      - inversion H; subst q z. rewrite (negPf Hpb). left; reflexivity.
      - case Hq: (q == PTree.Prob.Backend.Common.RatSubTypes.nnQ_0); [exact: IH H|].
        right. exact: IH H. }
    move: (@In_nth_error _ (enumQ_prune nu) (p, y) Hy')=> [j Hj].
    have Hjmass := @indexed_nth_nonzero B
      (enumQ_prune nu) j p y Hj Hpb.
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
    have Hinprune := @nth_error_In _ (enumQ_prune mu) i (q, x) Hi.
    have [Hinsrc Hqnz] := enumQ_prune_in_source Hinprune.
    exact: Hmu q x Hinsrc Hqnz.
  - move=> A B C D R S mu nu k h P Q Hmn HP HQ Hkh.
    cbn in Hmn, HP, HQ, Hkh |- *. rewrite !enumQ_prune_bind.
    eapply indexed_coupling_bind_ae
      with (P := P) (Q := Q); [exact Hmn|..].
    + move=> p x Hin. have [Hsrc Hnz] := enumQ_prune_in_source Hin.
      exact: HP p x Hsrc Hnz.
    + move=> q y Hin. have [Hsrc Hnz] := enumQ_prune_in_source Hin.
      exact: HQ q y Hsrc Hnz.
    + move=> x y Hxy Hpx Hqy. exact: Hkh Hxy Hpx Hqy.
Qed.

#[global] Instance EnumQ_MeasureCongruenceLaws :
    @MeasureCongruenceLaws EnumQ EnumQ_MeasureInterface.
Proof.
  have ae_transport : forall A (mu nu : EnumQ A) (P : A -> Prop),
      enumQ_meas_eq mu nu -> enumQ_ae mu P -> enumQ_ae nu P.
  { move=> A mu nu P Hmn Hmu p y Hy Hp.
    have Hpb : p != PTree.Prob.Backend.Common.RatSubTypes.nnQ_0.
    { apply/eqP=> Heq. exact: Hp Heq. }
    have Hy' : List.In (p, y) (enumQ_prune nu).
    { clear -Hy Hpb. induction nu as [|[q z] nu IH]=> //=.
      destruct Hy as [H|H].
      - inversion H; subst q z. rewrite (negPf Hpb). left; reflexivity.
      - case Hq: (q == PTree.Prob.Backend.Common.RatSubTypes.nnQ_0); [exact: IH H|].
        right. exact: IH H. }
    move: (@In_nth_error _ (enumQ_prune nu) (p, y) Hy')=> [j Hj].
    have Hjmass := @indexed_nth_nonzero A
      (enumQ_prune nu) j p y Hj Hpb.
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
    have Hinprune := @nth_error_In _ (enumQ_prune mu) i (q, x) Hi.
    have [Hinsrc Hqnz] := enumQ_prune_in_source Hinprune.
    exact: Hmu q x Hinsrc Hqnz. }
  constructor.
  - move=> A x y ->. apply indexed_coupling_refl. intros z. reflexivity.
  - move=> A B mu nu k h Hmn Hkh. cbn in Hmn, Hkh |- *.
    unfold enumQ_meas_eq in Hmn |- *. rewrite !enumQ_prune_bind.
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

#[global] Instance EnumQ_MeasureMonadLaws :
    @MeasureMonadLaws EnumQ EnumQ_MeasureInterface.
Proof.
  constructor.
  - move=> A x P Hx p y Hin Hnz. cbn in Hin.
    destruct Hin as [Hin|Hin]; last contradiction.
    inversion Hin; subst. exact Hx.
  - move=> A B x k. cbn [EnumQ_MeasureInterface].
    unfold enumQ_meas_eq. cbn.
    have Hone : scale_EnumQ (fst (1, x)) (k x) = k x.
    { induction (k x) as [|[p y] tl IH]=> //=.
      rewrite IH. congr ((_ , _) :: _). apply val_inj.
      exact: mul1r (Qval p). }
    rewrite Hone cats0. apply indexed_coupling_refl.
    intros z. reflexivity.
  - move=> A B C mu k h. cbn [EnumQ_MeasureInterface].
    unfold enumQ_meas_eq.
    change (indexed_coupling eq
      (enumQ_prune (bind_EnumQ (bind_EnumQ mu k) h))
      (enumQ_prune (bind_EnumQ mu (fun x => bind_EnumQ (k x) h)))).
    rewrite bind_EnumQ_assoc.
    apply indexed_coupling_refl. intros z. reflexivity.
Qed.

#[global] Instance EnumQ_MeasureCommutativeLaws :
    @MeasureCommutativeLaws EnumQ EnumQ_MeasureInterface.
Proof.
  constructor.
  move=> A B C D R mu nu f g Hfg.
  set xy : EnumQ (A * B) :=
    bind_EnumQ mu (fun x =>
      bind_EnumQ nu (fun y => ret_EnumQ (x, y))).
  set yx : EnumQ (A * B) :=
    bind_EnumQ nu (fun y =>
      bind_EnumQ mu (fun x => ret_EnumQ (x, y))).
  have Hxy : xy ==EnumQ yx.
  { exact: enumQ_Fubini_Tonelli. }
  have Hprune : enumQ_prune xy ==EnumQ enumQ_prune yx.
  { eapply enumQ_eq_trans.
    - exact: enumQ_prune_eqenum.
    - eapply enumQ_eq_trans; [exact Hxy|].
      apply enumQ_eq_sym. exact: enumQ_prune_eqenum. }
  have Hidx : indexed_coupling eq (enumQ_prune xy) (enumQ_prune yx).
  { apply indexed_coupling_of_coupling.
    exact: coupling_of_enumQ_eq Hprune. }
  have Hmap := indexed_coupling_emap
    (R := R)
    (f := fun xy : A * B => f (fst xy) (snd xy))
    (g := fun xy : A * B => g (snd xy) (fst xy))
    (fun x y (H : x = y) =>
      match H with Logic.eq_refl => Hfg (fst x) (snd x) end)
    Hidx.
  cbn [EnumQ_MeasureInterface].
  have Hleft :
      bind_EnumQ mu (fun x =>
      bind_EnumQ nu (fun y => ret_EnumQ (f x y))) =
      emap (fun xy : A * B => f (fst xy) (snd xy)) xy.
  { rewrite /xy emap_bind. apply bind_EnumQ_ext=> x.
    rewrite emap_bind. apply bind_EnumQ_ext=> y. reflexivity. }
  have Hright :
      bind_EnumQ nu (fun y =>
      bind_EnumQ mu (fun x => ret_EnumQ (g y x))) =
      emap (fun xy : A * B => g (snd xy) (fst xy)) yx.
  { rewrite /yx emap_bind. apply bind_EnumQ_ext=> y.
    rewrite emap_bind. apply bind_EnumQ_ext=> x. reflexivity. }
  change (indexed_coupling R
    (enumQ_prune (bind_EnumQ mu (fun x =>
      bind_EnumQ nu (fun y => ret_EnumQ (f x y)))))
    (enumQ_prune (bind_EnumQ nu (fun y =>
      bind_EnumQ mu (fun x => ret_EnumQ (g y x)))))).
  rewrite Hleft Hright !enumQ_prune_emap.
  exact Hmap.
Qed.

(** The representation-level Fubini theorem above proves the Dirac-terminal
    [MeasureCommutativeLaws] instance.  A full relational Fubini theorem for
    arbitrary continuation couplings additionally needs a product-joint
    flattening/gluing argument.  The previous attempted instance confused
    its coupling on paired samples with a coupling of [mu] and [nu], so it
    was unsound and is intentionally not registered.  Developments needing
    [MeasureKleisliCommutativeLaws] must currently assume that law explicitly. *)
