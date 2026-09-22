(** Position-indexed native semantics for finite ordinary rational weights.
    Equality and lifting still prune only zero weights before indexing. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat ssralg ssrnum order rat.
From PTree.Prob.Backend.EnumQ Require Import Representation Coupling IndexedCoupling Bind Map.
From PTree.Prob.Interface Require Import FrontierLift.
From PTree.Prob.Backend.Common Require Import FiniteEnum FinitePruning FiniteListAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Definition enumQ_prune {A} (mu : EnumQ A) : EnumQ A :=
  finite_enum_prune (fun p => p == 0) mu.
Lemma enumQ_prune_app {A} (mu nu : EnumQ A) :
  enumQ_raw (enumQ_prune (enumQ_app mu nu)) =
  enumQ_raw (enumQ_app (enumQ_prune mu) (enumQ_prune nu)).
Proof. exact: finite_prune_app. Qed.
Lemma enumQ_prune_emap {A B} (f : A -> B) (mu : EnumQ A) :
  enumQ_raw (enumQ_prune (emap f mu)) = enumQ_raw (emap f (enumQ_prune mu)).
Proof. exact: finite_prune_map. Qed.
Lemma enumQ_prune_eqenum {A : eqType} (mu : EnumQ A) :
  enumQ_prune mu ==EnumQ mu.
Proof. move=> x; exact: finite_expect_prune_zero. Qed.
Lemma enumQ_prune_scale_zero {A} (mu : EnumQ A) :
  enumQ_raw (enumQ_prune (scale_EnumQ (lexx 0) mu)) = nil.
Proof. rewrite /enumQ_prune /scale_EnumQ /enumQ_raw /= finite_prune_zero_scale eqxx; reflexivity. Qed.
Lemma enumQ_prune_scale {A} p (Hp : 0 <= p) (mu : EnumQ A) :
  enumQ_raw (enumQ_prune (scale_EnumQ Hp mu)) =
  if p == 0 then nil else enumQ_raw (scale_EnumQ Hp (enumQ_prune mu)).
Proof. exact: finite_prune_zero_scale. Qed.
Definition enumQ_ae {A} (mu : EnumQ A) (P : A -> Prop) : Prop :=
  forall p x, List.In (p,x) (enumQ_raw mu) -> p <> 0 -> P x.
Definition enumQ_meas_eq {A} (mu nu : EnumQ A) : Prop :=
  indexed_coupling eq (enumQ_prune mu) (enumQ_prune nu).
Definition enumQ_repr_eq {A} (mu nu : EnumQ A) : Prop := enumQ_raw mu = enumQ_raw nu.

Lemma enumQ_meas_eq_of_eqenum {A : eqType} (mu nu : EnumQ A) :
  mu ==EnumQ nu -> enumQ_meas_eq mu nu.
Proof.
  move=> H; apply indexed_coupling_of_coupling; apply coupling_of_enumQ_eq.
  eapply enumQ_eq_trans; first exact: enumQ_prune_eqenum.
  eapply enumQ_eq_trans; first exact H.
  apply enumQ_eq_sym; exact: enumQ_prune_eqenum.
Qed.
Lemma enumQ_prune_raw {A} (mu nu : EnumQ A) :
  enumQ_raw mu = enumQ_raw nu -> enumQ_raw (enumQ_prune mu) = enumQ_raw (enumQ_prune nu).
Proof.
  move=> H; change (finite_prune (fun p => p == 0) (enumQ_raw mu) =
    finite_prune (fun p => p == 0) (enumQ_raw nu)); by rewrite H.
Qed.
Lemma enumQ_repr_eq_implies_meas_eq {A} (mu nu : EnumQ A) :
  enumQ_repr_eq mu nu -> enumQ_meas_eq mu nu.
Proof.
  move=> H; apply (indexed_coupling_raw (mu := enumQ_prune mu) (nu := enumQ_prune mu)).
  - reflexivity.
  - exact: enumQ_prune_raw H.
  - apply indexed_coupling_refl=> x; reflexivity.
Qed.

#[global] Instance EnumQ_MeasureInterface : MeasureInterface EnumQ := {
  meas_ret := @ret_EnumQ; meas_bind := @bind_EnumQ;
  meas_eq := @enumQ_meas_eq; meas_ae := @enumQ_ae;
  meas_lift := fun A B R mu nu => indexed_coupling R (enumQ_prune mu) (enumQ_prune nu)
}.
Lemma enumQ_meas_lift_observe {A B} (R : A -> B -> Prop)
    (obsA : A -> bool) (obsB : B -> bool) (mu : EnumQ A) (nu : EnumQ B) :
  (forall x y, R x y -> obsA x = obsB y) ->
  @meas_lift EnumQ EnumQ_MeasureInterface A B R mu nu ->
  @meas_eq EnumQ EnumQ_MeasureInterface bool (emap obsA mu) (emap obsB nu).
Proof.
  move=> H Hlift; apply (indexed_coupling_raw
    (mu := emap obsA (enumQ_prune mu)) (nu := emap obsB (enumQ_prune nu))).
  - symmetry; exact: enumQ_prune_emap.
  - symmetry; exact: enumQ_prune_emap.
  - exact: indexed_coupling_emap H Hlift.
Qed.
#[global] Instance EnumQ_MeasureZeroInterface : MeasureZeroInterface EnumQ := {
  meas_empty := fun A => enumQ_zero
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
  - move=> A B R x y Hxy.
    apply (coupling_raw (mu := ret_EnumQ 0%N) (nu := ret_EnumQ 0%N)); try reflexivity.
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
  enumQ_ae mu (fun x => enumQ_raw (enumQ_prune (k1 x)) = enumQ_raw (enumQ_prune (k2 x))) ->
  enumQ_raw (enumQ_prune (bind_EnumQ mu k1)) = enumQ_raw (enumQ_prune (bind_EnumQ mu k2)).
Proof. exact: finite_prune_zero_bind_ae. Qed.
Lemma enumQ_prune_bind {A B} (mu : EnumQ A) (k : A -> EnumQ B) :
  enumQ_raw (enumQ_prune (bind_EnumQ mu k)) =
  enumQ_raw (bind_EnumQ (enumQ_prune mu) (fun x => enumQ_prune (k x))).
Proof. exact: finite_prune_zero_bind. Qed.
Lemma enumQ_prune_bind_coupling {A B C D} (R : C -> D -> Prop)
    (mu : EnumQ A) (nu : EnumQ B) (k : A -> EnumQ C) (h : B -> EnumQ D) :
  indexed_coupling R (bind_EnumQ (enumQ_prune mu) (fun x => enumQ_prune (k x)))
    (bind_EnumQ (enumQ_prune nu) (fun y => enumQ_prune (h y))) ->
  indexed_coupling R (enumQ_prune (bind_EnumQ mu k)) (enumQ_prune (bind_EnumQ nu h)).
Proof.
  apply indexed_coupling_raw; symmetry; exact: enumQ_prune_bind.
Qed.
Lemma enumQ_prune_in_source {A} (mu : EnumQ A) p x :
  List.In (p,x) (enumQ_raw (enumQ_prune mu)) -> List.In (p,x) (enumQ_raw mu) /\ p <> 0.
Proof.
  move/finite_prune_in=> [H Hp]; split; first exact H.
  move=> He; subst p; by rewrite eqxx in Hp.
Qed.
Lemma enumQ_prune_in {A} (mu : EnumQ A) p x :
  List.In (p,x) (enumQ_raw mu) -> p <> 0 -> List.In (p,x) (enumQ_raw (enumQ_prune mu)).
Proof.
  move=> Hin Hp; apply finite_prune_in; split; first exact Hin.
  apply/negP=> /eqP H; exact (Hp H).
Qed.
Lemma scale_entry_preimage {A} p (Hp : 0 <= p) w (x : A) (mu : EnumQ A) :
  List.In (w,x) (enumQ_raw (scale_EnumQ Hp mu)) ->
  exists q, List.In (q,x) (enumQ_raw mu) /\ w = p*q.
Proof.
  move/List.in_map_iff=> [[q y] [He Hin]]; inversion He; subst w y; by exists q.
Qed.
Lemma bind_entry_preimage {A B} (mu : EnumQ A) (k : A -> EnumQ B) w (b : B) :
  List.In (w,b) (enumQ_raw (bind_EnumQ mu k)) ->
  exists p a q, List.In (p,a) (enumQ_raw mu) /\
    List.In (q,b) (enumQ_raw (k a)) /\ w = p*q.
Proof.
  move/List.in_flat_map=> [[p a] [Hp Hin]].
  move/List.in_map_iff: Hin=> [[q y] [He Hq]]; inversion He; subst w y.
  exists p,a,q; by repeat split.
Qed.
Lemma rat_mul_nonzero_left (p q : rat) : p*q != 0 -> p != 0.
Proof. rewrite mulf_eq0 negb_or=> /andP [H _]; exact H. Qed.
Lemma rat_mul_nonzero_right (p q : rat) : p*q != 0 -> q != 0.
Proof. rewrite mulf_eq0 negb_or=> /andP [_ H]; exact H. Qed.

#[global] Instance EnumQ_MeasureAEKleisliLaws :
    @MeasureAEKleisliLaws EnumQ EnumQ_MeasureInterface.
Proof.
  constructor. move=> A B mu k P Q Hmu Hk w b Hin Hw.
  move: (bind_entry_preimage Hin)=> [p [a [q [Hp [Hq HwEq]]]]].
  subst w.
  have HwB : p * q != 0.
  { apply/negP=> /eqP Heq. exact: Hw Heq. }
  have HpB := rat_mul_nonzero_left HwB.
  have HqB := rat_mul_nonzero_right HwB.
  have Hp0 : p <> 0.
  { move=> Heq. subst p. by rewrite eq_refl in HpB. }
  have Hq0 : q <> 0.
  { move=> Heq. subst q. by rewrite eq_refl in HqB. }
  exact: Hk a (Hmu p a Hp Hp0) q b Hq Hq0.
Qed.

#[global] Instance EnumQ_MeasureBindLaws :
    @MeasureBindLaws EnumQ EnumQ_MeasureInterface.
Proof.
  constructor. move=> A B mu k1 k2 Hae.
  cbn in Hae |- *. unfold enumQ_meas_eq. apply enumQ_prune_bind_coupling.
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
  change (indexed_coupling S (enumQ_prune (bind_EnumQ mu k))
    (enumQ_prune (bind_EnumQ nu h))).
  apply enumQ_prune_bind_coupling.
  eapply indexed_coupling_bind; [exact Hmn|].
  move=> x y Hxy. exact (Hkh x y Hxy).
Qed.

#[global] Instance EnumQ_MeasureLiftAELaws :
    @MeasureLiftAELaws EnumQ EnumQ_MeasureInterface.
Proof.
  constructor.
  - move=> A B R mu nu P Hmn Hmu p y Hy Hp.
    have Hpb : p != 0.
    { apply/eqP=> Heq. exact: Hp Heq. }
    have Hy' : List.In (p, y) (enumQ_raw (enumQ_prune nu)).
    { exact: enumQ_prune_in Hy Hp. }
    move: (@In_nth_error _ (enumQ_raw (enumQ_prune nu)) (p, y) Hy')=> [j Hj].
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
    have Hinprune := @nth_error_In _ (enumQ_raw (enumQ_prune mu)) i (q, x) Hi.
    have [Hinsrc Hqnz] := enumQ_prune_in_source Hinprune.
    exact: Hmu q x Hinsrc Hqnz.
  - move=> A B C D R S mu nu k h P Q Hmn HP HQ Hkh.
    change (indexed_coupling S (enumQ_prune (bind_EnumQ mu k))
      (enumQ_prune (bind_EnumQ nu h))).
    apply enumQ_prune_bind_coupling.
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
    have Hpb : p != 0.
    { apply/eqP=> Heq. exact: Hp Heq. }
    have Hy' : List.In (p, y) (enumQ_raw (enumQ_prune nu)).
    { exact: enumQ_prune_in Hy Hp. }
    move: (@In_nth_error _ (enumQ_raw (enumQ_prune nu)) (p, y) Hy')=> [j Hj].
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
    have Hinprune := @nth_error_In _ (enumQ_raw (enumQ_prune mu)) i (q, x) Hi.
    have [Hinsrc Hqnz] := enumQ_prune_in_source Hinprune.
    exact: Hmu q x Hinsrc Hqnz. }
  constructor.
  - move=> A x y ->. apply indexed_coupling_refl. intros z. reflexivity.
  - move=> A B mu nu k h Hmn Hkh. cbn in Hmn, Hkh |- *.
    unfold enumQ_meas_eq in Hmn |- *. apply enumQ_prune_bind_coupling.
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
  - move=> A B x k.
    change (enumQ_meas_eq (bind_EnumQ (ret_EnumQ x) k) (k x)).
    apply enumQ_repr_eq_implies_meas_eq.
    change (finite_bind [:: (1,x)] (fun a => enumQ_raw (k a)) = enumQ_raw (k x)).
    rewrite -finite_bind_with_numeric.
    exact (@finite_bind_with_left_unit rat (fun p q => p*q) A B 1 x
      (fun a => enumQ_raw (k a)) (fun p => mul1r p)).
  - move=> A B C mu k h.
    apply enumQ_repr_eq_implies_meas_eq; exact: bind_EnumQ_assoc.
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
      enumQ_raw (bind_EnumQ mu (fun x =>
      bind_EnumQ nu (fun y => ret_EnumQ (f x y)))) =
      enumQ_raw (emap (fun xy : A * B => f (fst xy) (snd xy)) xy).
  { symmetry; rewrite /xy emap_bind; apply bind_EnumQ_ext=> x.
    rewrite emap_bind; apply bind_EnumQ_ext=> y; reflexivity. }
  have Hright :
      enumQ_raw (bind_EnumQ nu (fun y =>
      bind_EnumQ mu (fun x => ret_EnumQ (g y x)))) =
      enumQ_raw (emap (fun xy : A * B => g (snd xy) (fst xy)) yx).
  { symmetry; rewrite /yx emap_bind; apply bind_EnumQ_ext=> y.
    rewrite emap_bind; apply bind_EnumQ_ext=> x; reflexivity. }
  change (indexed_coupling R
    (enumQ_prune (bind_EnumQ mu (fun x =>
      bind_EnumQ nu (fun y => ret_EnumQ (f x y)))))
    (enumQ_prune (bind_EnumQ nu (fun y =>
      bind_EnumQ mu (fun x => ret_EnumQ (g y x)))))).
  eapply indexed_coupling_raw; last exact Hmap.
  - rewrite -enumQ_prune_emap; apply enumQ_prune_raw; symmetry; exact Hleft.
  - rewrite -enumQ_prune_emap; apply enumQ_prune_raw; symmetry; exact Hright.
Qed.

(** The representation-level Fubini theorem above proves the Dirac-terminal
    [MeasureCommutativeLaws] instance.  A full relational Fubini theorem for
    arbitrary continuation couplings additionally needs a product-joint
    flattening/gluing argument.  The previous attempted instance confused
    its coupling on paired samples with a coupling of [mu] and [nu], so it
    was unsound and is intentionally not registered.  Developments needing
    [MeasureKleisliCommutativeLaws] must currently assume that law explicitly. *)
