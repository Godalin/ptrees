(** Role: Canonical observable measure, mixed and omega instances and laws. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import FunctionalExtensionality.
From Coq.Program Require Import Equality.
Require Import Morphisms Arith.

From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient.


#[global] Polymorphic Instance FreeOmegaObservableSemanticMeasure
    {MN} `{NI : SemanticMeasure MN}
    `{NO : @SemanticOmega MN NI} :
    SemanticMeasure (FreeOmega MN) := {
  sem_ret := @FORet MN;
  sem_bind := @free_omega_bind MN;
  sem_eq := fun A => @free_omega_qlift MN NI NO A A eq;
  sem_ae := fun A mu P => @free_omega_ae MN NI A P mu;
  sem_lift := @free_omega_qlift MN NI NO
}.

Lemma free_omega_observable_sem_retE {MN}
    `{NI : SemanticMeasure MN}
    `{NO : @SemanticOmega MN NI} {A} (x : A) :
  @sem_ret (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    A x = FORet x.
Proof. reflexivity. Qed.

(** A proof of an existing capability, not a new axiom or global instance.
    This fact is structural in FreeOmega and needs no node separation law. *)
Lemma free_omega_observable_dirac_ae_laws {MN}
    `{NI : SemanticMeasure MN} `{NO : @SemanticOmega MN NI} :
  @SemanticMeasureDiracAELaws (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Proof.
  constructor. intros A x P. split; intro H.
  - change (free_omega_ae P (FORet x)) in H. dependent destruction H. assumption.
  - apply FOAERet. exact H.
Qed.

Section FreeOmegaObservableLaws.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}.

Lemma free_omega_qlift_refl {A} (R : A -> A -> Prop) mu :
  Reflexive R -> free_omega_qlift R mu mu.
Proof. intro HR. apply FOQLStructural, free_omega_lift_refl, HR. Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureCoreLaws :
    @SemanticMeasureCoreLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Proof.
  constructor.
  - intros A mu. apply free_omega_qlift_refl. intros x. reflexivity.
  - intros A mu nu H. apply FOQLSym.
    eapply FOQLMono; [exact H|]. intros x y ->. reflexivity.
  - intros A mu nu xi Hmn Hnx.
    refine (FOQLComp (R := eq) Hmn Hnx _).
    intros x z [y [-> ->]]. reflexivity.
  - intros A mu. induction mu.
    + constructor. exact I.
    + constructor.
    + eapply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros x _. exact (H x).
    + constructor. exact H.
  - intros A mu P Q HPQ Hae.
    exact (free_omega_ae_mono (P := P) (Q := Q) (mu := mu) HPQ Hae).
  - intros A mu P Q HP HQ.
    exact (free_omega_ae_conj (P := P) (Q := Q) (mu := mu) HP HQ).
  - intros A B R T mu nu HRT H.
    eapply FOQLMono; eauto.
  - intros A R mu HR. apply free_omega_qlift_refl. exact HR.
  - intros A B R x y Hxy. apply FOQLStructural. constructor. exact Hxy.
  - intros A B R mu mu' nu Hmm Hmn.
    assert (Hmm' : free_omega_qlift eq mu' mu).
    { apply FOQLSym. eapply FOQLMono; [exact Hmm|].
      intros x y ->. reflexivity. }
    refine (FOQLComp (R := R) Hmm' Hmn _).
    intros x z [y [-> Hyz]]. exact Hyz.
  - intros A B R mu nu nu' Hnn Hmn.
    refine (FOQLComp (R := R) Hmn Hnn _).
    intros x z [y [Hxy ->]]. exact Hxy.
  - intros A B R mu nu H. apply FOQLSym. exact H.
  - intros A B C R T mu nu xi Hmn Hnx.
    refine (FOQLComp (R := fun x z => exists y, R x y /\ T y z)
      Hmn Hnx _).
    intros x z Hxz. exact Hxz.
Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureAEKleisliLaws :
    @SemanticMeasureAEKleisliLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Proof.
  constructor.
  - intros A P x Hx. constructor. exact Hx.
  - intros A B mu k P Q Hmu Hk.
    cbn in Hmu, Hk |- *. exact (free_omega_ae_bind Hmu Hk).
Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureCountableAELaws
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI} :
    @SemanticMeasureCountableAELaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Proof.
  constructor. intros A mu P HP. apply free_omega_ae_countable. exact HP.
Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureCouplingAELaws
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI} :
    @SemanticMeasureCouplingAELaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Proof.
  constructor.
  - intros A B R mu nu P Hlift HP.
    exact (proj1 (free_omega_qlift_support Hlift) P HP).
  - intros A B R mu nu P Q Hlift HP HQ.
    eapply FOQLAERestrict with (T := R) (P := P) (Q := Q).
    + exact Hlift.
    + exact HP.
    + exact HQ.
    + intros x y Hxy. exact Hxy.
Qed.

Lemma free_omega_qlift_bind_ae
    `{NAE : @SemanticMeasureAELiftLaws MN NI}
    {A B} (mu : FreeOmega MN A) (k h : A -> FreeOmega MN B) :
  free_omega_ae (fun x => free_omega_qlift eq (k x) (h x)) mu ->
  free_omega_qlift eq (free_omega_bind mu k) (free_omega_bind mu h).
Proof.
  intro Hae. induction Hae; cbn.
  - exact H.
  - apply FOQLStructural. constructor.
  - eapply FOQLSample with (T := fun x y => x = y /\ Good x).
    + exact (sem_lift_refl_ae H).
    + intros x y [-> Hy]. exact (H1 y Hy).
  - apply FOQLLub. exact H0.
Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureBindLaws
    `{NAE : @SemanticMeasureAELiftLaws MN NI} :
    @SemanticMeasureBindLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Proof.
  constructor.
  - intros A B x k. apply free_omega_qlift_refl. intros y. reflexivity.
  - intros A B C mu k h.
    change (free_omega_qlift eq
      (free_omega_bind (free_omega_bind mu k) h)
      (free_omega_bind mu (fun x => free_omega_bind (k x) h))).
    rewrite free_omega_bind_assoc.
    apply free_omega_qlift_refl. intros y. reflexivity.
  - intros A B mu k h Hae. exact (free_omega_qlift_bind_ae Hae).
  - intros A B C D R T mu nu k h Hmn Hkh.
    eapply FOQLBind; eauto.
Qed.

#[global] Instance FreeOmegaObservableMixedMeasureLaws
    `{NAE : @SemanticMeasureAELiftLaws MN NI} :
    @MixedMeasureLaws MN (FreeOmega MN) NI
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure.
Proof.
  constructor.
  - intros A B mu k h Hae.
    eapply FOQLSample with (T := fun x y => x = y /\
      free_omega_qlift eq (k x) (h x)).
    + exact (sem_lift_refl_ae Hae).
    + intros x y [-> Hxy]. exact Hxy.
  - intros A B C mu k h.
    apply free_omega_qlift_refl. intros x. reflexivity.
  - intros A B C D R T mu nu k h Hmn Hkh.
    eapply FOQLSample; eauto.
Qed.

#[global] Instance FreeOmegaObservableMixedMeasureUnitLaws
    `{ND : @SemanticMeasureDiracAELaws MN NI} :
    @MixedMeasureUnitLaws MN (FreeOmega MN) NI
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure.
Proof.
  constructor. intros A B x k.
  change (free_omega_qlift eq (FOSample (sem_ret x) k) (k x)).
  apply FOQLSampleRetL.
  - apply sem_ae_ret_iff.
  - apply free_omega_qlift_refl.
  intro y. reflexivity.
Qed.

#[global] Instance FreeOmegaObservableMixedMeasureNodeBindLaws
    `{NBAE : @SemanticMeasureBindAEExactLaws MN NI} :
    @MixedMeasureNodeBindLaws MN (FreeOmega MN) NI
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure.
Proof.
  constructor. intros A B C mu h k.
  change (free_omega_qlift eq
    (FOSample mu (fun x => FOSample (h x) k))
    (FOSample (sem_bind mu h) k)).
  eapply FOQLSampleBind.
  - apply sem_ae_bind_iff.
  - intro y. apply free_omega_qlift_refl. intro z. reflexivity.
Qed.

Lemma free_omega_mixed_exchange_of_product
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    `{ND : @SemanticMeasureDiracAELaws MN NI}
    `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}
    {X Y} (mu : MN X) (nu : MN Y) :
  sem_lift semantic_pair_swap_rel
    (semantic_product mu nu) (semantic_product nu mu) ->
  @mixed_measure_exchange MN (FreeOmega MN) NI
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure X Y mu nu.
Proof.
  intro Hswap. intros A B R k1 k2 Hkl.
  change (free_omega_qlift R
    (FOSample mu (fun x => FOSample nu (k1 x)))
    (FOSample nu (fun y => FOSample mu (k2 y)))).
  eapply FOQLSampleExchange.
  - exact Hswap.
  - exact Hkl.
  - eapply free_omega_support_lift_sample_exchange; [exact Hswap|].
    intros x y. apply free_omega_qlift_support. exact (Hkl x y).
Qed.

#[global] Polymorphic Instance FreeOmegaObservableSemanticOmega :
    @SemanticOmega (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)) := {
  sem_zero := @FOZero MN;
  sem_le := fun A => @free_omega_approx MN NI A A eq;
  sem_lub := fun A chain out =>
    @sem_eq (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)) A
      out (FOLub chain);
  sem_total := fun A mu => exists representative : FreeOmega MN A,
    free_omega_qlift eq mu representative /\
    exists (O : Type) (obs : A -> O) (out : MN O),
      free_omega_observes obs representative out /\ sem_total out
}.

Lemma free_omega_observable_total_intro {A} (mu : FreeOmega MN A) :
  (exists (O : Type) (obs : A -> O) (out : MN O),
    free_omega_observes obs mu out /\ sem_total out) ->
  @sem_total (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega A mu.
Proof.
  intro Htotal. exists mu. split; [apply free_omega_qlift_refl;
    intros x; reflexivity|exact Htotal].
Qed.

#[global] Instance FreeOmegaObservableSemanticTotalProperLaws :
    @SemanticTotalProperLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega.
Proof.
  constructor. intros A mu nu Hmn. cbn. split.
  - intros [rep [Hmu Htotal]]. exists rep. split; [|exact Htotal].
    eapply FOQLComp with (T := eq) (U := eq) (mid := mu).
    + apply FOQLSym. eapply FOQLMono; [exact Hmn|].
      intros x y ->. reflexivity.
    + exact Hmu.
    + intros x z [y [-> ->]]. reflexivity.
  - intros [rep [Hnu Htotal]]. exists rep. split; [|exact Htotal].
    eapply FOQLComp with (T := eq) (U := eq) (mid := nu).
    + exact Hmn.
    + exact Hnu.
    + intros x z [y [-> ->]]. reflexivity.
Qed.

Lemma free_omega_cofinal_lub_iff {A}
    (left right : nat -> FreeOmega MN A) out :
  (forall n, free_omega_approx eq (left n) (left (S n))) ->
  (forall n, free_omega_approx eq (right n) (right (S n))) ->
  free_omega_chains_cofinal eq left right ->
  @sem_lub (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega A left out <->
  @sem_lub (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega A right out.
Proof.
  intros Hleft Hright Hcofinal. cbn. split; intro Hlim.
  - refine (FOQLComp (R := eq) Hlim (FOQLCofinal Hleft Hright Hcofinal) _).
    intros x z [y [-> ->]]. reflexivity.
  - refine (FOQLComp (R := eq) Hlim (FOQLSym (FOQLCofinal Hleft Hright Hcofinal)) _).
    intros x z [y [-> ->]]. reflexivity.
Qed.

#[global] Instance FreeOmegaObservableSemanticOmegaLaws :
    @SemanticOmegaLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega.
Proof.
  constructor.
  - intros A chain _. exists (FOLub chain).
    cbn.
    apply free_omega_qlift_refl. intros x. reflexivity.
  - intros A chain mu nu Hmu Hnu.
    cbn in Hmu, Hnu |- *.
    eapply (@sem_eq_trans _
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A); [exact Hmu|].
    eapply (@sem_eq_sym _
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A). exact Hnu.
  - intros A chain chain' mu nu Hcc Hmu Hnu.
    cbn in Hcc, Hmu, Hnu |- *.
    eapply (@sem_eq_trans _
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A); [exact Hmu|].
    eapply (@sem_eq_trans _
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A).
    + apply FOQLLub. exact Hcc.
    + eapply (@sem_eq_sym _
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws A). exact Hnu.
  - intros A chain chain' mu Hcc Hmu.
    cbn in Hcc, Hmu |- *.
    eapply (@sem_eq_trans _
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A); [exact Hmu|].
    apply FOQLLub. exact Hcc.
  - intros A B chain mu k _ Hmu.
    cbn in Hmu |- *.
    change (free_omega_qlift eq (free_omega_bind mu k)
      (free_omega_bind (FOLub chain) k)).
    eapply FOQLBind with (T := eq); [exact Hmu|].
    intros x y ->. apply free_omega_qlift_refl.
    intros z. reflexivity.
Qed.

#[global] Instance FreeOmegaObservableSemanticOmegaAELaws
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI} :
    @SemanticOmegaAELaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega.
Proof.
  constructor.
  - intros A P. constructor.
  - intros A chain out P Hlub HP. cbn in Hlub.
    pose proof (free_omega_qlift_support Hlub) as Hsupport.
    assert (Hchain : free_omega_ae P (FOLub chain)).
    { constructor. exact HP. }
    pose proof ((proj2 Hsupport) P Hchain) as Himage.
    eapply free_omega_ae_mono; [|exact Himage].
    intros x [y [Hxy Hy]]. subst y. exact Hy.
Qed.

#[global] Instance FreeOmegaObservableSemanticOmegaCofinalityLaws :
    @SemanticOmegaCofinalityLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega.
Proof.
  constructor.
  - intros A chain out. cbn. split; intro Hlim.
    + eapply (@sem_eq_trans _
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A); [exact Hlim|].
      apply FOQLLubZeroPrefixR. intro n.
      apply free_omega_qlift_refl. intros x. reflexivity.
    + eapply (@sem_eq_trans _
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A); [exact Hlim|].
      apply FOQLLubZeroPrefixL. intro n.
      apply free_omega_qlift_refl. intros x. reflexivity.
  - intros A mu. cbn. apply FOQLLubConstantR.
    apply free_omega_qlift_refl. intros x. reflexivity.
Qed.

#[global] Instance FreeOmegaObservableMixedMeasureOmegaLaws :
    @MixedMeasureOmegaLaws MN (FreeOmega MN) NI
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega.
Proof.
  constructor.
  - intros A B mu. cbn. apply FOQLSampleZero.
  - intros A B mu Good chain out Hae Hinc Hlim.
    cbn in Hlim |- *.
    eapply FOQLSampleLub; eauto.
Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureDiagonalLaws
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI} :
    @SemanticMeasureDiagonalLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega.
Proof.
  constructor. intros A B source source_out kernels kernel_out
    Hsource_inc Hkernels_inc Hsource Hkernels.
  cbn in Hsource, Hkernels |- *.
  eapply FOQLBindLub;
    [exact Hsource_inc|exact Hkernels_inc|exact Hsource|exact Hkernels|].
  eapply free_omega_support_lift_bind_diagonal; eauto.
  - apply free_omega_qlift_support. exact Hsource.
  - intro x. apply free_omega_qlift_support. exact (Hkernels x).
Qed.

#[global] Instance FreeOmegaObservableSemanticOmegaFubiniLaws
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI} :
    @SemanticOmegaFubiniLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega.
Proof.
  constructor. intros A grid row_out out Hrows_inc Hcols_inc Hrows Hout.
  cbn in Hrows, Hout |- *.
  eapply (@sem_eq_trans _
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws A); [exact Hout|].
  eapply (@sem_eq_trans _
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws A).
  - apply FOQLLub. exact Hrows.
  - eapply FOQLDoubleDiagonal with (HAB := eq_refl) (grid := grid).
    + intros outer inner. exact (Hrows_inc outer inner).
    + intros outer inner. exact (Hcols_inc inner outer).
    + intros x. reflexivity.
    + apply free_omega_support_lift_double_diagonal.
      * intros outer inner. exact (Hrows_inc outer inner).
      * intros outer inner. exact (Hcols_inc inner outer).
Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureOrderLaws :
    @SemanticMeasureOrderLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega.
Proof.
  constructor.
  - intros A mu. apply free_omega_approx_refl. intros x. reflexivity.
  - intros A mu nu xi Hmn Hnx.
    eapply free_omega_approx_mono with
      (R := fun x z => exists mid, x = mid /\ mid = z).
    + intros x z [mid [-> ->]]. reflexivity.
    + exact (free_omega_approx_comp (R := eq) (T := eq) Hmn Hnx).
  - intros A mu. constructor.
  - intros A B mu nu k Hmn.
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + exact Hmn.
    + intros x y ->. apply free_omega_approx_refl.
      intros z. reflexivity.
  - intros A B mu k h Hkh.
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply free_omega_approx_refl. intros x. reflexivity.
    + intros x y ->. apply Hkh.
Qed.

End FreeOmegaObservableLaws.
