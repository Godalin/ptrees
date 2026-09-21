(** Role: High-universe support transport required by observable coupling. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import FunctionalExtensionality.
From Coq.Program Require Import Equality.
Require Import Morphisms Arith.

From PTree.Prob.Interface Require Import Measure AE Coupling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.StructuralMeasure.


(** High-universe support transport, stated without choosing a concrete
    measure on the result carrier.  This is the information that an
    observation-level coupling must retain in addition to its low-universe
    denotation: every AE-good set on one representation is transported to
    the relational image on the other. *)
Polymorphic Definition free_omega_support_lift {MN}
    `{NI : SemanticMeasure MN} {A B}
    (R : A -> B -> Prop) (mu : FreeOmega MN A) (nu : FreeOmega MN B) : Prop :=
  (forall P, free_omega_ae P mu ->
    free_omega_ae (fun y => exists x, R x y /\ P x) nu) /\
  (forall Q, free_omega_ae Q nu ->
    free_omega_ae (fun x => exists y, R x y /\ Q y) mu).

Lemma free_omega_lift_support_lift {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    {A B} (R : A -> B -> Prop) mu nu :
  free_omega_lift R mu nu -> free_omega_support_lift R mu nu.
Proof.
  intro Hlift. split.
  - intro P. exact (free_omega_lift_ae_transport_r Hlift).
  - intro Q. apply free_omega_lift_ae_transport_r.
    exact (free_omega_lift_sym Hlift).
Qed.

(** Almost-everywhere predicates are downward closed along the finite
    subbehavior order.  This is the support fact needed by diagonal and
    cofinal quotient laws: a finite approximation cannot introduce a return
    outside the support of the behavior which contains it. *)
Lemma free_omega_approx_ae_backward {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    {A B} (R : A -> B -> Prop) mu nu (Q : B -> Prop) :
  free_omega_approx R mu nu -> free_omega_ae Q nu ->
  free_omega_ae (fun x => exists y, R x y /\ Q y) mu.
Proof.
  intros Happrox. induction Happrox; intro HQ.
  - constructor.
  - dependent destruction HQ. constructor. exists y. split; assumption.
  - dependent destruction HQ.
    eapply FOAESample with
      (Good := fun x => exists y, S x y /\ Good y).
    + apply sem_lift_ae_transport_r with
        (R := fun y x => S x y) (mu := nu) (nu := mu).
      * apply sem_lift_sym. exact H.
      * exact H2.
    + intros x [y [Hxy Hy]]. eapply H1; eauto.
  - dependent destruction HQ. constructor. intro n. eapply H0; eauto.
Qed.

Lemma free_omega_support_lift_mono {MN}
    `{NI : SemanticMeasure MN} {A B}
    (R T : A -> B -> Prop) mu nu :
  free_omega_support_lift R mu nu ->
  (forall x y, R x y -> T x y) ->
  free_omega_support_lift T mu nu.
Proof.
  intros [Hright Hleft] HRT. split.
  - intros P HP. eapply free_omega_ae_mono; [|exact (Hright P HP)].
    intros y [x [Hxy Hx]]. exists x. split; [apply HRT|]; assumption.
  - intros Q HQ. eapply free_omega_ae_mono; [|exact (Hleft Q HQ)].
    intros x [y [Hxy Hy]]. exists y. split; [apply HRT|]; assumption.
Qed.

Lemma free_omega_support_lift_sym {MN}
    `{NI : SemanticMeasure MN} {A B}
    (R : A -> B -> Prop) mu nu :
  free_omega_support_lift R mu nu ->
  free_omega_support_lift (fun y x => R x y) nu mu.
Proof. intros [Hright Hleft]. split; assumption. Qed.

Lemma free_omega_support_lift_comp {MN}
    `{NI : SemanticMeasure MN} {A B C}
    (R : A -> B -> Prop) (T : B -> C -> Prop) mu mid nu :
  free_omega_support_lift R mu mid ->
  free_omega_support_lift T mid nu ->
  free_omega_support_lift
    (fun x z => exists y, R x y /\ T y z) mu nu.
Proof.
  intros [HRr HRl] [HTr HTl]. split.
  - intros P HP. specialize (HRr P HP). specialize (HTr _ HRr).
    eapply free_omega_ae_mono; [|exact HTr].
    intros z [y [Hyz [x [Hxy Hx]]]].
    exists x. split; [exists y; split|]; assumption.
  - intros Q HQ. specialize (HTl Q HQ). specialize (HRl _ HTl).
    eapply free_omega_ae_mono; [|exact HRl].
    intros x [y [Hxy [z [Hyz Hz]]]].
    exists z. split; [exists y; split|]; assumption.
Qed.

Lemma free_omega_support_lift_restrict {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    {A B} (R : A -> B -> Prop) mu nu (P : A -> Prop) (Q : B -> Prop) :
  free_omega_support_lift R mu nu ->
  free_omega_ae P mu -> free_omega_ae Q nu ->
  free_omega_support_lift (fun x y => R x y /\ P x /\ Q y) mu nu.
Proof.
  intros [Hright Hleft] HP HQ. split.
  - intros P0 HP0.
    pose proof (free_omega_ae_conj (P := P0) (Q := P)
      (mu := mu) HP0 HP) as HPboth.
    pose proof (Hright _ HPboth) as Himage.
    pose proof (free_omega_ae_conj (P := _ ) (Q := Q)
      (mu := nu) Himage HQ) as Hboth.
    eapply free_omega_ae_mono; [|exact Hboth].
    intros y [[x [Hxy [HP0x HPx]]] HQy].
    exists x. repeat split; assumption.
  - intros Q0 HQ0.
    pose proof (free_omega_ae_conj (P := Q0) (Q := Q)
      (mu := nu) HQ0 HQ) as HQboth.
    pose proof (Hleft _ HQboth) as Himage.
    pose proof (free_omega_ae_conj (P := _) (Q := P)
      (mu := mu) Himage HP) as Hboth.
    eapply free_omega_ae_mono; [|exact Hboth].
    intros x [[y [Hxy [HQ0y HQy]]] HPx].
    exists y. repeat split; assumption.
Qed.

Lemma free_omega_support_lift_bind {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    {A B C D} (T : C -> D -> Prop) (R : A -> B -> Prop)
    mu nu (k : C -> FreeOmega MN A) (h : D -> FreeOmega MN B) :
  free_omega_support_lift T mu nu ->
  (forall x y, T x y -> free_omega_support_lift R (k x) (h y)) ->
  free_omega_support_lift R
    (free_omega_bind mu k) (free_omega_bind nu h).
Proof.
  intros [HTRight HTLeft] Hkh. split.
  - intros P HP. apply free_omega_ae_bind_inv in HP.
    specialize (HTRight _ HP).
    eapply free_omega_ae_bind; [exact HTRight|].
    intros y [x [Hxy Hpx]].
    exact ((proj1 (Hkh x y Hxy)) P Hpx).
  - intros Q HQ. apply free_omega_ae_bind_inv in HQ.
    specialize (HTLeft _ HQ).
    eapply free_omega_ae_bind; [exact HTLeft|].
    intros x [y [Hxy Hqy]].
    exact ((proj2 (Hkh x y Hxy)) Q Hqy).
Qed.

Lemma free_omega_support_lift_sample {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    {A B C D} (T : C -> D -> Prop) (R : A -> B -> Prop)
    (mu : MN C) (nu : MN D)
    (k : C -> FreeOmega MN A) (h : D -> FreeOmega MN B) :
  sem_lift T mu nu ->
  (forall x y, T x y -> free_omega_support_lift R (k x) (h y)) ->
  free_omega_support_lift R (FOSample mu k) (FOSample nu h).
Proof.
  intros HT Hkh. split.
  - intros P HP. dependent destruction HP.
    eapply FOAESample with
      (Good := fun y => exists x, T x y /\ Good x).
    + eapply sem_lift_ae_transport_r; eassumption.
    + intros y [x [Hxy Hx]].
      apply (proj1 (Hkh x y Hxy) P). eauto.
  - intros Q HQ. dependent destruction HQ.
    eapply FOAESample with
      (Good := fun x => exists y, T x y /\ Good y).
    + eapply sem_lift_ae_transport_r with
        (R := fun y x => T x y) (mu := nu) (nu := mu).
      * apply sem_lift_sym. exact HT.
      * eassumption.
    + intros x [y [Hxy Hy]].
      apply (proj2 (Hkh x y Hxy) Q). eauto.
Qed.

Lemma free_omega_ae_sample_inv {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    {A C} (mu : MN C) (k : C -> FreeOmega MN A) (P : A -> Prop) :
  free_omega_ae P (FOSample mu k) ->
  sem_ae mu (fun x => free_omega_ae P (k x)).
Proof.
  intro HP. dependent destruction HP.
  eapply sem_ae_mono; [|eassumption]. intros x Hx. eauto.
Qed.

Lemma free_omega_support_lift_sample_lub {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A B C} (R : A -> B -> Prop) (mu : MN C) (Good : C -> Prop)
    (chain : C -> nat -> FreeOmega MN B)
    (out : C -> FreeOmega MN A) :
  sem_ae mu Good ->
  (forall x, Good x ->
    free_omega_support_lift R (out x) (FOLub (chain x))) ->
  free_omega_support_lift R
    (FOSample mu out)
    (FOLub (fun n => FOSample mu (fun x => chain x n))).
Proof.
  intros HGood Hout. split.
  - intros P HP. apply free_omega_ae_sample_inv in HP. constructor. intro n.
    eapply FOAESample with
      (Good := fun x => Good x /\ free_omega_ae P (out x)).
    + apply sem_ae_conj; assumption.
    + intros x [HxGood HxP].
      pose proof ((proj1 (Hout x HxGood)) P HxP) as Hlub.
      dependent destruction Hlub. eauto.
  - intros Q HQ. dependent destruction HQ.
    eapply FOAESample with
      (Good := fun x => Good x /\
        forall n, free_omega_ae Q (chain x n)).
    + apply sem_ae_conj; [exact HGood|].
      apply sem_ae_countable. intro n.
      apply free_omega_ae_sample_inv. eauto.
    + intros x [HxGood HxQ].
      apply (proj2 (Hout x HxGood) Q). constructor. exact HxQ.
Qed.

Lemma free_omega_support_lift_lub {MN}
    `{NI : SemanticMeasure MN} {A B}
    (R : A -> B -> Prop) (c : nat -> FreeOmega MN A)
    (d : nat -> FreeOmega MN B) :
  (forall n, free_omega_support_lift R (c n) (d n)) ->
  free_omega_support_lift R (FOLub c) (FOLub d).
Proof.
  intro Hcd. split; intros P HP; dependent destruction HP; constructor;
    intro n; [apply (proj1 (Hcd n))|apply (proj2 (Hcd n))]; auto.
Qed.

Lemma free_omega_support_lift_lub_zero_prefix_l {MN}
    `{NI : SemanticMeasure MN} {A B}
    (R : A -> B -> Prop) (c : nat -> FreeOmega MN A)
    (d : nat -> FreeOmega MN B) :
  (forall n, free_omega_support_lift R (c n) (d n)) ->
  free_omega_support_lift R
    (FOLub (fun n => match n with O => FOZero
      | Datatypes.S n' => c n' end)) (FOLub d).
Proof.
  intro Hcd. split.
  - intros P HP. dependent destruction HP. constructor. intro n.
    apply (proj1 (Hcd n) P).
    match goal with
    | Hchain : forall i : nat, _ |- _ =>
        exact (Hchain (S n))
    end.
  - intros P HP. dependent destruction HP. constructor. intros [|n].
    + constructor.
    + apply (proj2 (Hcd n) P).
      match goal with
      | Hchain : forall i : nat, _ |- _ =>
          exact (Hchain n)
      end.
Qed.

Lemma free_omega_support_lift_sample_zero {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    {A B C} (R : A -> B -> Prop) (mu : MN C) :
  free_omega_support_lift R (FOSample mu (fun _ => @FOZero MN A))
    (@FOZero MN B).
Proof.
  split; intros P HP.
  - constructor.
  - eapply FOAESample with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros. constructor.
Qed.

Lemma free_omega_support_lift_lub_constant_r {MN}
    `{NI : SemanticMeasure MN} {A B}
    (R : A -> B -> Prop) mu nu :
  free_omega_support_lift R mu nu ->
  free_omega_support_lift R mu (FOLub (fun _ => nu)).
Proof.
  intros [Hright Hleft]. split.
  - intros P HP. constructor. intro n. exact (Hright P HP).
  - intros Q HQ. dependent destruction HQ. apply Hleft.
    match goal with
    | Hchain : forall i : nat, _ |- _ => exact (Hchain 0)
    end.
Qed.

Lemma free_omega_support_lift_bind_diagonal {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A B} (R : B -> B -> Prop)
    (source : nat -> FreeOmega MN A) (source_out : FreeOmega MN A)
    (kernels : A -> nat -> FreeOmega MN B)
    (kernel_out : A -> FreeOmega MN B) :
  (forall n, free_omega_approx eq (source n) (source (S n))) ->
  (forall x n,
    free_omega_approx eq (kernels x n) (kernels x (S n))) ->
  free_omega_support_lift eq source_out (FOLub source) ->
  (forall x, free_omega_support_lift R
    (kernel_out x) (FOLub (kernels x))) ->
  free_omega_support_lift R
    (free_omega_bind source_out kernel_out)
    (FOLub (fun n => free_omega_bind (source n)
      (fun x => kernels x n))).
Proof.
  intros Hsource_inc Hkernels_inc Hsource Hkernels. split.
  - intros P HP. apply free_omega_ae_bind_inv in HP.
    pose proof ((proj1 Hsource) _ HP) as HsourceP.
    eapply free_omega_ae_mono in HsourceP.
    2: { intros x [y [-> Hy]]. exact Hy. }
    dependent destruction HsourceP. constructor. intro n.
    eapply free_omega_ae_bind; [eauto|]. intros x Hx.
    pose proof ((proj1 (Hkernels x)) P Hx) as HkernelP.
    dependent destruction HkernelP. eauto.
  - intros Q HQ. dependent destruction HQ.
    apply free_omega_ae_bind with
      (P := fun x => forall j, free_omega_ae Q (kernels x j)).
    + eapply free_omega_ae_mono.
      2: { apply (proj2 Hsource). constructor. intro i.
        apply free_omega_ae_countable. intro j.
      pose (fuel := i + j).
      assert (Hdiag : free_omega_ae Q
          (free_omega_bind (source fuel)
            (fun x => kernels x fuel))) by eauto.
      apply free_omega_ae_bind_inv in Hdiag.
      pose proof (free_omega_approx_steps Hsource_inc i j) as Hsrc.
      pose proof (free_omega_approx_ae_backward
        (R := eq) Hsrc Hdiag) as Hsrc_ae.
      eapply free_omega_ae_mono in Hsrc_ae.
      2: { intros x [y [-> Hy]]. exact Hy. }
      eapply free_omega_ae_mono; [|exact Hsrc_ae]. intros x Hfuel.
      pose proof (free_omega_approx_steps (Hkernels_inc x) j i) as Hkernel.
      replace (j + i) with fuel in Hkernel by
        (unfold fuel; apply Nat.add_comm).
      pose proof (free_omega_approx_ae_backward
        (R := eq) Hkernel Hfuel) as Hj.
      eapply free_omega_ae_mono; [|exact Hj].
      intros y [z [-> Hz]]. exact Hz. }
      intros x [y [-> Hy]]. exact Hy.
    + intros x Hx. apply (proj2 (Hkernels x) Q). constructor. exact Hx.
Qed.

Lemma free_omega_support_lift_double_diagonal {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    {A} (grid : nat -> nat -> FreeOmega MN A) :
  (forall outer inner,
    free_omega_approx eq (grid outer inner) (grid outer (S inner))) ->
  (forall outer inner,
    free_omega_approx eq (grid outer inner) (grid (S outer) inner)) ->
  free_omega_support_lift eq
    (FOLub (fun outer => FOLub (grid outer)))
    (FOLub (fun fuel => grid fuel fuel)).
Proof.
  intros Hrows Hcols. split.
  - intros P HP. dependent destruction HP. constructor. intro fuel.
    match goal with
    | Houter : forall i : nat, _ |- _ =>
      specialize (Houter fuel); dependent destruction Houter
    end.
    eapply free_omega_ae_mono; [|eauto].
    intros x Hx. exists x. split; [reflexivity|exact Hx].
  - intros P HP. dependent destruction HP. constructor. intro outer.
    constructor. intro inner. pose (fuel := outer + inner).
    assert (Hfuel : free_omega_ae P (grid fuel fuel)) by eauto.
    pose proof (free_omega_approx_steps (Hrows outer) inner outer) as Hrow.
    replace (inner + outer) with fuel in Hrow by
      (unfold fuel; apply Nat.add_comm).
    pose proof (free_omega_approx_steps
      (fun n => Hcols n fuel) outer inner) as Hcol.
    pose proof (free_omega_approx_trans Hrow Hcol) as Happrox.
    pose proof (free_omega_approx_ae_backward
      (R := eq) Happrox Hfuel) as Hback.
    eapply free_omega_ae_mono; [|exact Hback].
    intros x [y [-> Hy]]. exists y. split; [reflexivity|exact Hy].
Qed.

Lemma free_omega_support_lift_sample_bind {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    {A B C D} (R : A -> B -> Prop)
    (mu : MN C) (h : C -> MN D)
    (k : D -> FreeOmega MN A) (l : D -> FreeOmega MN B) :
  (forall P, sem_ae (sem_bind mu h) P <->
    sem_ae mu (fun x => sem_ae (h x) P)) ->
  (forall y, free_omega_support_lift R (k y) (l y)) ->
  free_omega_support_lift R
    (FOSample mu (fun x => FOSample (h x) k))
    (FOSample (sem_bind mu h) l).
Proof.
  intros Hbind Hkl. split.
  - intros P HP. dependent destruction HP.
    match goal with
    | Houter : sem_ae mu ?Good,
      Hinner : forall x, ?Good x -> _ |- _ =>
      eapply FOAESample with
        (Good := fun y => exists x, Good x /\
          free_omega_ae P (k y));
      [apply (proj2 (Hbind _));
       eapply sem_ae_mono; [|exact Houter];
       intros x Hx; specialize (Hinner x Hx);
       dependent destruction Hinner;
       eapply sem_ae_mono; [|eassumption];
       intros y Hy; exists x; split; [exact Hx|eauto]
      |intros y [x [Hx Hky]];
       exact ((proj1 (Hkl y)) P Hky)]
    end.
  - intros Q HQ. dependent destruction HQ.
    apply (proj1 (Hbind _)) in H.
    eapply FOAESample with
      (Good := fun x => sem_ae (h x) Good).
    + exact H.
    + intros x Hx. eapply FOAESample with (Good := Good).
      * exact Hx.
      * intros y Hy. apply (proj2 (Hkl y) Q). apply H0. exact Hy.
Qed.

Definition semantic_product {MN}
    `{NI : SemanticMeasure MN} {X Y}
    (mu : MN X) (nu : MN Y) : MN (X * Y)%type :=
  sem_bind mu (fun x => sem_bind nu (fun y => sem_ret (x, y))).

Lemma free_omega_ae_sample2_product_iff {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{ND : @SemanticMeasureDiracAELaws MN NI}
    `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}
    {A X Y} (P : A -> Prop) (mu : MN X) (nu : MN Y)
    (k : X -> Y -> FreeOmega MN A) :
  free_omega_ae P (FOSample mu (fun x => FOSample nu (k x))) <->
  sem_ae (semantic_product mu nu)
    (fun p => free_omega_ae P (k (fst p) (snd p))).
Proof.
  split.
  - intro Hnested. dependent destruction Hnested.
    apply (proj2 (sem_ae_bind_iff _ _ _)).
    eapply sem_ae_mono; [|exact H]. intros x Hx.
    specialize (H0 x Hx). dependent destruction H0.
    apply (proj2 (sem_ae_bind_iff _ _ _)).
    eapply sem_ae_mono; [|exact H0]. intros y Hy.
    apply (proj2 (sem_ae_ret_iff _ _)). exact (H1 y Hy).
  - intro Hproduct.
    apply (proj1 (sem_ae_bind_iff _ _ _)) in Hproduct.
    eapply FOAESample with
      (Good := fun x => sem_ae
        (sem_bind nu (fun y => sem_ret (x, y)))
        (fun p => free_omega_ae P (k (fst p) (snd p)))).
    + exact Hproduct.
    + intros x Hx.
      apply (proj1 (sem_ae_bind_iff _ _ _)) in Hx.
      eapply FOAESample with
        (Good := fun y => sem_ae (sem_ret (x, y))
          (fun p => free_omega_ae P (k (fst p) (snd p)))).
      * exact Hx.
      * intros y Hy. apply (proj1 (sem_ae_ret_iff _ _)) in Hy.
        exact Hy.
Qed.

Definition semantic_pair_swap_rel {X Y}
    (p : X * Y) (q : Y * X) : Prop :=
  fst p = snd q /\ snd p = fst q.

Lemma free_omega_support_lift_sample_exchange {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{ND : @SemanticMeasureDiracAELaws MN NI}
    `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}
    {A B X Y} (R : A -> B -> Prop)
    (mu : MN X) (nu : MN Y)
    (k1 : X -> Y -> FreeOmega MN A)
    (k2 : Y -> X -> FreeOmega MN B) :
  sem_lift semantic_pair_swap_rel
    (semantic_product mu nu) (semantic_product nu mu) ->
  (forall x y, free_omega_support_lift R (k1 x y) (k2 y x)) ->
  free_omega_support_lift R
    (FOSample mu (fun x => FOSample nu (k1 x)))
    (FOSample nu (fun y => FOSample mu (k2 y))).
Proof.
  intros Hswap Hkl. split.
  - intros P HP.
    apply (proj2 (free_omega_ae_sample2_product_iff
      (fun b => exists a, R a b /\ P a) nu mu k2)).
    pose proof (proj1 (free_omega_ae_sample2_product_iff
      P mu nu k1) HP) as Hprod.
    pose proof (sem_lift_ae_transport_r Hswap Hprod) as Htransport.
    eapply sem_ae_mono; [|exact Htransport].
    intros [y x] [[x' y'] [[Hxx Hyy] HPxy]]. cbn in *.
    subst x'. subst y'. apply (proj1 (Hkl x y) P). exact HPxy.
  - intros Q HQ.
    apply (proj2 (free_omega_ae_sample2_product_iff
      (fun a => exists b, R a b /\ Q b) mu nu k1)).
    pose proof (proj1 (free_omega_ae_sample2_product_iff
      Q nu mu k2) HQ) as Hprod.
    pose proof (sem_lift_ae_transport_r (sem_lift_sym Hswap) Hprod)
      as Htransport.
    eapply sem_ae_mono; [|exact Htransport].
    intros [x y] [[y' x'] [[Hyy Hxx] HQyx]]. cbn in *.
    subst y'. subst x'. apply (proj2 (Hkl x y) Q). exact HQyx.
Qed.
