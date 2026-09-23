(** Role: Auxiliary structural measure instances and laws; not the observable canonical quotient. *)
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

Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation.


(** Structural operations and their indexed laws are internal proof tools.
    Their constants remain available, but importing this module does not
    register them for global search. Structural clients opt in locally.
    The shared [FreeOmegaMixedMeasure] operation below is the sole global
    exception: it does not select an equality/lifting interpretation. *)
#[local] Polymorphic Instance FreeOmegaSemanticMeasure {MN}
    `{NI : SemanticMeasure MN} :
    SemanticMeasure (FreeOmega MN) := {
  sem_ret := @FORet MN;
  sem_bind := @free_omega_bind MN;
  sem_eq := fun A => @free_omega_lift MN NI A A eq;
  sem_ae := fun A mu P => @free_omega_ae MN NI A P mu;
  sem_lift := @free_omega_lift MN NI
}.

Lemma free_omega_sem_retE {MN} `{NI : SemanticMeasure MN}
    {A} (x : A) :
  @sem_ret (FreeOmega MN)
    (FreeOmegaSemanticMeasure (NI := NI)) A x = FORet x.
Proof. reflexivity. Qed.

Section FreeOmegaLaws.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}.

Lemma free_omega_ae_mono {A} (P Q : A -> Prop) mu :
  (forall x, P x -> Q x) -> free_omega_ae P mu -> free_omega_ae Q mu.
Proof.
  intros HPQ Hae. induction Hae.
  - constructor. exact (HPQ _ H).
  - constructor.
  - eapply FOAESample; [exact H|]. intros x Hx. exact (H1 x Hx).
  - constructor. exact H0.
Qed.

Lemma free_omega_ae_conj {A} (P Q : A -> Prop) mu :
  free_omega_ae P mu -> free_omega_ae Q mu ->
  free_omega_ae (fun x => P x /\ Q x) mu.
Proof.
  intros HP. revert Q. induction HP; intros Q HQ; dependent destruction HQ.
  - constructor. split; assumption.
  - constructor.
  - eapply FOAESample with (Good := fun x => Good x /\ Good0 x).
    + eapply sem_ae_conj; eassumption.
    + intros x [Hx Hx0]. eapply H1; eauto.
  - constructor. intro n. eapply H0. exact (H1 n).
Qed.

Lemma free_omega_ae_bind {A B} (mu : FreeOmega MN A)
    (k : A -> FreeOmega MN B) (P : A -> Prop) (Q : B -> Prop) :
  free_omega_ae P mu ->
  (forall x, P x -> free_omega_ae Q (k x)) ->
  free_omega_ae Q (free_omega_bind mu k).
Proof.
  intros Hae Hk. induction Hae; cbn.
  - exact (Hk x H).
  - constructor.
  - eapply FOAESample; [exact H|].
    intros x Hx. exact (H1 x Hx).
  - constructor. exact H0.
Qed.

Lemma free_omega_ae_bind_inv {A B} (mu : FreeOmega MN A)
    (k : A -> FreeOmega MN B) (P : B -> Prop) :
  free_omega_ae P (free_omega_bind mu k) ->
  free_omega_ae (fun x => free_omega_ae P (k x)) mu.
Proof.
  induction mu; cbn; intro Hae.
  - constructor. exact Hae.
  - constructor.
  - dependent destruction Hae. eapply FOAESample; [exact H0|].
    intros x Hx. exact (H x (H1 x Hx)).
  - dependent destruction Hae. constructor. intro n.
    exact (H n (H0 n)).
Qed.

Lemma free_omega_lift_mono {A B} (R T : A -> B -> Prop) mu nu :
  (forall x y, R x y -> T x y) ->
  free_omega_lift R mu nu -> free_omega_lift T mu nu.
Proof.
  intros HRT Hl. induction Hl.
  - apply FOLRet. exact (HRT _ _ H).
  - apply FOLZero.
  - eapply FOLSample; [exact H|exact H1].
  - apply FOLLub. exact H0.
Qed.

Lemma free_omega_lift_refl {A} (R : A -> A -> Prop) mu :
  Reflexive R -> free_omega_lift R mu mu.
Proof.
  intros HR. induction mu.
  - constructor. apply HR.
  - constructor.
  - eapply FOLSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. exact (H y).
  - constructor. exact H.
Qed.

Lemma free_omega_approx_refl {A} (R : A -> A -> Prop) mu :
  Reflexive R -> free_omega_approx R mu mu.
Proof.
  intros HR. induction mu.
  - constructor. apply HR.
  - constructor.
  - eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. exact (H y).
  - constructor. exact H.
Qed.

Lemma free_omega_approx_mono {A B} (R T : A -> B -> Prop) mu nu :
  (forall x y, R x y -> T x y) ->
  free_omega_approx R mu nu -> free_omega_approx T mu nu.
Proof.
  intros HRT Happrox. induction Happrox.
  - constructor.
  - constructor. exact (HRT _ _ H).
  - eapply FOApproxSample; [exact H|exact H1].
  - constructor. exact H0.
Qed.

Lemma free_omega_approx_comp {A B C}
    (R : A -> B -> Prop) (T : B -> C -> Prop) mu nu xi :
  free_omega_approx R mu nu -> free_omega_approx T nu xi ->
  free_omega_approx (fun x z => exists y, R x y /\ T y z) mu xi.
Proof.
  intros H12. revert C T xi.
  induction H12; intros C T xi H23.
  - constructor.
  - dependent destruction H23. constructor. eexists. split; eassumption.
  - dependent destruction H23.
    eapply FOApproxSample with
      (S := fun x z => exists y, S x y /\ S0 y z).
    + eapply sem_lift_comp; eassumption.
    + intros x z [y [Hxy Hyz]]. eapply H1; eauto.
  - dependent destruction H23. constructor. intro n.
    eapply H0. exact (H1 n).
Qed.

Lemma free_omega_approx_trans {A}
    (mu nu xi : FreeOmega MN A) :
  free_omega_approx eq mu nu -> free_omega_approx eq nu xi ->
  free_omega_approx eq mu xi.
Proof.
  intros Hmn Hnx. eapply free_omega_approx_mono with
    (R := fun x z => exists mid, x = mid /\ mid = z).
  - intros x z [mid [-> ->]]. reflexivity.
  - exact (free_omega_approx_comp (R := eq) (T := eq) Hmn Hnx).
Qed.

Lemma free_omega_approx_steps {A} (c : nat -> FreeOmega MN A) :
  (forall n, free_omega_approx eq (c n) (c (S n))) ->
  forall n k, free_omega_approx eq (c n) (c (n + k)).
Proof.
  intros Hinc n k. induction k.
  - replace (n + 0) with n by exact (plus_n_O n).
    apply free_omega_approx_refl. intros x. exact eq_refl.
  - replace (n + S k) with (S (n + k)) by
      exact (plus_n_Sm n k).
    eapply free_omega_approx_trans; eauto.
Qed.

Lemma free_omega_lift_sym {A B} (R : A -> B -> Prop) mu nu :
  free_omega_lift R mu nu ->
  free_omega_lift (fun y x => R x y) nu mu.
Proof.
  intros Hl. induction Hl.
  - constructor. exact H.
  - constructor.
  - eapply FOLSample with (S := fun y x => S x y).
    + exact (sem_lift_sym H).
    + intros y x Hyx. exact (H1 x y Hyx).
  - constructor. exact H0.
Qed.

Lemma free_omega_lift_comp {A B C}
    (R : A -> B -> Prop) (T : B -> C -> Prop) mu nu xi :
  free_omega_lift R mu nu -> free_omega_lift T nu xi ->
  free_omega_lift (fun x z => exists y, R x y /\ T y z) mu xi.
Proof.
  intros H12. revert C T xi.
  induction H12; intros C T xi H23; dependent destruction H23.
  - constructor. eexists. split; eassumption.
  - constructor.
  - eapply FOLSample with
      (S := fun x z => exists y, S x y /\ S0 y z).
    + eapply sem_lift_comp; eassumption.
    + intros x z [y [Hxy Hyz]]. eapply H1; eauto.
  - constructor. intro n. eapply H0. exact (H1 n).
Qed.

#[local] Polymorphic Instance FreeOmegaSemanticMeasureCoreLaws :
    @SemanticMeasureCoreLaws (FreeOmega MN)
      (FreeOmegaSemanticMeasure (NI := NI)).
Proof.
  constructor.
  - intros A mu. apply free_omega_lift_refl. intros x. reflexivity.
  - intros A mu nu Hmn.
    eapply free_omega_lift_mono; [|exact (free_omega_lift_sym Hmn)].
    intros x y Hyx. symmetry. exact Hyx.
  - intros A mu nu xi Hmn Hnx.
    eapply free_omega_lift_mono;
      [|exact (free_omega_lift_comp (R := eq) (T := eq) Hmn Hnx)].
    intros x z [y [-> ->]]. reflexivity.
  - intros A mu. induction mu.
    + apply FOAERet. exact I.
    + apply FOAEZero.
    + eapply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros x _. exact (H x).
    + apply FOAELub. exact H.
  - intros A mu P Q. exact (free_omega_ae_mono (P := P) (Q := Q) (mu := mu)).
  - intros A mu P Q. exact (free_omega_ae_conj (P := P) (Q := Q) (mu := mu)).
  - exact @free_omega_lift_mono.
  - exact @free_omega_lift_refl.
  - intros A B R x y Hxy. constructor. exact Hxy.
  - intros A B R mu mu' nu Hmm Hmn.
    assert (Hmm' : free_omega_lift eq mu' mu).
    { eapply free_omega_lift_mono; [|exact (free_omega_lift_sym Hmm)].
      intros x y Hyx. symmetry. exact Hyx. }
    eapply free_omega_lift_mono;
      [|exact (free_omega_lift_comp (R := eq) (T := R) Hmm' Hmn)].
    intros x z [y [-> Hyz]]. exact Hyz.
  - intros A B R mu nu nu' Hnn Hmn.
    eapply free_omega_lift_mono;
      [|exact (free_omega_lift_comp (R := R) (T := eq) Hmn Hnn)].
    intros x z [y [Hxy ->]]. exact Hxy.
  - exact @free_omega_lift_sym.
  - exact @free_omega_lift_comp.
Qed.

#[local] Polymorphic Instance FreeOmegaSemanticMeasureAEKleisliLaws :
    @SemanticMeasureAEKleisliLaws (FreeOmega MN)
      (FreeOmegaSemanticMeasure (NI := NI)).
Proof.
  constructor.
  - intros A P x Hx. constructor. exact Hx.
  - intros A B mu k P Q Hmu Hk.
    cbn in Hmu, Hk |- *. exact (free_omega_ae_bind Hmu Hk).
Qed.

Lemma free_omega_ae_countable
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A} (mu : FreeOmega MN A) (P : nat -> A -> Prop) :
  (forall n, free_omega_ae (P n) mu) ->
  free_omega_ae (fun x => forall n, P n x) mu.
Proof.
  revert P. induction mu as [x| |X node k IH|chain IH]; intros P HP.
  - constructor. intro n. specialize (HP n). dependent destruction HP.
    assumption.
  - constructor.
  - eapply FOAESample with
      (Good := fun x => forall n, free_omega_ae (P n) (k x)).
    + apply sem_ae_countable. intro n.
      specialize (HP n). dependent destruction HP.
      eapply sem_ae_mono; [|eassumption]. intros y Hy. eauto.
    + intros x Hx. apply IH. exact Hx.
  - constructor. intro m. apply IH. intro n. specialize (HP n).
    dependent destruction HP. eauto.
Qed.

#[local] Polymorphic Instance FreeOmegaSemanticMeasureCountableAELaws
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI} :
    @SemanticMeasureCountableAELaws (FreeOmega MN)
      (FreeOmegaSemanticMeasure (NI := NI)).
Proof.
  constructor. intros A mu P HP. apply free_omega_ae_countable. exact HP.
Qed.

Lemma free_omega_lift_ae_restrict
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    {A B} (R : A -> B -> Prop) (mu : FreeOmega MN A)
    (nu : FreeOmega MN B) (P : A -> Prop) (Q : B -> Prop) :
  free_omega_lift R mu nu ->
  free_omega_ae P mu -> free_omega_ae Q nu ->
  free_omega_lift (fun x y => R x y /\ P x /\ Q y) mu nu.
Proof.
  intros Hlift. induction Hlift; intros HP HQ;
    dependent destruction HP; dependent destruction HQ.
  - constructor. repeat split; assumption.
  - constructor.
  - eapply FOLSample with
      (S := fun x y => S x y /\ Good x /\ Good0 y).
    + eapply sem_lift_ae_restrict; eassumption.
    + intros x y [Hxy [Hx Hy]]. eapply H1; eauto.
  - constructor. intro n. eapply H0; eauto.
Qed.

Lemma free_omega_lift_ae_transport_r
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    {A B} (R : A -> B -> Prop) (mu : FreeOmega MN A)
    (nu : FreeOmega MN B) (P : A -> Prop) :
  free_omega_lift R mu nu -> free_omega_ae P mu ->
  free_omega_ae (fun y => exists x, R x y /\ P x) nu.
Proof.
  intros Hlift HP. induction Hlift; dependent destruction HP.
  - constructor. exists x. split; assumption.
  - constructor.
  - eapply FOAESample with
      (Good := fun y => exists x, S x y /\ Good x).
    + eapply sem_lift_ae_transport_r; eassumption.
    + intros y [x [Hxy Hx]]. eapply H1; eauto.
  - constructor. intro n. exact (H0 n (H1 n)).
Qed.

#[local] Polymorphic Instance FreeOmegaSemanticMeasureCouplingAELaws
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI} :
    @SemanticMeasureCouplingAELaws (FreeOmega MN)
      (FreeOmegaSemanticMeasure (NI := NI)).
Proof.
  constructor.
  - intros A B R mu nu P Hlift HP.
    exact (free_omega_lift_ae_transport_r
      (NCAE := NCAE) Hlift HP).
  - intros A B R mu nu P Q Hlift HP HQ.
    exact (free_omega_lift_ae_restrict
      (NCAE := NCAE) Hlift HP HQ).
Qed.

Lemma free_omega_bind_assoc {A B C} (mu : FreeOmega MN A)
    (k : A -> FreeOmega MN B) (h : B -> FreeOmega MN C) :
  free_omega_bind (free_omega_bind mu k) h =
  free_omega_bind mu (fun x => free_omega_bind (k x) h).
Proof.
  induction mu; cbn; try reflexivity.
  - f_equal. apply functional_extensionality. exact H.
  - f_equal. apply functional_extensionality. exact H.
Qed.

Lemma free_omega_lift_bind {A B C D}
    (R : A -> B -> Prop) (T : C -> D -> Prop)
    (mu : FreeOmega MN A) (nu : FreeOmega MN B)
    (k : A -> FreeOmega MN C) (h : B -> FreeOmega MN D) :
  free_omega_lift R mu nu ->
  (forall x y, R x y -> free_omega_lift T (k x) (h y)) ->
  free_omega_lift T (free_omega_bind mu k) (free_omega_bind nu h).
Proof.
  intros Hl Hkh. induction Hl; cbn.
  - exact (Hkh _ _ H).
  - constructor.
  - eapply FOLSample; [exact H|]. intros x y Hxy. exact (H1 x y Hxy).
  - constructor. exact H0.
Qed.

Lemma free_omega_bind_ae_proper
    `{NAE : @SemanticMeasureAELiftLaws MN NI}
    {A B} (mu : FreeOmega MN A) (k h : A -> FreeOmega MN B) :
  free_omega_ae (fun x => free_omega_lift eq (k x) (h x)) mu ->
  free_omega_lift eq (free_omega_bind mu k) (free_omega_bind mu h).
Proof.
  intros Hae. induction Hae; cbn.
  - exact H.
  - constructor.
  - eapply FOLSample with (S := fun x y => x = y /\ Good x).
    + exact (sem_lift_refl_ae H).
    + intros x y [-> Hy]. exact (H1 y Hy).
  - constructor. exact H0.
Qed.

#[local] Polymorphic Instance FreeOmegaSemanticMeasureBindLaws
    `{NAE : @SemanticMeasureAELiftLaws MN NI} :
    @SemanticMeasureBindLaws (FreeOmega MN)
      (FreeOmegaSemanticMeasure (NI := NI)).
Proof.
  constructor.
  - intros A B x k. apply free_omega_lift_refl. intros y. reflexivity.
  - intros A B C mu k h.
    change (free_omega_lift eq
      (free_omega_bind (free_omega_bind mu k) h)
      (free_omega_bind mu (fun x => free_omega_bind (k x) h))).
    rewrite free_omega_bind_assoc.
    apply free_omega_lift_refl. intros y. reflexivity.
  - intros A B mu k h Hae. exact (free_omega_bind_ae_proper Hae).
  - exact @free_omega_lift_bind.
Qed.

#[global] Polymorphic Instance FreeOmegaMixedMeasure :
    MixedMeasure MN (FreeOmega MN) := {
  mixed_bind := fun A B mu k => @FOSample MN B A mu k
}.

Lemma free_omega_mixed_bindE {A B} (mu : MN A)
    (k : A -> FreeOmega MN B) :
  @mixed_bind MN (FreeOmega MN) FreeOmegaMixedMeasure
    A B mu k = FOSample mu k.
Proof. reflexivity. Qed.

#[local] Polymorphic Instance FreeOmegaMixedMeasureLaws
    `{NAE : @SemanticMeasureAELiftLaws MN NI} :
    @MixedMeasureLaws MN (FreeOmega MN) NI
      (FreeOmegaSemanticMeasure (NI := NI))
      FreeOmegaMixedMeasure.
Proof.
  constructor.
  - intros A B mu k h Hae.
    eapply FOLSample with (S := fun x y => x = y /\
      free_omega_lift eq (k x) (h x)).
    + exact (sem_lift_refl_ae Hae).
    + intros x y [-> Hxy]. exact Hxy.
  - intros A B C mu k h.
    apply free_omega_lift_refl. intros x. reflexivity.
  - intros A B C D R T mu nu k h Hmn Hkh.
    eapply FOLSample with (S := R); eauto.
Qed.

(** The free completion has a canonical formal lub.  [sem_total] is kept
    explicit and conservative: totality certificates for analytic limits
    belong to an observable interpretation, not to the syntax alone. *)
#[local] Polymorphic Instance FreeOmegaSemanticOmega :
    forall `{NO : @SemanticOmega MN NI},
    @SemanticOmega (FreeOmega MN)
      (FreeOmegaSemanticMeasure (NI := NI)).
Proof.
  intros NO. refine {| sem_zero := @FOZero MN;
    sem_le := fun A => @free_omega_approx MN NI A A eq;
    sem_lub := fun A chain out =>
      @sem_eq (FreeOmega MN)
        (FreeOmegaSemanticMeasure (NI := NI)) A
        out (FOLub chain);
    sem_total := fun A mu => exists (O : Type) (obs : A -> O) (out : MN O),
      free_omega_observes obs mu out /\ sem_total out |}.
Defined.

(** The old syntactic-total design would accept only [FORet].  Observable
    totality instead permits a formal omega limit exactly when it denotes a
    total low-universe node distribution. *)

#[local] Polymorphic Instance FreeOmegaSemanticOmegaLaws :
    forall `{NO : @SemanticOmega MN NI},
    @SemanticOmegaLaws (FreeOmega MN)
      (FreeOmegaSemanticMeasure (NI := NI))
      (FreeOmegaSemanticOmega (NO := NO)).
Proof.
  intros NO. constructor.
  - intros A chain _. exists (FOLub chain).
    apply free_omega_lift_refl. intros x. reflexivity.
  - intros A chain mu nu Hmu Hnu.
    eapply sem_eq_trans; [exact Hmu|].
    eapply sem_eq_sym. exact Hnu.
  - intros A chain chain' mu nu Hcc Hmu Hnu.
    eapply sem_eq_trans; [exact Hmu|].
    eapply sem_eq_trans.
    + apply FOLLub. exact Hcc.
    + eapply sem_eq_sym. exact Hnu.
  - intros A chain chain' mu Hcc Hmu.
    eapply sem_eq_trans; [exact Hmu|].
    apply FOLLub. exact Hcc.
  - intros A B chain mu k _ Hmu.
    cbn in Hmu |- *.
    change (free_omega_lift eq (free_omega_bind mu k)
      (free_omega_bind (FOLub chain) k)).
    eapply free_omega_lift_bind with (R := eq) (T := eq);
      [exact Hmu|].
    intros x y ->. apply free_omega_lift_refl.
    intros z. reflexivity.
Qed.

#[local] Polymorphic Instance FreeOmegaSemanticMeasureOrderLaws :
    forall `{NO : @SemanticOmega MN NI},
    @SemanticMeasureOrderLaws (FreeOmega MN)
      (FreeOmegaSemanticMeasure (NI := NI))
      (FreeOmegaSemanticOmega (NO := NO)).
Proof.
  intros NO. constructor.
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

End FreeOmegaLaws.
