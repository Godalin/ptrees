Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Lia.
From PTree.Prob Require Import TwoLevelMeasure SemanticCoupling FreeOmegaMeasure.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import FreeOmegaNative.
From PTree.Eq Require Import FiniteInternalPlan PFiniteResidual PStrong.
From PTree.Eq.FreeOmega Require Import FiniteInternalNative.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NecessaryLaw.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}.

(** Even IDENTITY decoders force a native relational left-unit law.
    This is a necessary condition, not a sufficient reflection package. *)
Theorem native_reflection_requires_left_unit {A B}
    (reflect : forall mu nu : MN B,
      free_omega_qlift eq (FOSample mu (fun y => FORet y))
        (FOSample nu (fun y => FORet y)) -> sem_lift eq mu nu)
    (x : A) (k : A -> MN B) :
  sem_lift eq (sem_bind (sem_ret x) k) (k x).
Proof. apply reflect, free_omega_sample_bind_ret_l. Qed.
End NecessaryLaw.

(** Audit of a proposed proof route, NOT a counterexample to pfinite
    soundness or to a maintained probability backend.

    Think of Some (n,x) as a Dirac with mass 2^(-n), and None as zero.
    The deliberately faulty bind loses another factor 1/2.  Core coupling,
    Dirac AE, exact bind AE, countable AE, and actual native joints all
    still hold.  Hence those capabilities alone cannot reflect FreeOmega
    quotient coupling back into native coupling: SampleBind quotients out
    this bind while SampleRetL quotients out its Dirac input. *)
Module AttenuatedDirac.
Definition M (A : Type) := option (nat * A).
Definition ret {A} (x : A) : M A := Some (0,x).
Definition bind {A B} (mu : M A) (k : A -> M B) : M B :=
  match mu with
  | None => None
  | Some (n,x) => match k x with
    | None => None
    | Some (m,y) => Some (S (n+m),y)
    end
  end.
Definition ae {A} (mu : M A) (P : A -> Prop) :=
  match mu with None => True | Some (_,x) => P x end.
Definition lift {A B} (R : A -> B -> Prop) (mu : M A) (nu : M B) :=
  match mu, nu with
  | None, None => True
  | Some (n,x), Some (m,y) => n = m /\ R x y
  | _, _ => False
  end.

#[local] Instance Measure : SemanticMeasure M := {
  sem_ret := @ret; sem_bind := @bind; sem_eq := fun A => @eq (M A);
  sem_ae := @ae; sem_lift := @lift
}.

#[local] Instance Core : @SemanticMeasureCoreLaws M Measure.
Proof.
  constructor.
  - intros A x. reflexivity.
  - intros A x y H. symmetry. exact H.
  - intros A x y z -> ->. reflexivity.
  - intros A [[n x]|]; cbn; trivial.
  - intros A [[n x]|] P Q HPQ HP; cbn in *; auto.
  - intros A [[n x]|] P Q HP HQ; cbn in *; auto.
  - intros A B R T [[n x]|] [[m y]|] HRT H; cbn in *; firstorder.
  - intros A R [[n x]|] HR; cbn; auto.
  - intros A B R x y H. cbn. auto.
  - intros A B R mu mu' nu -> H. exact H.
  - intros A B R mu nu nu' -> H. exact H.
  - intros A B R [[n x]|] [[m y]|] H; cbn in *; firstorder.
  - intros A B C R T [[n x]|] [[m y]|] [[p z]|] Hxy Hyz;
      cbn in *; try contradiction; try exact I.
    destruct Hxy as [-> Hxy]. destruct Hyz as [-> Hyz].
    split; [reflexivity|]. exists y. auto.
Qed.

#[local] Instance DiracAE : @SemanticMeasureDiracAELaws M Measure.
Proof. constructor. intros A x P. reflexivity. Qed.

#[local] Instance BindAE : @SemanticMeasureBindAEExactLaws M Measure.
Proof.
  constructor. intros A B [[n x]|] k P; cbn; [destruct (k x) as [[m y]|]|];
    reflexivity.
Qed.

#[local] Instance CountableAE : @SemanticMeasureCountableAELaws M Measure.
Proof. constructor. intros A [[n x]|] P H; cbn in *; auto. Qed.

#[local] Instance CouplingAE : @SemanticMeasureCouplingAELaws M Measure.
Proof.
  constructor.
  - intros A B R [[n x]|] [[m y]|] P Hlift HP; cbn in *;
      try contradiction; try exact I.
    exists x. split; [exact (proj2 Hlift)|exact HP].
  - intros A B R [[n x]|] [[m y]|] P Q Hlift HP HQ;
      cbn in *; firstorder.
Qed.

#[local] Instance AELift : @SemanticMeasureAELiftLaws M Measure.
Proof. constructor. intros A [[n x]|] P HP; cbn in *; auto. Qed.

#[local] Instance AEKleisli : @SemanticMeasureAEKleisliLaws M Measure.
Proof.
  constructor.
  - intros A x P HP. exact HP.
  - intros A B mu k P Q Hmu Hk.
    apply (proj2 (@sem_ae_bind_iff M Measure BindAE A B mu k Q)).
    eapply sem_ae_mono; eassumption.
Qed.

#[local] Instance Subprobability : @SemanticSubprobability M Measure := {
  sem_subprob := fun _ _ => True
}.
#[local] Instance SubprobabilityLaws :
    @SemanticSubprobabilityLaws M Measure Subprobability.
Proof. constructor; intros; cbn; tauto. Qed.
#[local] Instance SubprobabilityCarrier :
    @SemanticSubprobabilityCarrierLaws M Measure Subprobability.
Proof. constructor; intros; cbn; tauto. Qed.

Definition le {A} (mu nu : M A) := mu = None \/ mu = nu.
#[local] Instance Omega : @SemanticOmega M Measure := {
  sem_zero := fun _ => None;
  sem_le := @le;
  sem_lub := fun A c out => (forall n, le (c n) out) /\
    (forall upper, (forall n, le (c n) upper) -> le out upper);
  sem_total := fun A mu => exists x : A, mu = Some (0,x)
}.

Lemma native_joints {A B} (R : A -> B -> Prop) (mu : M A) (nu : M B) :
  sem_lift R mu nu -> exists joint, semantic_coupling R mu nu joint.
Proof.
  destruct mu as [[n x]|], nu as [[m y]|]; cbn; intro H; try contradiction.
  - destruct H as [<- H]. exists (Some (n,(x,y))). repeat split; cbn; auto.
  - exists None. repeat split; exact I.
Qed.

Definition sample (mu : M unit) : FreeOmega M unit := FOSample mu (fun x => FORet x).

Lemma quotient_forgets_extra_attenuation :
  free_omega_qlift eq (sample (bind (ret tt) ret)) (sample (ret tt)).
Proof.
  exact (@free_omega_sample_bind_ret_l M Measure Core Omega DiracAE BindAE
    unit unit unit tt (@ret unit) (fun x => FORet x)).
Qed.

Lemma native_coupling_keeps_mass : ~ sem_lift eq (bind (ret tt) ret) (ret tt).
Proof. cbn. intros [H _]. discriminate. Qed.

Theorem quotient_native_reflection_fails :
  ~ (forall mu nu : M unit,
    free_omega_qlift eq (sample mu) (sample nu) -> sem_lift eq mu nu).
Proof.
  intro Hreflect. apply native_coupling_keeps_mass.
  apply Hreflect, quotient_forgets_extra_attenuation.
Qed.

Lemma attenuated_bind_has_no_left_unit :
  ~ @SemanticMeasureBindLaws M Measure.
Proof.
  intro Hbind.
  pose proof (@sem_bind_ret_l M Measure Hbind unit unit tt (@ret unit)) as Hunit.
  discriminate Hunit.
Qed.

(** The failure is present for actual well-founded compression plans,
    not merely for hand-written native presentations.  Both cuts decode
    to the same residual Ret; their path measures have different mass. *)
Definition Event (_ : Type) := Empty_set.
Local Notation tree := (ptree Event M bool).
Definition sampled_plan : finite_internal_plan
    (Prob (ret tt) (fun _ => Ret true) : tree) :=
  FIPProb (ret tt) (fun _ => FIPStop (Ret true)).
Definition direct_plan : finite_internal_plan (Ret true : tree) := FIPStop (Ret true).

Theorem actual_plans_quotient_coupled :
  free_omega_qlift eq (free_omega_native (internal_plan_native sampled_plan))
    (free_omega_native (internal_plan_native direct_plan)).
Proof.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := @internal_plan_frontier Event M bool (FreeOmega M)
      (FreeOmegaObservableSemanticMeasure (NI := Measure) (NO := Omega))
      FreeOmegaMixedMeasure _ sampled_plan).
  - apply FOQLMono with (T := fun x y => y = x).
    + apply FOQLSym, internal_plan_native_eq.
    + intros x y Hyx. symmetry. exact Hyx.
  - eapply FOQLComp with (T := eq) (U := eq) (mid := FORet (Ret true)).
    + apply (@FOQLSampleRetL M Measure Omega); [intro P; reflexivity|].
      apply FOQLStructural, FOLRet. reflexivity.
    + exact (internal_plan_native_eq direct_plan).
    + intros x z [y [-> ->]]. reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

Theorem actual_plans_have_no_native_coupling :
  ~ sem_lift (fun _ _ => True)
    (internal_plan_measure sampled_plan) (internal_plan_measure direct_plan).
Proof. cbn. intros [H _]. discriminate. Qed.

Theorem actual_plans_have_no_native_joint :
  ~ exists joint,
    semantic_coupling (fun _ _ => True)
      (internal_plan_measure sampled_plan) (internal_plan_measure direct_plan) joint.
Proof.
  intros [joint [Hleft [Hright _]]].
  apply actual_plans_have_no_native_coupling.
  eapply sem_lift_mono with (R := fun x z => exists y, fst y = x /\ snd y = z).
  - intros x z _. exact I.
  - eapply sem_lift_comp; [apply sem_lift_sym; exact Hleft|exact Hright].
Qed.

(** This is an actual step of the proposed generator.  Thus the failed
    extraction was not stronger merely because of unrelated endpoints. *)
Theorem actual_plans_are_guard_coupled :
  free_omega_qlift (pfinite_guard eq eq)
    (free_omega_native (internal_plan_native sampled_plan))
    (free_omega_native (internal_plan_native direct_plan)).
Proof.
  eapply FOQLMono with (T := eq); [apply actual_plans_quotient_coupled|].
  intros t u ->. unfold pfinite_guard.
  destruct (observe u).
  - constructor. reflexivity.
  - constructor. reflexivity.
  - constructor. intro x. reflexivity.
  - constructor. apply sem_lift_refl. intro x. reflexivity.
Qed.

Theorem actual_residual_step :
  @pfinite_residualF Event M (FreeOmega M) Measure
    (FreeOmegaObservableSemanticMeasure (NI := Measure) (NO := Omega))
    FreeOmegaMixedMeasure
    bool bool eq eq (Prob (ret tt) (fun _ => Ret true)) (Ret true).
Proof.
  eapply PFiniteResidualStep.
  - apply FiniteInternal.FIProb. intro x. apply FiniteInternal.FIStop.
  - apply FiniteInternal.FIStop.
  - apply (@FOQLSampleRetL M Measure Omega); [intro P; reflexivity|].
    apply FOQLStructural, FOLRet. unfold pfinite_guard. constructor. reflexivity.
Qed.
End AttenuatedDirac.

From mathcomp Require Import reals.
From PTree.Prob Require Import TwoLevelMeasureSubEnum MathCompMeasure TwoLevelMeasureMathComp.

(** Both maintained node backends satisfy the necessary relational
    left-unit law.  For MathComp we use its existing ordinary kernel law,
    NOT the missing full relational SemanticMeasureBindLaws instance.
    These checks do not claim that left-unit alone suffices for reflection. *)
Example subenum_native_relational_left_unit {A B} (x : A) (k : A -> SubEnum B) :
  @sem_lift SubEnum SubEnum_SemanticMeasure B B eq
    (subenum_bind (subenum_ret x) k) (k x).
Proof.
  eapply (@sem_lift_proper_r SubEnum SubEnum_SemanticMeasure
    SubEnum_SemanticMeasureCoreLaws).
  - apply (@sem_bind_ret_l SubEnum SubEnum_SemanticMeasure SubEnum_SemanticMeasureBindLaws).
  - apply sem_lift_refl. intro y. reflexivity.
Qed.

Section MathCompNecessaryLaw.
Context (Real : realType) `{MathCompCouplingGluing Real}.
Example mathcomp_native_relational_left_unit {A B} (x : A)
    (k : A -> MathCompKernelMeasure Real B) :
  @sem_lift (MathCompKernelMeasure Real) (MathCompNodeSemanticMeasure Real) B B eq
    (@mathcomp_kernel_bind Real A B (@mathcomp_kernel_ret Real A x) k) (k x).
Proof.
  eapply (@sem_lift_proper_r (MathCompKernelMeasure Real)
    (MathCompNodeSemanticMeasure Real) (MathCompNodeSemanticMeasureCoreLaws (R := Real))).
  - exact (@mathcomp_kernel_bind_ret_l Real A B x k).
  - apply sem_lift_refl. intro y. reflexivity.
Qed.
End MathCompNecessaryLaw.
