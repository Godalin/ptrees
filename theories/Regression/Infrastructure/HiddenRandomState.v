Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From Coq Require Import Program.Equality.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg rat.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum
  RatSubTypes DiscreteMC FrontierLiftEnum FreeOmegaMeasure FreeOmegaCoupling.
From PTree.Eq Require Import PrimitiveStableHitting.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import FiniteInternal UnifiedFrontier PTreeKernel.
From PTree.Eq.FreeOmega Require Import KernelCompletion KernelProjection
  FiniteInternalAcceleration FiniteInternalProjectedPolicy.
From PTree.Regression.Backend Require Import EnumMeasureRegression SubEnumRegression.
From PTree.Regression.Infrastructure Require Import CouplingReferences.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Add a fresh, unobserved random component to EVERY internal successor
    of an arbitrary kernel.  Projection removes it even across unbounded
    execution; this is not a finite-prefix or AST-only statement. *)
Section Instrumentation.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI} {X Y S O : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Variable hidden : MN X.
Variable point : Y.
Hypothesis hidden_mass : sem_same_mass hidden (sem_ret point).
Hypothesis point_ae : forall P, sem_ae (sem_ret point) P <-> P point.
Variable base : S -> MF (stable_target S O).

Definition add_random_state (z : stable_target S O) : MF (stable_target (S * X) O) :=
  match z with
  | SHStable o => FORet (SHStable o)
  | SHInternal s => FOSample hidden (fun x => FORet (SHInternal (s,x)))
  end.
Definition random_state_kernel (p : S * X) := free_omega_bind (base (fst p)) add_random_state.

Lemma random_state_target_marginal z :
  free_omega_qlift
    (fun w v => kernel_target_projection (@fst S X) (fun o : O => o) w = v)
    (add_random_state z) (FORet z).
Proof.
  destruct z as [o|s].
  - apply FOQLStructural, FOLRet. reflexivity.
  - eapply free_omega_sample_to_constant with (point := point).
    + exact point_ae.
    + exact hidden_mass.
    + intro x. apply FOQLStructural, FOLRet. reflexivity.
Qed.

Lemma random_state_kernel_marginal p :
  free_omega_qlift
    (fun w v => kernel_target_projection (@fst S X) (fun o : O => o) w = v)
    (random_state_kernel p) (base (fst p)).
Proof.
  eapply FOQLComp with
    (T := fun w v => kernel_target_projection (@fst S X) (fun o : O => o) w = v)
    (U := eq) (mid := free_omega_bind (base (fst p)) (fun z => FORet z)).
  - eapply FOQLBind with (T := eq).
    + apply free_omega_qlift_refl. intro z. reflexivity.
    + intros z w ->. apply random_state_target_marginal.
  - apply FOQLStructural, free_omega_bind_return_lift.
  - intros w v [z [Hw ->]]. exact Hw.
Qed.

Theorem random_state_complete_hitting s x out1 out2 :
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega
    (S * X) O random_state_kernel (s,x) out1 ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O base s out2 ->
  free_omega_qlift eq out1 out2.
Proof.
  intros Hleft Hright.
  assert (Hproject : free_omega_qlift eq
    (free_omega_bind out1 (fun o => FORet o)) out2).
  { eapply kernel_stable_hitting_projection with
      (source := random_state_kernel) (target := base)
      (state_projection := @fst S X) (output_projection := fun o : O => o)
      (D := fun _ => True) (s := (s,x)).
    - intros p _. eapply free_omega_ae_mono with (P := fun _ => True).
      + intros [o|q] _; exact I.
      + apply (@sem_ae_true MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
    - intros p _. apply random_state_kernel_marginal.
    - exact I.
    - exact Hleft.
    - exact Hright. }
  eapply FOQLComp with (T := eq) (U := eq); [|exact Hproject|].
  - apply FOQLMono with (T := fun x y => y = x).
    + apply FOQLSym, FOQLStructural, free_omega_bind_return_lift.
    + intros a b Heq. symmetry. exact Heq.
  - intros a c [b [-> ->]]. reflexivity.
Qed.

End Instrumentation.

Import Enum RatSubTypes GRing.Theory.
#[local] Open Scope ring_scope.

(** A concrete nondegenerate sample discharges the TOTAL-MASS premise.
    Support alone would not justify forgetting a subprobability sample. *)
Example fair_hidden_state_preserves_hitting {S O}
    (base : S -> FreeOmega SubEnum (stable_target S O)) s b out1 out2 :
  @stable_hitting (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    FreeOmegaObservableSemanticOmega (S * bool) O
    (random_state_kernel subenum_fair base) (s,b) out1 ->
  @stable_hitting (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    FreeOmegaObservableSemanticOmega S O base s out2 ->
  free_omega_qlift eq out1 out2.
Proof.
  apply random_state_complete_hitting with (point := false).
  - exact fair_discard_same_mass.
  - intro P. apply (@sem_ae_ret_iff SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureDiracAELaws).
Qed.

Section CompressedPrograms.
Context {E : Type -> Type} {A : Type}.
Local Notation tree := (ptree E SubEnum A).
Local Notation head := (stable_head E SubEnum A).
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Variable policy : tree -> MF tree.
Hypothesis policy_valid : forall t,
  @finite_internal E SubEnum MF FI FreeOmegaMixedMeasure A t (policy t).

(** Fresh hidden coins are added after arbitrary well-founded cuts, in
    every subsequent round too.  Their sampled bits remain in the joint
    state.  Adequacy uses quotient projection, without a structural
    reference, joint extraction assumption, AST, or uniform cut bound. *)
Example fair_hidden_compressed_hitting t b out original :
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega (tree * bool) head
    (random_state_kernel subenum_fair (finite_internal_round_kernel policy)) (t,b) out ->
  @ptree_stable_hitting E SubEnum MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A (observe t) original ->
  free_omega_qlift eq (free_omega_bind out (fun h => FORet h)) original.
Proof.
  intros Hout Horiginal.
  eapply finite_internal_projected_policy_adequate with
    (kernel := random_state_kernel subenum_fair (finite_internal_round_kernel policy))
    (project_state := @fst tree bool) (project_output := fun h : head => h)
    (policy := policy) (D := fun _ => True) (s := (t,b)).
  - exact policy_valid.
  - intros p _. eapply free_omega_ae_mono with (P := fun _ => True).
    + intros [h|q] _; exact I.
    + apply (@sem_ae_true MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
  - intros p _. exact (@random_state_kernel_marginal SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureCoreLaws SubEnum_SemanticOmega bool bool tree head
      subenum_fair false fair_discard_same_mass
      (fun P => @sem_ae_ret_iff SubEnum SubEnum_SemanticMeasure
        SubEnum_SemanticMeasureDiracAELaws bool false P)
      (finite_internal_round_kernel policy) p).
  - exact I.
  - exact Hout.
  - exact Horiginal.
Qed.

End CompressedPrograms.

(** This marginal really lies outside the previous reference method.
    The base takes one deterministic internal step and then returns;
    instrumentation stores a fair bit at that intermediate state. *)
Definition delayed_return_kernel (state : bool) : FreeOmega SubEnum (stable_target bool bool) :=
  if state then FORet (SHInternal false) else FORet (SHStable false).

Example hidden_step_has_no_structural_reference :
  ~ exists reference : FreeOmega SubEnum (stable_target (bool * bool) bool),
    free_omega_qlift eq
      (random_state_kernel subenum_fair delayed_return_kernel (true,false)) reference /\
    free_omega_lift
      (fun z target => kernel_target_projection (@fst bool bool) (fun b : bool => b) z = target)
      reference (delayed_return_kernel true).
Proof.
  intros [reference [Heq Hmarginal]].
  assert (Hself : free_omega_lift eq
    (random_state_kernel subenum_fair delayed_return_kernel (true,false))
    (random_state_kernel subenum_fair delayed_return_kernel (true,false))).
  { apply free_omega_lift_refl. intro z. reflexivity. }
  pose proof (free_omega_reference_marginals_ret_deterministic
    (project_left := fun z : stable_target (bool * bool) bool => z)
    Heq Hself Hmarginal)
    as Hconstant.
  destruct Hconstant as [z Hae]. apply free_omega_ae_sample_inv in Hae.
  destruct (CorrelatedSampleAlgebra.exchange_fair_both_values Hae) as [Htrue Hfalse].
  dependent destruction Htrue; dependent destruction Hfalse.
Qed.

(** A missing-mass sample cannot be silently treated as unobservable
    total noise.  The mass premise of the projection example rejects it. *)
Example zero_hidden_sample_rejected :
  ~ @sem_same_mass SubEnum SubEnum_SemanticMeasure bool bool
      subenum_zero (subenum_ret false).
Proof.
  intro Hmass.
  assert (Hzero : @sem_ae SubEnum SubEnum_SemanticMeasure bool subenum_zero
    (fun _ => False)).
  { intros p x Hempty. contradiction. }
  pose proof (sem_lift_ae_transport_r Hmass Hzero) as Hret.
  apply (proj1 (@sem_ae_ret_iff SubEnum SubEnum_SemanticMeasure
    SubEnum_SemanticMeasureDiracAELaws bool false
    (fun y => exists x : bool, True /\ False))) in Hret.
  destruct Hret as [x [_ Hfalse]]. exact Hfalse.
Qed.
