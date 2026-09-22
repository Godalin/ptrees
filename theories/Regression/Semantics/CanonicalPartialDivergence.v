(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
(** Keep the zero query in the behavior carrier's universe, rather than
    minimizing its otherwise unconstrained [FOZero] representation to Set. *)
Local Unset Universe Minimization ToSet.

From Coq.Program Require Import Equality.
From mathcomp Require Import ssreflect ssrbool ssrnat seq ssralg ssrnum rat reals.
From mathcomp.analysis Require Import ereal.
From mathcomp.reals_stdlib Require Import Rstruct.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.FrontierLift PTree.Prob.Backend.EnumQ.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.EnumQ.FreeOmega.UpperExpectation PTree.Prob.Backend.EnumQ.FreeOmega.UpperQuotient.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier PTreeKernel PEutt ProbabilisticTrace.
From PTree.Regression.Backend Require Import EnumQMeasureRegression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Native samples remain EnumQ. Complete heads belong to FreeOmega EnumQ,
    not to the same monomorphic native EnumQ universe. In particular these
    missing-mass tests must coexist with arbitrary sampled continuations. *)
Local Notation MF := (FreeOmega EnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := EnumQ_SemanticMeasure) (NC := EnumQ_SemanticMeasureCoreLaws)
  (NO := EnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega)).
Local Notation K := (@ptree_primitive_kernel regE EnumQ MF FI
  FreeOmegaMixedMeasure bool).
Local Notation hits t out := (@stable_hitting MF FI FO _ _ K (observe t) out).
Local Notation W := (@peutt regE EnumQ MF FI FC
  FreeOmegaMixedMeasure FO bool bool eq).
Local Notation scalar := (@Real.Pack Rdefinitions.R (Real.on Rdefinitions.R)).

CoFixpoint canonical_spin : ptree regE EnumQ bool := Tau canonical_spin.

Lemma observe_canonical_spin :
  observe canonical_spin = TauF canonical_spin.
Proof. reflexivity. Qed.

Definition half_return_half_diverge : ptree regE EnumQ bool :=
  Prob reg_fair (fun b => if b then Ret true else canonical_spin).

Definition half_return_heads : MF (stable_head regE EnumQ bool) :=
  FOSample reg_fair (fun b => if b then FORet (FHRet true) else FOZero).

Lemma canonical_spin_target_approx_zero fuel :
  @stable_target_approx MF FI FO _ _ K fuel
    (SHInternal (observe canonical_spin)) = FOZero.
Proof.
  induction fuel as [|fuel IH]; [reflexivity|].
  change (@stable_target_approx MF FI FO _ _ K fuel
    (SHInternal (observe canonical_spin)) = FOZero).
  exact IH.
Qed.

Lemma canonical_spin_hitting_approx_zero fuel :
  @stable_hitting_approx MF FI FO _ _ K fuel
    (observe canonical_spin) = FOZero.
Proof. exact (canonical_spin_target_approx_zero fuel). Qed.

Lemma canonical_spin_stable_hitting_zero : hits canonical_spin FOZero.
Proof.
  unfold stable_hitting.
  eapply (sem_lub_chain_proper (SI := FI) (SO := FO))
    with (chain := fun _ => FOZero).
  - intro n. rewrite canonical_spin_hitting_approx_zero.
    apply sem_eq_refl.
  - apply sem_lub_constant.
Qed.

Definition impossible_trace_step {X} (e : regE X) : option X :=
  match e with end.
Definition divergent_one_event_trace : @finite_interaction_pattern regE :=
  cons (@impossible_trace_step) nil.
Definition divergent_trace_query : MF bool := FOZero.

Lemma canonical_spin_nonempty_trace_query_zero :
  @finite_interaction_query regE EnumQ MF FI FreeOmegaMixedMeasure FO bool
    divergent_one_event_trace canonical_spin divergent_trace_query.
Proof.
  exists FOZero, (fun _ : stable_head regE EnumQ bool => FOZero).
  repeat split.
  - exact canonical_spin_stable_hitting_zero.
  - apply FOAEZero.
  - apply free_omega_qlift_refl. intro b. reflexivity.
Qed.

Lemma divergent_trace_query_mass_zero :
  exists out : EnumQ bool,
    @free_omega_observes EnumQ EnumQ_SemanticMeasure EnumQ_SemanticOmega
      bool bool (fun b => b) divergent_trace_query out /\
    enumQ_expect (fun _ : bool => (1 : rat)) out = 0.
Proof. exists [::]. split; [constructor|reflexivity]. Qed.

Lemma divergent_trace_query_not_rejection_mass :
  ~ @sem_same_mass MF FI bool bool divergent_trace_query (FORet false).
Proof.
  intro Hmass.
  pose proof ((proj1 (free_omega_qlift_support Hmass)) (fun _ => False)
    (FOAEZero _)) as Hbad.
  dependent destruction Hbad.
  destruct H as [x [_ Hfalse]]. exact Hfalse.
Qed.

Lemma enumQ_ret_true_stable_hitting : hits (Ret true) (FORet (FHRet true)).
Proof. apply (stable_hitting_ret (FI := FI) (FO := FO)). Qed.

Lemma half_return_half_diverge_stable_hitting :
  hits half_return_half_diverge half_return_heads.
Proof.
  unfold half_return_half_diverge, half_return_heads.
  apply (stable_hitting_prob (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros [] _; [exact enumQ_ret_true_stable_hitting|exact canonical_spin_stable_hitting_zero].
Qed.

(** Scalar soundness of the observable quotient separates mass 1/2 from
    mass 1. This is the proved backend model, not a new mass/reflection axiom.
    The standard-real instance is the same one used by native recovery. *)
Lemma half_return_heads_not_same_mass_ret :
  ~ @sem_same_mass MF FI
      (stable_head regE EnumQ bool) (stable_head regE EnumQ bool)
      half_return_heads (FORet (FHRet true)).
Proof.
  intro Hmass.
  have Hweight := free_omega_qlift_extended_upper_mass scalar Hmass.
  change (enumQ_extended_expect (R := scalar)
    (fun b : bool => if b then 1 else 0) reg_fair = 1)%E in Hweight.
  cbn [enumQ_extended_expect reg_fair] in Hweight.
  rewrite !reg_half_val mule0 mule1 !adde0 in Hweight.
  have Hone : (1 : \bar scalar)%E = (ratr (1 : rat) : scalar)%:E by rewrite rmorph1.
  rewrite Hone in Hweight. injection Hweight as Hrat.
  rewrite add0r in Hrat.
  have Hbad := fmorph_inj (ratr : {rmorphism rat -> scalar}) Hrat.
  move: Hbad. native_compute. discriminate.
Qed.

Theorem half_return_half_diverge_not_peutt_ret :
  ~ W half_return_half_diverge (Ret true).
Proof.
  intro Hrel.
  have Hlift := peutt_hitting_lift (FI := FI) (FC := FC) (FO := FO)
    (FOL := FreeOmegaObservableSemanticOmegaLaws
      (NC := EnumQ_SemanticMeasureCoreLaws)) Hrel
    half_return_half_diverge_stable_hitting enumQ_ret_true_stable_hitting.
  apply half_return_heads_not_same_mass_ret.
  exact (sem_lift_same_mass Hlift).
Qed.

From Coq.Program Require Import Equality.
From Coq.Classes Require Import RelationClasses.
From Coq.Relations Require Import Relation_Operators.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import PEutt PTreeKernel PrimitiveStableHitting UnifiedFrontier.
Module HittingDivergenceTests.
(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Complete stable hitting distinguishes silent divergence from return.
    This sanity check is independent of any finite-compression relation. *)
Variant closure_event : Type -> Type := .
Local Notation tree := (ptree closure_event SubEnumQ bool).
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation hit := (@ptree_hitting_approx closure_event SubEnumQ MF FI
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool).
Local Notation PE := (@peutt closure_event SubEnumQ MF FI
  FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
  FreeOmegaObservableSemanticOmega bool bool eq).

CoFixpoint closure_spin : tree := Tau closure_spin.
Definition closure_return : tree := Ret true.
Definition closure_delayed : tree := Tau closure_return.

Lemma closure_spin_approx_zero n : hit n (observe closure_spin) = FOZero.
Proof.
  induction n as [|n IH]; [reflexivity|].
  change (hit n (observe closure_spin) = FOZero). exact IH.
Qed.

Lemma closure_spin_not_peutt_return : ~ PE closure_spin closure_return.
Proof.
  intro Hpeutt.
  pose (out := FOLub (fun n => hit n (observe closure_spin))).
  assert (Hspin : @ptree_stable_hitting closure_event SubEnumQ MF FI
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool
    (observe closure_spin) out).
  { apply free_omega_qlift_refl. intro h. reflexivity. }
  assert (Hret : @ptree_stable_hitting closure_event SubEnumQ MF FI
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool
    (observe closure_return) (FORet (FHRet true))).
  { exact (@stable_hitting_ret closure_event SubEnumQ MF
      FI FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaObservableSemanticMeasureBindLaws
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega FreeOmegaObservableSemanticOmegaLaws
      FreeOmegaObservableSemanticOmegaCofinalityLaws bool true). }
  pose proof (peutt_hitting_lift Hpeutt Hspin Hret) as Hlift.
  pose proof (proj1 (free_omega_qlift_support Hlift)) as Hsupport.
  assert (Hempty : free_omega_ae (fun _ => False) out).
  { apply FOAELub. intro n. rewrite closure_spin_approx_zero. apply FOAEZero. }
  specialize (Hsupport _ Hempty). dependent destruction Hsupport.
  destruct H as [x [_ Hfalse]]. exact Hfalse.
Qed.

End HittingDivergenceTests.
