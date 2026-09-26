(** User-facing algebra: probability is proved once in the existing factory,
    then transported through bind, eventful iteration and State. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import EnumQ.
From PTree.Prob.FreeOmega Require Import RelationalLimit.
From PTree.Interp Require Import IterationUniform.
From PTree.Interp Require Import ExceptionFacts.
From PTree.Interp.FreeOmega Require Import Unrestricted State.
From PTree.Examples.BernoulliFactory Require Import BernoulliFactory BernoulliFactoryComposition.
From PTree.Examples.FactoryController Require Import Controller.
From PTree.Examples.FactoryController Require Import Scripted.
Set Implicit Arguments.
Unset Strict Implicit.
Set Default Timeout 20.

Lemma embed_preserves {E A} (t u : ptree factoryE EnumQ A) :
  t ≈ₚ u -> @embed E A t ≈ₚ embed u.
Proof. apply peutt_interp. Qed.

Theorem implementation_sampler_correct : implementation_sampler ≈ₚ specification_sampler.
Proof. apply embed_preserves. exact peutt_third_to_two_fifths_compositional. Qed.

#[local] Instance attempt_Proper job :
  Proper (canonical_peutt eq ==> canonical_peutt eq) (fun sampler => attempt sampler job).
Proof.
  intros s t H. unfold attempt. eapply peutt_bind; [exact H|].
  intros x y ->. reflexivity.
Qed.

Lemma controller_step_congr s t : s ≈ₚ t -> forall pc,
  controller_step s pc ≈ₚ controller_step t pc.
Proof. intros H [|job]; cbn [controller_step]; [reflexivity|]. now apply attempt_Proper. Qed.

Theorem controller_congr s t : s ≈ₚ t -> forall pc,
  controller s pc ≈ₚ controller t pc.
Proof.
  intros H pc. unfold controller.
  eapply (peutt_iter_direct_rel free_omega_relational_zero free_omega_relational_lub)
    with (SI := eq).
  - intros x y ->. eapply peutt_rel_mono.
    + intros v w ->. destruct w; constructor; reflexivity.
    + apply controller_step_congr. exact H.
  - reflexivity.
Qed.

#[local] Instance controller_Proper :
  Proper (canonical_peutt eq ==> eq ==> canonical_peutt eq) controller.
Proof. intros s t H pc pc' ->. now apply controller_congr. Qed.

(** Main source theorem: no whole-controller coupling or coinduction. *)
Theorem controller_refinement : controller_impl ≈ₚ controller_spec.
Proof.
  unfold controller_impl, controller_spec.
  setoid_rewrite implementation_sampler_correct. reflexivity.
Qed.

Theorem state_controller_refinement s : device_controller_impl s ≈ₚ device_controller_spec s.
Proof. apply run_state_peutt_eq. exact controller_refinement. Qed.

(** Any device interpretation, not only the scripted demo, preserves the
    source refinement. No liveness assumption about device responses. *)
Theorem device_handler_refinement {F} (h : forall X, deviceE X -> ptree F EnumQ X) s :
  PTree.interp h (device_controller_impl s) ≈ₚ
  PTree.interp h (device_controller_spec s).
Proof. apply peutt_interp. apply state_controller_refinement. Qed.

Theorem scripted_controller_refinement counts script :
  scripted_impl counts script ≈ₚ scripted_spec counts script.
Proof.
  unfold scripted_impl, scripted_spec, close_controller.
  eapply peutt_rel_mono with (RR := Exception.exception_result_rel eq).
  - intros [x|x] [y|y] H; cbn in H; try contradiction; now subst.
  - apply (run_exception_peutt free_omega_relational_bind).
    apply run_state_peutt_eq. apply device_handler_refinement.
Qed.

(** The user-facing transformation is not restricted to the demo's 2/5.
    Source weights are nonnegative, normalized and nondegenerate. *)
Section RationalParameters.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Variables pfalse ptrue q : rat.
Variables (pf0 : 0 <= pfalse) (pt0 : 0 <= ptrue) (q0 : 0 <= q) (q1 : q <= 1).
Hypotheses (pnorm : pfalse + ptrue = 1) (pnontrivial : 0 < pfalse * ptrue).
Theorem rational_controller_refinement pc :
  controller (embed (biased_to_rational_coin pf0 pt0 q)) pc ≈ₚ
  controller (embed (factory_direct_q q0 q1)) pc.
Proof.
  apply controller_congr, embed_preserves.
  exact (peutt_factory_vn_direct q0 q1 pf0 pt0 pnorm pnontrivial).
Qed.
End RationalParameters.
