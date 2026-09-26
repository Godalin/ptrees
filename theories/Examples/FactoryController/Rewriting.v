(** Full-program calculation. Only the two unbounded sampler analyses are
    opaque: VN -> fair, and the standard binary loop -> Bernoulli(q).
    Everything between them is a visible program-algebra rewrite, inside
    the SAME infinite controller and the SAME stack of effect handlers. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From ITree.Events Require Import State Exception.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import EnumQ.
From PTree.Prob.Backend.EnumQ Require Import Representation Measure Bind.
From PTree.Prob.Interface Require Import Measure Mixed.
From PTree.Prob.FreeOmega Require Import RelationalLimit StructuralMeasure.
Require Import PTree.Prob.FreeOmega.Measure.
From PTree.Interp Require Import IterationUniform ExceptionFacts Unrestricted StatePreservation.
From PTree.Examples.BernoulliFactory Require Import
  BernoulliFactory BernoulliFactoryComposition OperationalBernoulliFactory
  VonNeumannUnbounded RationalBernoulli.
From PTree.Examples.FactoryController Require Import Controller Scripted Facts.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Set Default Timeout 20.

(** Only local registration: the generic library owns these congruences.
    The three program-specific contexts belong to their example owners. *)
#[local] Existing Instance embed_Proper.
#[local] Existing Instance factory_with_sampler_Proper.
#[local] Existing Instance controller_Proper.

#[local] Instance state_rewrite {S E A} :
  Proper (canonical_peutt eq ==> eq ==> canonical_peutt eq)
    (@run_state S E EnumQ A) :=
  run_state_peutt_eq_Proper free_omega_relational_bind
    free_omega_relational_zero free_omega_relational_lub.

#[local] Instance interp_rewrite {E F A} (h : forall X, E X -> ptree F EnumQ X) :
  Proper (canonical_peutt eq ==> canonical_peutt eq)
    (PTree.interp h : ptree E EnumQ A -> ptree F EnumQ A) :=
  peutt_interp_Proper free_omega_relational_zero free_omega_relational_lub h.

#[local] Instance exception_rewrite {Err E A} :
  Proper (canonical_peutt eq ==> canonical_peutt eq) (@run_exception Err E EnumQ A) :=
  run_exception_peutt_eq_Proper free_omega_relational_bind.

#[local] Instance iter_rewrite {E I A} :
  Proper (pointwise_relation I (canonical_peutt eq) ==> eq ==> canonical_peutt eq)
    (@PTree.iter E EnumQ A I) :=
  peutt_iter_Proper free_omega_relational_zero free_omega_relational_lub.

Section FullProgram.
Variables pfalse ptrue q : rat.
Variables (pf0 : 0 <= pfalse) (pt0 : 0 <= ptrue) (q0 : 0 <= q) (q1 : q <= 1).
Hypotheses (pnorm : pfalse + ptrue = 1) (pnontrivial : 0 < pfalse * ptrue).
Variables (pc : phase) (counts : counters) (script : script_state).

(** A notation, not a new interpreter or an opaque refinement wrapper.
    Every rewrite below acts under ALL these unchanged program contexts. *)
Local Notation "'Run' sampler" :=
  (run_exception
    (run_state
      (PTree.interp device_handler
        (run_state (controller (embed sampler) pc) counts)) script))
  (at level 10, sampler at next level).

Theorem factory_controller_program_rewrite :
  Run (biased_to_rational_coin pf0 pt0 q) ≈ₚ Run (factory_direct_q q0 q1).
Proof.
  unfold biased_to_rational_coin.
  (* 1. Run[Controller[Factory(VN(p),q)]]
        -> Run[Controller[Factory(Fair,q)]].
        First and only VN probability-analysis lemma. *)
  setoid_rewrite (peutt_factory_vn_fair pf0 pt0 pnorm pnontrivial).
  change (Run (factory_with_sampler factory_direct_fair q) ≈ₚ
    Run (factory_direct_q q0 q1)).

  (* 2. Open the outer factory loop; distribute bind through sampling,
        eliminate Ret, and combine the finite sampling/return step. *)
  unfold factory_with_sampler, factory_sampler_step, factory_direct_fair.
  setoid_rewrite (peutt_sample_bind (E := factoryE)
    (NI := EnumQ_SemanticMeasure) (FI := FreeOmegaObservableSemanticMeasure) vn_fair).
  setoid_rewrite (peutt_sample_map (E := factoryE)
    (NI := EnumQ_SemanticMeasure) (FI := FreeOmegaObservableSemanticMeasure) vn_fair).
  assert (Hround :
    (fun x => (Prob (bind_EnumQ vn_fair (fun b => ret_EnumQ (binary_round_result x b)))
      (fun a => Ret a) : ptree factoryE EnumQ (rat + bool))) = factory_standard_step).
  { apply functional_extensionality. intro x. unfold factory_standard_step.
    rewrite fair_binary_round_measure. reflexivity. }
  rewrite Hround.

  (* 3. The residual program is the standard binary loop, still INSIDE
        the controller, both State handlers, device interp and exception. *)
  change (Run (factory_standard q) ≈ₚ Run (factory_direct_q q0 q1)).
  (* Second probability-analysis lemma: the unbounded binary loop's law. *)
  setoid_rewrite (peutt_factory_standard_direct q0 q1).
  reflexivity.
Qed.
End FullProgram.

(** This is the actual pair of closed programs used by OCaml extraction. *)
Corollary scripted_controller_program_rewrite counts script :
  scripted_impl counts script ≈ₚ scripted_spec counts script.
Proof.
  unfold scripted_impl, scripted_spec, close_controller,
    device_controller_impl, device_controller_spec, controller_impl, controller_spec,
    implementation_sampler, specification_sampler, third_to_two_fifths, direct_two_fifths.
  apply factory_controller_program_rewrite.
  - exact third_bias_normalized.
  - exact third_bias_nontrivial.
Qed.
