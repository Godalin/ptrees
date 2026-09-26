(** Full-program calculation. Only the two unbounded sampler analyses are
    opaque: VN -> fair, and the standard binary loop -> Bernoulli(q).
    Everything between them is a visible program-algebra rewrite, inside
    the SAME infinite controller and the SAME stack of effect handlers. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat.
From ITree.Events Require Import State Exception.
From PTree Require Import PTreeFacts.
From PTree.Prob.Backend.EnumQ Require Import Representation Measure Bind.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Interp.FreeOmega Require Import Rewriting.
Import FreeOmegaRewriting.
From PTree.Examples.BernoulliFactory Require Import
  BernoulliFactory BernoulliFactoryComposition OperationalBernoulliFactory
  VonNeumannUnbounded RationalBernoulli.
From PTree.Examples.FactoryController Require Import Controller Scripted Facts.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Set Default Timeout 20.

(** Select the observable interpretation explicitly. This is notation for
    the raw generic relation, not a second relation or a canonical wrapper. *)
Local Notation W :=
  (PEutt.peutt (MN := EnumQ) (MF := FreeOmega EnumQ)
    (FI := @FreeOmegaObservableSemanticMeasure EnumQ EnumQ_SemanticMeasure EnumQ_SemanticOmega)
    (FC := @FreeOmegaObservableSemanticMeasureCoreLaws EnumQ EnumQ_SemanticMeasure EnumQ_SemanticMeasureCoreLaws EnumQ_SemanticOmega)
    (MX := @StructuralMeasure.FreeOmegaMixedMeasure EnumQ)
    (FO := @FreeOmegaObservableSemanticOmega EnumQ EnumQ_SemanticMeasure EnumQ_SemanticOmega)).
Local Notation "t ≈ₚ u" := (W eq t u)
  (at level 70, no associativity) : type_scope.

Section FullProgram.
Variables pfalse ptrue q : rat.
Variables (pfpos : 0 < pfalse) (ptpos : 0 < ptrue) (q0 : 0 <= q) (q1 : q <= 1).
Hypothesis pnorm : pfalse + ptrue = 1.
Let pf0 : 0 <= pfalse := ltW pfpos.
Let pt0 : 0 <= ptrue := ltW ptpos.
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
  setoid_rewrite (peutt_factory_vn_fair pf0 pt0 pnorm (mulr_gt0 pfpos ptpos)).
  change (Run (factory_with_sampler factory_direct_fair q) ≈ₚ
    Run (factory_direct_q q0 q1)).

  (* 2. Open the outer factory loop; distribute bind through sampling,
        eliminate Ret, and combine the finite sampling/return step. *)
  unfold factory_with_sampler, factory_sampler_step, factory_direct_fair.
  setoid_rewrite (peutt_sample_bind vn_fair).
  setoid_rewrite (peutt_sample_map vn_fair).
  assert (Hround : forall x,
    Prob (bind_EnumQ vn_fair (fun b => ret_EnumQ (binary_round_result x b)))
      (fun a => Ret a) ≈ₚ factory_standard_step x).
  { intro x. unfold factory_standard_step.
    rewrite fair_binary_round_measure. reflexivity. }
  setoid_rewrite Hround.

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
  have pfpos : 0 < vn_one_third by vm_compute; reflexivity.
  have ptpos : 0 < vn_two_thirds by vm_compute; reflexivity.
  (* The extracted program keeps its original nonnegativity certificates.
     Boolean proof uniqueness aligns these with the derived certificates. *)
  replace third_false_nonnegative with (ltW pfpos) by apply bool_irrelevance.
  replace third_true_nonnegative with (ltW ptpos) by apply bool_irrelevance.
  apply factory_controller_program_rewrite.
  exact third_bias_normalized.
Qed.
