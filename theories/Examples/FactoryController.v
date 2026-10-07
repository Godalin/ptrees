(** Case role: paper case study.
    Reading entry: Rewriting.factory_controller_program_rewrite.
    Scope: SubEnumQ / observable FreeOmega; native bounds are intrinsic.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDIES.md. *)
(** Learn: a complete rewrite calculation through sampler and handler contexts.
    Reusable endpoints: Rewriting.factory_controller_program_rewrite; Observation.factory_next_action_probability.
    Boundary: probability/AST analysis and extracted experiments are separate.
    User navigation: docs/CASE_STUDIES.md. *)
(** Interactive Bernoulli factory: a single, end-to-end case study.

    Reading order:
    1. Controller: the infinite effectful program and its two samplers.
    2. Scripted: State/Exception/device interpretation and executable roots.
    3. Rewriting: the self-contained, full-program algebraic calculation.
    4. Facts: reusable congruences and short refinement corollaries.
    5. Observation: exact next-action distribution and probabilities.

    The internal modules isolate local notation/instances and retain the
    existing qualified declaration names. Tests and the OCaml host remain
    separate; this file does not duplicate the sampler analysis library. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Set Implicit Arguments.
Unset Strict Implicit.
Set Default Timeout 20.
From Coq Require Import List Morphisms FunctionalExtensionality.
From Coq.Program Require Import Equality.
From ITree.Basics Require Import Monad.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat.
From ITree.Events Require Import State Exception.
From ITree.Indexed Require Import Sum.
From PTree Require Import PTreeFacts.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import Shallow ProbabilisticTrace PTreeKernel.
From PTree.Eq.Backend Require Import SubEnumQ ProbabilisticTraceSubEnumQ.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
From PTree.Prob.Backend.EnumQ Require Import Representation Bind.
From PTree.Prob.Backend.SubEnumQ Require Import Representation Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure
  PTree.Prob.FreeOmega.Observation.
From PTree.Prob.FreeOmega Require Import StructuralMeasure RelationalLimit.
From PTree.Interp Require Import State StateFacts Exception ExceptionFacts IterationUniform.
From PTree.Interp.FreeOmega Require Import Base Unrestricted State Rewriting.
From PTree.Examples.BernoulliFactory Require Import
  BernoulliFactory BoundedFactory VonNeumannUnbounded RationalBernoulli.
Import BoundedFactory.

Import MonadNotation SemanticMeasureNotations.
Local Open Scope monad_scope.
Local Open Scope semantic_measure_scope.
Local Open Scope freeomega_scope.
Import HittingNotations.
Local Open Scope hitting_scope.
Local Open Scope subenumQ_probability_scope.

Import EnumQ.

Module Controller.
(** Interactive factory: the existing nested sampler, not a new algorithm.
    Three independent sources of unbounded behavior: VN, binary factory,
    and the reactive service (including environment-driven retries). *)


Inductive machine_reply := Pass | Rework | Jam.
Variant deviceE : Type → Type :=
| ReceiveOrder : deviceE nat
| RunMachine (job : nat) (fast : bool) : deviceE machine_reply
| Ship (job : nat) : deviceE unit
| Alarm (job : nat) : deviceE unit
| WaitReset : deviceE unit.

Record counters := Counters { completed : nat; retries : nat; jams : nat }.
Definition initial_counters := Counters 0 0 0.
Definition count_pass s := Counters (S (completed s)) (retries s) (jams s).
Definition count_rework s := Counters (completed s) (S (retries s)) (jams s).
Definition count_jam s := Counters (completed s) (retries s) (S (jams s)).
Definition controllerE := sum1 (stateE counters) deviceE.
Definition tree := ptree controllerE SubEnumQ.
Inductive phase := AwaitOrder | Manufacturing (job : nat).

Definition emit {X} (e : deviceE X) : tree X := PTree.trigger (inr1 e).
Definition update (f : counters → counters) : tree unit :=
  s <- State.get;; State.put (f s).

Definition respond (job : nat) (reply : machine_reply) : tree (phase + Empty_set) :=
  match reply with
  | Pass =>
      update count_pass;;
      emit (Ship job);;
      Ret (inl AwaitOrder)
  | Rework =>
      update count_rework;;
      Ret (inl (Manufacturing job))
  | Jam =>
      update count_jam;;
      emit (Alarm job);;
      emit WaitReset;;
      Ret (inl (Manufacturing job))
  end.

Definition attempt (sampler : tree bool) job : tree (phase + Empty_set) :=
  fast <- sampler;;
  Vis (inr1 (RunMachine job fast)) (respond job).
Definition controller_step sampler (pc : phase) : tree (phase + Empty_set) :=
  match pc with
  | AwaitOrder => Vis (inr1 ReceiveOrder) (λ job, Ret (inl (Manufacturing job)))
  | Manufacturing job => attempt sampler job
  end.
Definition controller sampler pc : tree Empty_set := PTree.iter (controller_step sampler) pc.

(** Closed source sampler is embedded by the ordinary interpreter. *)
Definition embed {E A} (t : ptree factoryE SubEnumQ A) : ptree E SubEnumQ A :=
  PTree.interp_tree (λ X (e : factoryE X), match e with end) t.
Definition direct_q (q : rat) (q0 : (0 <= q)%R) (q1 : (q <= 1)%R) : ptree factoryE SubEnumQ bool :=
  sample (bernoulli q0 q1).
Definition implementation_sampler : tree bool :=
  embed (BoundedVonNeumann.factory third_false_nonnegative third_true_nonnegative
    third_bias_normalized (2/5)%R).
Definition specification_sampler : tree bool :=
  embed (direct_q two_fifths_nonnegative two_fifths_at_most_one).
Definition controller_impl := controller implementation_sampler AwaitOrder.
Definition controller_spec := controller specification_sampler AwaitOrder.
Definition device_controller_impl s := run_state controller_impl s.
Definition device_controller_spec s := run_state controller_spec s.
End Controller.

Module Scripted.
(** A finite experiment around the SAME infinite controller. Exhausting a
    device script raises an explicit experiment-stop exception, not Lost or
    program termination. Internal samplers still have no retry bound. *)

Import Controller.
Import ListNotations.

Inductive log_entry :=
| Accepted (job : nat)
| Attempted (job : nat) (fast : bool) (reply : machine_reply)
| Shipped (job : nat)
| Alarmed (job : nat)
| ResetAcknowledged.
Record script_state := Script {
  orders : list nat;
  replies : list machine_reply;
  reverse_log : list log_entry
}.
Definition scriptE := sum1 (stateE script_state) (sum1 (exceptE script_state) void1).
Definition script_tree := ptree scriptE SubEnumQ.

Definition stop_experiment {A} (s : script_state) : script_tree A := Exception.throw s.
Definition remember {A} (s : script_state) (v : A) : script_tree A :=
  State.put s;; Ret v.

Definition device_handler X (e : deviceE X) : script_tree X :=
  s <- State.get;;
  match e in deviceE Y return script_tree Y with
  | ReceiveOrder => match orders s with
      | [] => stop_experiment s
      | j :: rest => remember (Script rest (replies s) (Accepted j :: reverse_log s)) j
      end
  | RunMachine j fast => match replies s with
      | [] => stop_experiment s
      | reply :: rest => remember
          (Script (orders s) rest (Attempted j fast reply :: reverse_log s)) reply
      end
  | Ship j => remember (Script (orders s) (replies s) (Shipped j :: reverse_log s)) tt
  | Alarm j => remember (Script (orders s) (replies s) (Alarmed j :: reverse_log s)) tt
  | WaitReset => remember (Script (orders s) (replies s) (ResetAcknowledged :: reverse_log s)) tt
  end.

Definition close_controller (t : ptree deviceE SubEnumQ (counters * Empty_set)) s :=
  run_exception (run_state (PTree.interp_tree device_handler t) s).
Definition scripted_impl counts s := close_controller (device_controller_impl counts) s.
Definition scripted_spec counts s := close_controller (device_controller_spec counts) s.
Definition demo_script := Script [17;23] [Rework;Jam;Pass;Pass] [].
Definition demo_impl := scripted_impl initial_counters demo_script.
Definition demo_spec := scripted_spec initial_counters demo_script.

Definition chronological_log s := rev (reverse_log s).
End Scripted.

Module Rewriting.
(** Self-contained full-program calculation. Rewrite the sampler directly
    inside the manufacturing step, then the step under the handler stack.
    Library congruences are used automatically by setoid rewriting.
    Only the two unbounded analyses are
    opaque: VN -> fair, and the standard binary loop -> Bernoulli(q).
    No application-specific congruence lemma from [Facts] is used. *)

Import FreeOmegaRewriting.

Import Controller Scripted.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** Select the observable interpretation explicitly. This is notation for
    the raw generic relation, not a second relation or a canonical wrapper. *)
Local Notation W :=
  (PEutt.peutt (MN := SubEnumQ) (MF := FreeOmega SubEnumQ)
    (FI := @FreeOmegaObservableSemanticMeasure SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega)
    (FC := @FreeOmegaObservableSemanticMeasureCoreLaws SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticMeasureCoreLaws SubEnumQ_SemanticOmega)
    (MX := @StructuralMeasure.FreeOmegaMixedMeasure SubEnumQ)
    (FO := @FreeOmegaObservableSemanticOmega SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega)).
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
    The conclusion compares the SAME controller and complete handler stack. *)
Local Notation "'Run' sampler" :=
  (run_exception
    (run_state
      (PTree.interp_tree device_handler
        (run_state (controller (embed sampler) pc) counts)) script))
  (at level 10, sampler at next level).

Theorem factory_controller_program_rewrite :
  Run (BoundedVonNeumann.factory pf0 pt0 pnorm q) ≈ₚ Run (direct_q q0 q1).
Proof.
  assert (Hstep : pointwise_relation phase (W eq)
    (controller_step (embed (BoundedVonNeumann.factory pf0 pt0 pnorm q)))
    (controller_step (embed (direct_q q0 q1)))).
  { intros [|job]; cbn [controller_step]; [reflexivity|].
    unfold attempt, embed.
    unfold BoundedVonNeumann.factory, direct_q, factory_with_sampler, factory_sampler_step.
    (* 1. Replace the unbounded two-draw VN sampler by one fair draw. *)
    setoid_rewrite (BoundedVonNeumann.sampler_fair pf0 pt0 pnorm
      (mulr_gt0 pfpos ptpos)).
    fold (@factory_with_sampler factoryE SubEnumQ (sample fair_coin) q).
    (* 2. Replace the fair-bit binary factory by its direct Bernoulli law. *)
    setoid_rewrite (BoundedFactory.fair_factory_direct q0 q1).
    reflexivity.
  }
  unfold controller.
  setoid_rewrite Hstep.
  reflexivity.
Qed.
End FullProgram.

(** This is the actual pair of closed programs used by OCaml extraction. *)
Corollary scripted_controller_program_rewrite counts script :
  scripted_impl counts script ≈ₚ scripted_spec counts script.
Proof.
  unfold scripted_impl, scripted_spec, close_controller,
    device_controller_impl, device_controller_spec, controller_impl, controller_spec,
    implementation_sampler, specification_sampler.
  have pfpos : 0 < vn_one_third by vm_compute; reflexivity.
  have ptpos : 0 < vn_two_thirds by vm_compute; reflexivity.
  (* The extracted program keeps its original nonnegativity certificates.
     Boolean proof uniqueness aligns these with the derived certificates. *)
  replace third_false_nonnegative with (ltW pfpos) by apply bool_irrelevance.
  replace third_true_nonnegative with (ltW ptpos) by apply bool_irrelevance.
  apply factory_controller_program_rewrite.
Qed.
End Rewriting.

Module Facts.
(** User-facing algebra: probability is proved once in the existing factory,
    then transported through bind, eventful iteration and State. *)

Import Controller.
Import Scripted.
Import FreeOmegaRewriting.

Lemma embed_preserves {E A} (t u : ptree factoryE SubEnumQ A) :
  t ≈ₚ u → @embed E A t ≈ₚ embed u.
Proof. apply peutt_interp. Qed.

Theorem implementation_sampler_correct : implementation_sampler ≈ₚ specification_sampler.
Proof.
  unfold implementation_sampler, specification_sampler, BoundedVonNeumann.factory, direct_q, embed,
    factory_with_sampler, factory_sampler_step.
  setoid_rewrite (BoundedVonNeumann.sampler_fair third_false_nonnegative
    third_true_nonnegative third_bias_normalized third_bias_nontrivial).
  fold (@factory_with_sampler factoryE SubEnumQ (sample fair_coin) (2/5)%R).
  setoid_rewrite (BoundedFactory.fair_factory_direct two_fifths_nonnegative two_fifths_at_most_one).
  reflexivity.
Qed.

Lemma controller_step_congr s t : s ≈ₚ t →
  pointwise_relation phase (λ x y, x ≈ₚ y) (controller_step s) (controller_step t).
Proof.
  intros H [|job]; cbn [controller_step]; [reflexivity|].
  unfold attempt. setoid_rewrite H. reflexivity.
Qed.

Theorem controller_congr s t : s ≈ₚ t → ∀ pc,
  controller s pc ≈ₚ controller t pc.
Proof.
  intros H pc. unfold controller.
  setoid_rewrite (controller_step_congr H). reflexivity.
Qed.

(** Main source theorem: no whole-controller coupling or coinduction. *)
Theorem controller_refinement : controller_impl ≈ₚ controller_spec.
Proof.
  unfold controller_impl, controller_spec, controller.
  setoid_rewrite (controller_step_congr implementation_sampler_correct).
  reflexivity.
Qed.

Theorem state_controller_refinement s : device_controller_impl s ≈ₚ device_controller_spec s.
Proof. apply run_state_peutt_eq. exact controller_refinement. Qed.

(** Any device interpretation, not only the scripted demo, preserves the
    source refinement. No liveness assumption about device responses. *)
Theorem device_handler_refinement {F} (h : ∀ X, deviceE X → ptree F SubEnumQ X) s :
  PTree.interp_tree h (device_controller_impl s) ≈ₚ
  PTree.interp_tree h (device_controller_spec s).
Proof. apply peutt_interp. apply state_controller_refinement. Qed.

Theorem scripted_controller_refinement counts script :
  scripted_impl counts script ≈ₚ scripted_spec counts script.
Proof.
  unfold scripted_impl, scripted_spec, close_controller.
  setoid_rewrite state_controller_refinement. reflexivity.
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
  controller (embed (BoundedVonNeumann.factory pf0 pt0 pnorm q)) pc ≈ₚ
  controller (embed (direct_q q0 q1)) pc.
Proof.
  apply controller_congr, embed_preserves.
  unfold BoundedVonNeumann.factory, direct_q, factory_with_sampler, factory_sampler_step.
  setoid_rewrite (BoundedVonNeumann.sampler_fair pf0 pt0 pnorm pnontrivial).
  fold (@factory_with_sampler factoryE SubEnumQ (sample fair_coin) q).
  setoid_rewrite (BoundedFactory.fair_factory_direct q0 q1). reflexivity.
Qed.
End RationalParameters.
End Facts.

Module Observation.
(** Next-device action law. The frontier retains the FULL reply continuation;
    the boolean query only projects the chosen production mode afterwards. *)

Import Controller Facts.
Import FreeOmegaRewriting.
Import ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Definition resume sampler (v : phase + Empty_set) : tree Empty_set :=
  match v with
  | inl pc => Tau (controller sampler pc)
  | inr x => Ret x
  end.
Definition machine_cont sampler job reply :=
  next <- respond job reply;; resume sampler next.
Definition after_receive sampler job : tree Empty_set :=
  fast <- sampler;;
  Vis (inr1 (RunMachine job fast)) (machine_cont sampler job).

Lemma controller_order_unfold sampler :
  controller sampler AwaitOrder ≈ₚ
  Vis (inr1 ReceiveOrder) (λ job, controller sampler (Manufacturing job)).
Proof.
  unfold controller at 1. rewrite peutt_iter_unfold.
  change (Vis (inr1 ReceiveOrder)
    (λ job, PTree.bind (Ret (inl (Manufacturing job))) (resume sampler)) ≈ₚ
    Vis (inr1 ReceiveOrder) (λ job, controller sampler (Manufacturing job))).
  apply peutt_vis. intro job.
  transitivity (resume sampler (inl (Manufacturing job))).
  - exact (PTree.Eq.Algebra.peutt_bind_ret_l _ (resume sampler)).
  - apply peutt_tau_l.
Qed.

Lemma controller_manufacturing_unfold sampler job :
  controller sampler (Manufacturing job) ≈ₚ after_receive sampler job.
Proof.
  unfold controller at 1. rewrite peutt_iter_unfold.
  change (PTree.bind (attempt sampler job) (resume sampler) ≈ₚ after_receive sampler job).
  unfold attempt, after_receive. rewrite peutt_bind_assoc.
  eapply peutt_bind; [reflexivity|]. intros x y ->.
  apply PTree.Eq.Algebra.peutt_observe_eq. reflexivity.
Qed.

Section NextAction.
Variable q : rat.
Variables (q0 : 0 <= q) (q1 : q <= 1).
Local Notation coin := (bernoulli q0 q1).
Definition native_sampler : tree bool := sample coin.

Lemma embedded_direct_native : embed (direct_q q0 q1) ≈ₚ native_sampler.
Proof.
  unfold embed, direct_q, native_sampler. rewrite peutt_interp_prob.
  setoid_rewrite peutt_interp_ret. reflexivity.
Qed.

(** The simple normal form keeps the actual implementation continuation.
    Only the finite pre-Vis sampling computation is replaced. *)
Definition next_normal sampler job : tree Empty_set :=
  Prob coin (λ fast, Vis (inr1 (RunMachine job fast)) (machine_cont sampler job)).

Lemma next_normal_form sampler job : sampler ≈ₚ native_sampler →
  after_receive sampler job ≈ₚ next_normal sampler job.
Proof.
  intro H. unfold after_receive.
  setoid_rewrite H at 1.
  unfold native_sampler, PTree.sample.
  setoid_rewrite (peutt_sample_bind coin). reflexivity.
Qed.

Definition next_device sampler job s := run_state (next_normal sampler job) s.
Definition device_front sampler job s :=
  fast ←ω coin ;;
  ηω (FHVis (RunMachine job fast)
    (λ reply, run_state (machine_cont sampler job reply) s)).

Lemma next_device_hitting sampler job s :
  next_device sampler job s ⇓ₕ device_front sampler job s.
Proof.
  change (Prob coin (λ fast,
    Vis (RunMachine job fast) (λ reply, run_state (machine_cont sampler job reply) s))
    ⇓ₕ device_front sampler job s).
  unfold device_front.
  apply (stable_hitting_prob (FI := FreeOmegaObservableSemanticMeasure)
    (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure)
    (front := λ fast, ηω (FHVis (RunMachine job fast)
      (λ reply, run_state (machine_cont sampler job reply) s))))
    with (Good := λ _, True).
  - apply sem_ae_true.
  - intros b _. apply (stable_hitting_vis
      (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)).
Qed.

(** Every complete implementation frontier couples with the explicit normal
    frontier, relating whole reply continuations, not just event labels. *)
Theorem next_device_frontier sampler job s out :
  sampler ≈ₚ native_sampler →
  run_state (controller sampler (Manufacturing job)) s ⇓ₕ out →
  out ≈[stable_head_rel eq (λ t u, t ≈ₚ u)]ₘ device_front sampler job s.
Proof.
  intros H Hhit. eapply peutt_hitting_lift.
  - apply run_state_peutt_eq. transitivity (after_receive sampler job).
    + apply controller_manufacturing_unfold.
    + apply next_normal_form. exact H.
  - exact Hhit.
  - apply next_device_hitting.
Qed.

Definition accepts_mode (fast : bool) {X} (e : deviceE X) : bool :=
  match e with RunMachine _ b => Bool.eqb b fast | _ => false end.
Definition mode_query sampler job s fast :=
  device_front sampler job s >>=ₘ λ h,
  ηₘ (observe_stable_head (λ _, false) (@accepts_mode fast) h).

Lemma next_device_query sampler job s fast :
  next_event_query (MF := FreeOmega SubEnumQ)
    (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)
    (@accepts_mode fast) (next_device sampler job s) (mode_query sampler job s fast).
Proof. exists (device_front sampler job s). split; [apply next_device_hitting|apply sem_eq_refl]. Qed.

Definition mode_measure fast : SubEnumQ bool :=
  coin >>=ₘ λ b, ηₘ (Bool.eqb b fast).
Lemma mode_query_denotes sampler job s fast :
  free_omega_denotes (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)
    (λ b : bool, b) (mode_query sampler job s fast) (mode_measure fast).
Proof.
  exists (mode_measure fast). split; [|apply sem_eq_refl].
  unfold mode_query, device_front, mode_measure.
  cbn [sem_bind sem_ret free_omega_bind FreeOmegaObservableSemanticMeasure
    observe_stable_head accepts_mode].
  constructor. intro b.
  exact (@FOOObserveRet SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    bool bool (λ x, x) (Bool.eqb b fast)).
Qed.

Lemma mode_measure_probability fast :
  enumQ_expect subenumQ_bool_indicator (subenumQ_raw (mode_measure fast)) =
    if fast then q else 1-q.
Proof.
  change (enumQ_expect subenumQ_bool_indicator
    (bind_EnumQ (rational_bernoulli_measure q0 q1)
      (λ b, ret_EnumQ (Bool.eqb b fast))) = if fast then q else 1-q).
  rewrite enumQ_expect_bind.
  transitivity (enumQ_expect (λ b, if Bool.eqb b fast then 1 else 0)
    (rational_bernoulli_measure q0 q1)).
  { apply finite_expect_ext. intro b. apply enumQ_expect_ret. }
  rewrite rational_bernoulli_indicator. by destruct fast; rewrite /= ?addr0 ?add0r.
Qed.

Theorem next_action_distribution sampler job s fast :
  sampler ≈ₚ native_sampler →
  ∃ query,
    next_event_query (MF := FreeOmega SubEnumQ)
      (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)
      (@accepts_mode fast) (run_state (controller sampler (Manufacturing job)) s) query ∧
    mode_query sampler job s fast ≈[eq]ₘ query.
Proof.
  intro H. eapply peutt_preserves_next_event_query.
  - apply peutt_sym, run_state_peutt_eq.
    transitivity (after_receive sampler job).
    + apply controller_manufacturing_unfold.
    + apply next_normal_form. exact H.
  - apply next_device_query.
Qed.

Definition select_mode (fast : bool) {X} (e : deviceE X) : option X :=
  match e in deviceE Y return option Y with
  | RunMachine _ b => if Bool.eqb b fast then Some Pass else None
  | _ => None
  end.

Lemma select_mode_accept fast :
  @selector_accept deviceE (@select_mode fast) = @accepts_mode fast.
Proof.
  apply functional_extensionality_dep. intro X.
  apply functional_extensionality. intro e. destruct e; try reflexivity.
  destruct fast0, fast; reflexivity.
Qed.

(** Numeric, paper-facing endpoint. The one-event selector merely supplies
    an arbitrary reply; for a singleton query the continuation is not run. *)
Theorem next_action_probability sampler job s fast :
  sampler ≈ₚ native_sampler →
  Prₛ[ run_state (controller sampler (Manufacturing job)) s |
       [@select_mode fast] ] = (if fast then q else 1-q).
Proof.
  intro H. destruct (next_action_distribution job s fast H) as [query [Hquery Hlift]].
  eapply subenumQ_finite_interaction_probability_intro
    with (query := query) (representative := mode_query sampler job s fast)
      (out := mode_measure fast).
  - apply (proj2 (finite_interaction_query_singleton_iff_next_event_query
      (@select_mode fast) _ _)).
    rewrite select_mode_accept. exact Hquery.
  - exact Hlift.
  - apply mode_query_denotes.
  - apply mode_measure_probability.
Qed.
End NextAction.

Theorem factory_next_action_probability job s fast :
  Prₛ[ run_state (controller implementation_sampler (Manufacturing job)) s |
       [@select_mode fast] ] = (if fast then 2/5 else 3/5).
Proof.
  replace (if fast then 2/5 else 3/5 : rat) with
    (if fast then 2/5 else 1-2/5 : rat) by (destruct fast; reflexivity).
  apply (next_action_probability (q0 := two_fifths_nonnegative)
    (q1 := two_fifths_at_most_one)).
  transitivity specification_sampler; [apply implementation_sampler_correct|].
  apply embedded_direct_native.
Qed.
End Observation.

Export Controller Scripted Rewriting Facts Observation.
