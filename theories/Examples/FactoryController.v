(** Case role: paper case study.
    Proof mode: algebraic rewriting.
    Reading entry: Rewriting.factory_controller_program_rewrite.
    Scope: EnumQ / observable FreeOmega; native validity and quantitative results are separate.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
(** Interactive Bernoulli factory: a single, end-to-end case study.

    Reading order:
    1. Controller: the infinite effectful program and its two samplers.
    2. Scripted: State/Exception/device interpretation and executable roots.
    3. Rewriting: the self-contained, full-program algebraic calculation.
    4. Facts: reusable congruences and short refinement corollaries.
    5. Probability: native sampling validity.
    6. Observation: exact next-action distribution and probabilities.

    The internal modules isolate local notation/instances and retain the
    existing qualified declaration names. Tests and the OCaml host remain
    separate; this file does not duplicate the sampler analysis library. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Set Implicit Arguments.
Unset Strict Implicit.
Set Default Timeout 20.
From Coq Require Import List Morphisms FunctionalExtensionality.
From Coq.Program Require Import Equality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat.
From ITree.Events Require Import State Exception.
From ITree.Indexed Require Import Sum.
From PTree Require Import PTreeFacts.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import WellFormedness Shallow ProbabilisticTrace PTreeKernel.
From PTree.Eq.Backend Require Import EnumQ ProbabilisticTraceEnumQ.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Prob.Backend.EnumQ Require Import Representation Measure Bind.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure
  PTree.Prob.FreeOmega.Observation.
From PTree.Prob.FreeOmega Require Import StructuralMeasure RelationalLimit.
From PTree.Interp Require Import State StateFacts Exception ExceptionFacts IterationUniform.
From PTree.Interp.FreeOmega Require Import Base Unrestricted State Rewriting.
From PTree.Examples.BernoulliFactory Require Import
  BernoulliFactory BernoulliFactoryComposition BernoulliFactoryProbability
  OperationalBernoulliFactory VonNeumannUnbounded RationalBernoulli.

Module Controller.
(** Interactive factory: the existing nested sampler, not a new algorithm.
    Three independent sources of unbounded behavior: VN, binary factory,
    and the reactive service (including environment-driven retries). *)

Import EnumQ.

Inductive machine_reply := Pass | Rework | Jam.
Variant deviceE : Type -> Type :=
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
Definition tree := ptree controllerE EnumQ.
Inductive phase := AwaitOrder | Manufacturing (job : nat).

Definition emit {X} (e : deviceE X) : tree X := PTree.trigger (inr1 e).
Definition update (f : counters -> counters) : tree unit :=
  PTree.bind (State.get) (fun s => State.put (f s)).

Definition respond (job : nat) (reply : machine_reply) : tree (phase + Empty_set) :=
  match reply with
  | Pass => PTree.bind (update count_pass) (fun _ =>
      PTree.bind (emit (Ship job)) (fun _ => Ret (inl AwaitOrder)))
  | Rework => PTree.bind (update count_rework) (fun _ => Ret (inl (Manufacturing job)))
  | Jam => PTree.bind (update count_jam) (fun _ =>
      PTree.bind (emit (Alarm job)) (fun _ =>
      PTree.bind (emit WaitReset) (fun _ => Ret (inl (Manufacturing job)))))
  end.

Definition attempt (sampler : tree bool) job : tree (phase + Empty_set) :=
  PTree.bind sampler (fun fast =>
    Vis (inr1 (RunMachine job fast)) (respond job)).
Definition controller_step sampler (pc : phase) : tree (phase + Empty_set) :=
  match pc with
  | AwaitOrder => Vis (inr1 ReceiveOrder) (fun job => Ret (inl (Manufacturing job)))
  | Manufacturing job => attempt sampler job
  end.
Definition controller sampler pc : tree Empty_set := PTree.iter (controller_step sampler) pc.

(** Closed source sampler is embedded by the ordinary interpreter. *)
Definition embed {E A} (t : ptree factoryE EnumQ A) : ptree E EnumQ A :=
  PTree.interp (fun X (e : factoryE X) => match e with end) t.
Definition implementation_sampler : tree bool := embed third_to_two_fifths.
Definition specification_sampler : tree bool := embed direct_two_fifths.
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
Import ListNotations EnumQ.

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
Definition script_tree := ptree scriptE EnumQ.

Definition stop_experiment {A} (s : script_state) : script_tree A := Exception.throw s.
Definition remember {A} (s : script_state) (v : A) : script_tree A :=
  PTree.bind (State.put s) (fun _ => Ret v).

Definition device_handler X (e : deviceE X) : script_tree X :=
  PTree.bind State.get (fun s =>
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
  end).

Definition close_controller (t : ptree deviceE EnumQ (counters * Empty_set)) s :=
  run_exception (run_state (PTree.interp device_handler t) s).
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
  (PEutt.peutt (MN := EnumQ) (MF := FreeOmega EnumQ)
    (FI := @FreeOmegaObservableSemanticMeasure EnumQ EnumQ_SemanticMeasure EnumQ_SemanticOmega)
    (FC := @FreeOmegaObservableSemanticMeasureCoreLaws EnumQ EnumQ_SemanticMeasure EnumQ_SemanticMeasureCoreLaws EnumQ_SemanticOmega)
    (MX := @StructuralMeasure.FreeOmegaMixedMeasure EnumQ)
    (FO := @FreeOmegaObservableSemanticOmega EnumQ EnumQ_SemanticMeasure EnumQ_SemanticOmega)).
Local Notation "t ≈ₚ u" := (W eq t u)
  (at level 70, no associativity) : type_scope.

(** Local analysis endpoint: the native finite-round calculation is isolated
    here; the program calculation consumes only its behavioral equation. *)
Lemma fair_binary_round_step x :
  Prob (sem_bind vn_fair (fun b => sem_ret (binary_round_result x b)))
    (fun a => Ret a) ≈ₚ factory_standard_step x.
Proof.
  change (Prob (bind_EnumQ vn_fair
    (fun b => ret_EnumQ (binary_round_result x b))) (fun a => Ret a)
    ≈ₚ factory_standard_step x).
  unfold factory_standard_step.
  rewrite fair_binary_round_measure. reflexivity.
Qed.

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
      (PTree.interp device_handler
        (run_state (controller (embed sampler) pc) counts)) script))
  (at level 10, sampler at next level).

Theorem factory_controller_program_rewrite :
  Run (biased_to_rational_coin pf0 pt0 q) ≈ₚ Run (factory_direct_q q0 q1).
Proof.
  assert (Hstep : pointwise_relation phase (W eq)
    (controller_step (embed (biased_to_rational_coin pf0 pt0 q)))
    (controller_step (embed (factory_direct_q q0 q1)))).
  { intros [|job]; cbn [controller_step]; [reflexivity|].
    unfold attempt, embed.
    unfold biased_to_rational_coin.
    (* 1. Factory(VN(p),q) -> Factory(Fair,q).
          First and only VN probability-analysis lemma. *)
    setoid_rewrite (peutt_factory_vn_fair pf0 pt0 pnorm (mulr_gt0 pfpos ptpos)).

    (* 2. Open the outer factory loop; distribute bind through sampling,
          eliminate Ret, and combine the finite sampling/return step. *)
    unfold factory_with_sampler, factory_sampler_step, factory_direct_fair.
    setoid_rewrite (peutt_sample_bind vn_fair).
    setoid_rewrite (peutt_sample_map vn_fair).
    setoid_rewrite fair_binary_round_step.

    (* 3. The residual sampler is the standard binary loop. *)
    (* Second probability-analysis lemma: the unbounded binary loop's law. *)
    setoid_rewrite (peutt_factory_standard_direct q0 q1).
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
End Rewriting.

Module Facts.
(** User-facing algebra: probability is proved once in the existing factory,
    then transported through bind, eventful iteration and State. *)

Import Controller.
Import Scripted.

Lemma embed_preserves {E A} (t u : ptree factoryE EnumQ A) :
  t ≈ₚ u -> @embed E A t ≈ₚ embed u.
Proof. apply peutt_interp. Qed.

#[export] Instance embed_Proper {E A} :
  Proper (canonical_peutt eq ==> canonical_peutt eq) (@embed E A).
Proof. intros t u H. apply embed_preserves. exact H. Qed.

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

#[export] Instance controller_Proper :
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
End Facts.

Module Probability.
(** The retained legacy factory uses raw EnumQ. Its use here is a genuine
    probability program, not arbitrary finite weights. No termination claim
    is needed for this node-validity invariant. *)

Import Controller.
Import EnumQ.

Lemma embed_probability {E A} (t : ptree factoryE EnumQ A) :
  probabilistic_ptree t -> probabilistic_ptree (@embed E A t).
Proof.
  revert t. cofix CIH. intros t H.
  unfold probabilistic_ptree, embed in *.
  rewrite observe_interp. destruct H.
  - constructor.
  - constructor. apply CIH. assumption.
  - destruct e.
  - constructor; [assumption|]. intro x. apply CIH. apply H0.
Qed.

Lemma update_probability f : probabilistic_ptree (update f).
Proof.
  unfold update, State.get, State.put, PTree.trigger.
  apply probabilistic_ptree_bind.
  - apply probabilistic_ptree_vis. intro s. apply probabilistic_ptree_ret.
  - intro s. apply probabilistic_ptree_vis. intro u. apply probabilistic_ptree_ret.
Qed.

Lemma respond_probability j r : probabilistic_ptree (respond j r).
Proof.
  destruct r; cbn [respond]; apply probabilistic_ptree_bind;
    try apply update_probability; intro u.
  - apply probabilistic_ptree_bind.
    + apply probabilistic_ptree_vis. intro x. apply probabilistic_ptree_ret.
    + intro x. apply probabilistic_ptree_ret.
  - apply probabilistic_ptree_ret.
  - apply probabilistic_ptree_bind.
    + apply probabilistic_ptree_vis. intro x. apply probabilistic_ptree_ret.
    + intro x. apply probabilistic_ptree_bind.
      * apply probabilistic_ptree_vis. intro y. apply probabilistic_ptree_ret.
      * intro y. apply probabilistic_ptree_ret.
Qed.

Theorem controller_probability sampler pc :
  probabilistic_ptree sampler -> probabilistic_ptree (controller sampler pc).
Proof.
  intro H. apply probabilistic_ptree_iter. intros [|j].
  - apply probabilistic_ptree_vis. intro x. apply probabilistic_ptree_ret.
  - apply probabilistic_ptree_bind; [exact H|].
    intro b. apply probabilistic_ptree_vis. intro r. apply respond_probability.
Qed.

Theorem implementation_probability : probabilistic_ptree controller_impl.
Proof.
  apply controller_probability, embed_probability.
  exact probabilistic_third_to_two_fifths.
Qed.

Theorem specification_probability : probabilistic_ptree controller_spec.
Proof. apply controller_probability, embed_probability, probabilistic_factory_direct_q. Qed.
End Probability.

Module Observation.
(** Next-device action law. The frontier retains the FULL reply continuation;
    the boolean query only projects the chosen production mode afterwards. *)

Import Controller Facts.
Import ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Definition resume sampler (v : phase + Empty_set) : tree Empty_set :=
  match v with
  | inl pc => Tau (controller sampler pc)
  | inr x => Ret x
  end.
Definition machine_cont sampler job reply := PTree.bind (respond job reply) (resume sampler).
Definition after_receive sampler job : tree Empty_set :=
  PTree.bind sampler (fun fast => Vis (inr1 (RunMachine job fast)) (machine_cont sampler job)).

Lemma controller_order_unfold sampler :
  controller sampler AwaitOrder ≈ₚ
  Vis (inr1 ReceiveOrder) (fun job => controller sampler (Manufacturing job)).
Proof.
  unfold controller at 1. rewrite peutt_iter_unfold.
  change (Vis (inr1 ReceiveOrder)
    (fun job => PTree.bind (Ret (inl (Manufacturing job))) (resume sampler)) ≈ₚ
    Vis (inr1 ReceiveOrder) (fun job => controller sampler (Manufacturing job))).
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
Local Notation coin := (rational_bernoulli_measure q0 q1).
Definition native_sampler : tree bool := Prob coin (fun b => Ret b).

Lemma embedded_direct_native : embed (factory_direct_q q0 q1) ≈ₚ native_sampler.
Proof.
  unfold embed, factory_direct_q, native_sampler. rewrite peutt_interp_prob.
  eapply peutt_prob with (XR := eq).
  - apply sem_lift_refl. intros b. reflexivity.
  - intros b c ->. apply peutt_interp_ret.
Qed.

(** The simple normal form keeps the actual implementation continuation.
    Only the finite pre-Vis sampling computation is replaced. *)
Definition next_normal sampler job : tree Empty_set :=
  Prob coin (fun fast => Vis (inr1 (RunMachine job fast)) (machine_cont sampler job)).

Lemma next_normal_form sampler job : sampler ≈ₚ native_sampler ->
  after_receive sampler job ≈ₚ next_normal sampler job.
Proof.
  intro H. unfold after_receive.
  transitivity (PTree.bind native_sampler
    (fun fast => Vis (inr1 (RunMachine job fast)) (machine_cont sampler job))).
  - eapply peutt_bind; [exact H|]. intros b c ->. reflexivity.
  - change (Prob coin (fun b => PTree.bind (Ret b)
      (fun fast => Vis (inr1 (RunMachine job fast)) (machine_cont sampler job))) ≈ₚ
      next_normal sampler job).
    eapply peutt_prob with (XR := eq).
    + apply sem_lift_refl. intro b. reflexivity.
    + intros b c ->. exact (PTree.Eq.Algebra.peutt_bind_ret_l c
        (fun fast => Vis (inr1 (RunMachine job fast)) (machine_cont sampler job))).
Qed.

Definition next_device sampler job s := run_state (next_normal sampler job) s.
Definition device_front sampler job s :=
  FOSample coin (fun fast => FORet
    (FHVis (RunMachine job fast) (fun reply => run_state (machine_cont sampler job reply) s))).

Lemma next_device_hitting sampler job s :
  ptree_stable_hitting (MF := FreeOmega EnumQ)
    (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)
    (observe (next_device sampler job s)) (device_front sampler job s).
Proof.
  change (ptree_stable_hitting (MF := FreeOmega EnumQ)
    (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)
    (observe (Prob coin (fun fast =>
      Vis (RunMachine job fast) (fun reply => run_state (machine_cont sampler job reply) s))))
    (device_front sampler job s)).
  unfold device_front.
  apply (stable_hitting_prob (FI := FreeOmegaObservableSemanticMeasure)
    (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure)
    (front := fun fast => FORet (FHVis (RunMachine job fast)
      (fun reply => run_state (machine_cont sampler job reply) s))))
    with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. apply (stable_hitting_vis
      (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)).
Qed.

(** Every complete implementation frontier couples with the explicit normal
    frontier, relating whole reply continuations, not just event labels. *)
Theorem next_device_frontier sampler job s out :
  sampler ≈ₚ native_sampler ->
  ptree_stable_hitting (MF := FreeOmega EnumQ)
    (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)
    (observe (run_state (controller sampler (Manufacturing job)) s)) out ->
  sem_lift (SemanticMeasure := FreeOmegaObservableSemanticMeasure)
    (stable_head_rel eq (fun t u => t ≈ₚ u)) out (device_front sampler job s).
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
  sem_bind (SemanticMeasure := FreeOmegaObservableSemanticMeasure) (device_front sampler job s)
    (fun h => sem_ret (observe_stable_head (fun _ => false) (@accepts_mode fast) h)).

Lemma next_device_query sampler job s fast :
  next_event_query (MF := FreeOmega EnumQ)
    (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)
    (@accepts_mode fast) (next_device sampler job s) (mode_query sampler job s fast).
Proof. exists (device_front sampler job s). split; [apply next_device_hitting|apply sem_eq_refl]. Qed.

Definition mode_measure fast : EnumQ bool :=
  bind_EnumQ coin (fun b => ret_EnumQ (Bool.eqb b fast)).
Lemma mode_query_denotes sampler job s fast :
  free_omega_denotes (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega)
    (fun b : bool => b) (mode_query sampler job s fast) (mode_measure fast).
Proof.
  exists (mode_measure fast). split; [|apply sem_eq_refl].
  unfold mode_query, device_front, mode_measure.
  cbn [sem_bind sem_ret free_omega_bind FreeOmegaObservableSemanticMeasure
    observe_stable_head accepts_mode].
  constructor. intro b.
  exact (@FOOObserveRet EnumQ EnumQ_SemanticMeasure EnumQ_SemanticOmega
    bool bool (fun x => x) (Bool.eqb b fast)).
Qed.

Lemma mode_measure_probability fast :
  enumQ_expect enumQ_bool_indicator (mode_measure fast) = if fast then q else 1-q.
Proof.
  unfold mode_measure. rewrite enumQ_expect_bind.
  replace (fun b => enumQ_expect enumQ_bool_indicator (ret_EnumQ (Bool.eqb b fast)))
    with (fun b => if Bool.eqb b fast then 1 else 0 : rat).
  2: { apply functional_extensionality. intro b. rewrite enumQ_expect_ret. reflexivity. }
  change (enumQ_expect (fun b => if Bool.eqb b fast then 1 else 0) coin =
    if fast then q else 1-q).
  rewrite rational_bernoulli_indicator. by destruct fast; rewrite /= ?addr0 ?add0r.
Qed.

Theorem next_action_distribution sampler job s fast :
  sampler ≈ₚ native_sampler ->
  exists query,
    next_event_query (MF := FreeOmega EnumQ)
      (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)
      (@accepts_mode fast) (run_state (controller sampler (Manufacturing job)) s) query /\
    sem_lift (SemanticMeasure := FreeOmegaObservableSemanticMeasure) eq
      (mode_query sampler job s fast) query.
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
  sampler ≈ₚ native_sampler ->
  Prₜ[ run_state (controller sampler (Manufacturing job)) s |
       [@select_mode fast] ] = (if fast then q else 1-q).
Proof.
  intro H. destruct (next_action_distribution job s fast H) as [query [Hquery Hlift]].
  eapply enumQ_finite_interaction_probability_intro
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
  Prₜ[ run_state (controller implementation_sampler (Manufacturing job)) s |
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

Export Controller Scripted Rewriting Facts Probability Observation.
