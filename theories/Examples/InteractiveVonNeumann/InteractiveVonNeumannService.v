(** Case role: paper case study.
    Reading entry: interactive_von_neumann_service_equivalent; von_neumann_request_true_reply_trace_probability.
    Scope: EnumQ / observable FreeOmega; internal structural analysis is explicitly scoped.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
(** Learn: reuse a verified unbounded sampler inside up-to-bind coinduction.
    Reusable endpoints: service_sampler_equivalent, interactive_von_neumann_service_equivalent, von_neumann_request_true_reply_trace_probability.
    Boundary: quantitative witnesses remain; the service does not redo VN convergence.
    User navigation: docs/CASE_STUDIES.md. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Prob.Backend.Common Require Import FiniteRecordExtensionality.

From PTree.Eq Require Import StableHittingRelation.
From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Program Require Import Equality.
From mathcomp Require Import ssreflect ssralg rat.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.EnumQ.Representation.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Interface.Iteration.
Require Import PTree.Prob.Backend.EnumQ.Bind.
Require Import PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Iteration.
From PTree.Eq Require Import Shallow PrimitiveStableHitting UnifiedFrontier PTreeKernel PEutt.
From PTree.Eq Require Import Bind.
From PTree.Eq.Backend Require Import ProbabilisticTraceEnumQ.
From PTree.Eq Require Import ProbabilisticTrace.
From PTree.Eq.FreeOmega Require Import Base Hitting Relation Bind Algebra Iter.
From PTree.Interp.FreeOmega Require Import Base Guarded.
From PTree.Prob.FreeOmega Require Import BindOrder.
From PTree.Examples.BernoulliFactory Require Import VonNeumannUnbounded OperationalVonNeumann.
From ExtLib.Structures Require Import Monad.

Set Implicit Arguments.
#[local] Existing Instance FreeOmegaSemanticMeasure.
#[local] Existing Instance FreeOmegaSemanticOmega.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.
Import MonadNotation.
Local Open Scope monad_scope.
Import PTree.Prob.Backend.EnumQ.Map.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Universe-polymorphic singleton used as the response type of protocol
    events.  Using Coq's monomorphic [unit : Set] here would incorrectly pin
    the invariant event universe of [PTree] to [Set]. *)
Polymorphic Variant service_unit@{u} : Type@{u} := ServiceTT.

(** A client requests a fresh bit; the server then publishes its answer.
    Both events have one response, so the only observable choice is the
    reply bit. *)
Polymorphic Variant coin_serviceE@{u} : Type@{u} -> Type@{u} :=
  | CoinRequest : coin_serviceE service_unit@{u}
  | CoinReply (b : bool) : coin_serviceE service_unit@{u}.

(** Setup: one explicit observable profile, as in FactoryController.
    These local notations expand to the raw generic relation; no canonical
    wrapper or additional instance participates in the proof. *)
Local Notation tree := (ptree coin_serviceE EnumQ).
Local Notation MF := (FreeOmega EnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega)).
Local Notation MX := (@FreeOmegaMixedMeasure EnumQ).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega)).
Local Notation W := (PEutt.peutt (E := coin_serviceE) (MN := EnumQ)
  (MF := MF) (FI := FI) (FC := FC) (MX := MX) (FO := FO)).
Local Notation "t ≈ₚ u" := (W eq t u)
  (at level 70, no associativity) : type_scope.
Local Notation state := (ptree' coin_serviceE EnumQ bool).

Definition publish (b : bool) (next : tree bool) :
    tree bool :=
  Vis (CoinReply b) (fun _ => next).

(** One request is followed by a closed sampler and one visible reply. *)
Definition serve_round (sampler : tree bool)
    (next : tree bool) :
    tree bool :=
  Vis CoinRequest (fun _ =>
    b <- sampler ;; publish b next).

(** The recursive call is guarded by the request [Vis]. *)
CoFixpoint von_neumann_service : tree bool :=
  serve_round von_neumann_third_in von_neumann_service.

CoFixpoint direct_fair_service : tree bool :=
  serve_round direct_fair_in direct_fair_service.

Lemma observe_von_neumann_service :
  observe von_neumann_service =
  VisF CoinRequest (fun _ =>
    b <- von_neumann_third_in ;; publish b von_neumann_service).
Proof. reflexivity. Qed.

Lemma observe_direct_fair_service :
  observe direct_fair_service =
  VisF CoinRequest (fun _ =>
    b <- direct_fair_in ;; publish b direct_fair_service).
Proof. reflexivity. Qed.

Local Notation service_head :=
  (stable_head coin_serviceE EnumQ bool).

Definition service_head_value (h : service_head) : bool :=
  match h with
  | FHRet b => b
  | @FHVis _ _ _ X e k => false
  end.

(** The component theorem is shared with the closed executable case. *)
Theorem service_sampler_equivalent : von_neumann_third_in ≈ₚ direct_fair_in.
Proof. apply von_neumann_third_in_equivalent_to_fair. Qed.

(** Keep the original explicit AST witness, but obtain its probability law
    from component equivalence rather than repeating the VN analysis. *)
Definition service_vn_hitting (fuel : nat) : MF service_head :=
  ptree_hitting_approx (MF := MF) fuel
    (observe (@von_neumann_third_in coin_serviceE)).
Definition service_vn_heads : MF service_head :=
  FOLub (fun rounds => service_vn_hitting (ptree_vn_raw_schedule rounds)).

Lemma service_vn_weak :
  ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (@von_neumann_third_in coin_serviceE)) service_vn_heads.
Proof.
  apply stable_hitting_subsequence.
  - intro n. cbn [ptree_vn_raw_schedule]. repeat apply le_S. apply le_n.
  - exact ptree_vn_raw_schedule_ge.
Qed.

Definition service_direct_heads : MF service_head :=
  @mixed_bind EnumQ MF FreeOmegaMixedMeasure bool service_head
    vn_fair
    (fun b => @sem_ret MF
      FI service_head (FHRet b)).

Definition service_direct_observation : EnumQ bool :=
  @sem_bind EnumQ EnumQ_SemanticMeasure _ _ vn_fair
    (fun b => @sem_ret EnumQ EnumQ_SemanticMeasure bool b).

Lemma service_direct_heads_observes :
  free_omega_observes service_head_value
    service_direct_heads service_direct_observation.
Proof.
  unfold service_direct_heads, service_direct_observation.
  eapply FOOObserveSample. intro b. constructor.
Qed.

Lemma service_direct_observation_eq :
  service_direct_observation = vn_fair.
Proof.
  unfold service_direct_observation.
  change (bind_EnumQ vn_fair (fun b => ret_EnumQ b) = vn_fair).
  apply finite_enum_raw_eq.
  change (enumQ_raw (bind_EnumQ vn_fair (fun b => ret_EnumQ b)) = enumQ_raw vn_fair).
  rewrite bind_ret_emap. apply emap_id.
Qed.

Lemma service_direct_heads_total :
  @sem_total MF
    FI
    FreeOmegaObservableSemanticOmega _ service_direct_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, service_head_value, service_direct_observation.
  split; [exact service_direct_heads_observes|].
  rewrite service_direct_observation_eq. exact vn_fair_total.
Qed.

Theorem service_direct_fair_ast :
  @ptree_stable_hitting_ast coin_serviceE EnumQ MF
    FI
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe (@direct_fair_in coin_serviceE)) service_direct_heads.
Proof.
  assert (Hobserve : observe (@direct_fair_in coin_serviceE) =
    ProbF vn_fair (fun b => Ret b)) by reflexivity.
  rewrite Hobserve.
  eapply ptree_stable_hitting_ast_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. split.
    + apply ptree_stable_hitting_ret.
    + apply free_omega_observable_total_intro.
      exists bool, service_head_value,
        (@sem_ret EnumQ EnumQ_SemanticMeasure bool b).
      split; [constructor|].
      change (meas_total (ret_EnumQ b)).
      change (enumQ_expect (fun _ : bool => (1 : rat)) (ret_EnumQ b) =
        (1 : rat)).
      rewrite enumQ_expect_ret. reflexivity.
  - exact service_direct_heads_total.
Qed.

Definition service_head_is_ret (h : service_head) : Prop :=
  match h with
  | FHRet _ => True
  | @FHVis _ _ _ X e k => False
  end.

Lemma service_direct_heads_ret_only :
  free_omega_ae service_head_is_ret service_direct_heads.
Proof.
  unfold service_direct_heads.
  eapply FOAESample with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. constructor. exact I.
Qed.

Lemma service_vn_heads_eq :
  @sem_eq MF FI _ service_vn_heads service_direct_heads.
Proof.
  pose proof (peutt_hitting_lift service_sampler_equivalent
    service_vn_weak (proj1 service_direct_fair_ast)) as Hlift.
  change (@sem_lift MF FI _ _ eq service_vn_heads service_direct_heads).
  eapply sem_lift_mono; last first.
  - eapply sem_lift_ae_restrict.
    + exact Hlift.
    + apply sem_ae_true.
    + exact service_direct_heads_ret_only.
  - intros h1 h2 [Hrel [_ Hret]].
    destruct h2 as [b|X e k]; [|contradiction].
    dependent destruction Hrel. subst. reflexivity.
Qed.

Lemma service_vn_heads_total :
  @sem_total MF FI FO _ service_vn_heads.
Proof.
  apply (proj2 (sem_total_proper (SI := FI) (SO := FO) service_vn_heads_eq)).
  exact service_direct_heads_total.
Qed.

Theorem service_von_neumann_ast :
  ptree_stable_hitting_ast (FI := FI) (FO := FO)
    (observe (@von_neumann_third_in coin_serviceE)) service_vn_heads.
Proof. split; [exact service_vn_weak|exact service_vn_heads_total]. Qed.

(** A finite service round is a congruence.  The infinite theorem below
    instead retains its recursive continuation in an explicit coinduction
    candidate. *)
Lemma serve_round_congruence
    (sampler1 sampler2 next1 next2 : tree bool)
    (Hsampler : sampler1 ≈ₚ sampler2)
    (Hnext : next1 ≈ₚ next2) :
  serve_round sampler1 next1 ≈ₚ serve_round sampler2 next2.
Proof.
  unfold serve_round.
  apply peutt_vis. intros [].
  eapply peutt_bind.
  - exact Hsampler.
  - intros b1 b2 ->. unfold publish.
    apply peutt_vis. intros []. exact Hnext.
Qed.

Local Definition service_kernel {R} :
    ptree' coin_serviceE EnumQ R ->
    MF (stable_target (ptree' coin_serviceE EnumQ R)
      (stable_head coin_serviceE EnumQ R)) :=
  @ptree_primitive_kernel coin_serviceE EnumQ MF
    FI
    FreeOmegaMixedMeasure R.

Local Definition service_stable_rel {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree' coin_serviceE EnumQ R1 ->
      ptree' coin_serviceE EnumQ R2 -> Prop) :=
  @ptree_stable_head_rel coin_serviceE EnumQ R1 R2 RR sim.

Local Notation service_hitting :=
  (@ptree_stable_hitting coin_serviceE EnumQ MF
    FI
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega
    bool).

Local Definition service_lift {A B} (R : A -> B -> Prop)
    (mu : MF A) (nu : MF B) : Prop :=
  @sem_lift MF
    FI
    A B R mu nu.

Definition vn_after_request : tree bool :=
  b <- von_neumann_third_in ;; publish b von_neumann_service.

Definition direct_after_request : tree bool :=
  b <- direct_fair_in ;; publish b direct_fair_service.

Definition direct_reply_front (b : bool) :
    MF (stable_head coin_serviceE EnumQ bool) :=
  sem_ret (FHVis (CoinReply b)
    (fun _ => direct_fair_service)).

Local Opaque von_neumann_service direct_fair_service
  service_vn_heads service_direct_heads.

Definition direct_after_request_heads :
    MF (stable_head coin_serviceE EnumQ bool) :=
  free_omega_bind service_direct_heads
    (stable_head_ret_bind_front direct_reply_front).

Lemma direct_after_request_weak :
  service_hitting
    (observe direct_after_request) direct_after_request_heads.
Proof.
  unfold direct_after_request, direct_after_request_heads.
  eapply stable_hitting_bind_ret_only.
  - exact service_direct_heads_ret_only.
  - exact (proj1 service_direct_fair_ast).
  - intro b. unfold publish, direct_reply_front.
    apply (stable_hitting_vis
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)).
Qed.

(** The equivalence below is not structural reflexivity.  Immediately after
    the request, the implementation's first primitive sample is the biased
    [1/3,2/3] coin, whereas the specification samples [1/2,1/2]. *)
Lemma service_first_sampling_measure_not_direct :
  vn_biased_coin <> vn_fair.
Proof.
  intro Heq.
  have Hmass := f_equal
    (fun mu => enumQ_expect
      (fun b => if b then (0 : rat) else (1 : rat)) mu) Heq.
  cbn [vn_biased_coin vn_fair] in Hmass.
  vm_compute in Hmass. discriminate.
Qed.

Definition interactive_service_sim
    (s1 s2 : state) : Prop :=
  (s1 = observe von_neumann_service /\
    s2 = observe direct_fair_service) \/
  (exists b, s1 = observe (publish b von_neumann_service) /\
    s2 = observe (publish b direct_fair_service)).

Definition interactive_service_upto
    (s1 s2 : state) : Prop :=
  bind_upto_closure (FI := FI) (FC := FC) (MX := MX) (FO := FO)
    eq interactive_service_sim s1 s2.

(** Generator notation only; the complete-hitting progress obligation
    remains explicit, and is not replaced by a syntactic step. *)
Local Notation progress := (stable_hitting_match (FI := FI) (FO := FO)
  service_kernel service_kernel (@service_stable_rel bool bool eq)).

Lemma ISSRoot : interactive_service_sim
    (observe von_neumann_service) (observe direct_fair_service).
Proof. left. split; reflexivity. Qed.

Lemma ISSPublish b : interactive_service_sim
    (observe (publish b von_neumann_service))
    (observe (publish b direct_fair_service)).
Proof. right. exists b. split; reflexivity. Qed.

Lemma interactive_service_sim_postfixed :
  forall s1 s2, interactive_service_sim s1 s2 ->
    progress interactive_service_upto s1 s2.
Proof.
  intros s1 s2 [[-> ->]|[b [-> ->]]].
  - rewrite observe_von_neumann_service observe_direct_fair_service.
    apply stable_hitting_match_vis. intros [].
    eapply bind_upto_closure_bind.
    + exact service_sampler_equivalent.
    + intros b1 b2 ->. left. apply ISSPublish.
  - apply stable_hitting_match_vis. intros [].
    left. exact ISSRoot.
Qed.

Theorem interactive_von_neumann_service_equivalent :
  von_neumann_service ≈ₚ direct_fair_service.
Proof.
  eapply peutt_coinduction_upto_bind
    with (sim := interactive_service_sim); try typeclasses eauto.
  - intros. apply ptree_bind_cofinal_all.
  - exact interactive_service_sim_postfixed.
  - exact ISSRoot.
Qed.

(** Event-aware quantitative observation.  After a request has been
    accepted, this classifier asks whether the next visible action is
    [CoinReply true].  It does not inspect the program's return value. *)
Definition accepts_true_reply {X} (e : coin_serviceE X) : bool :=
  match e with
  | CoinRequest => false
  | CoinReply b => b
  end.

Definition direct_true_reply_query : MF bool :=
  sem_bind direct_after_request_heads
    (fun h => sem_ret
      (observe_stable_head (fun _ : bool => false) (@accepts_true_reply) h)).

Lemma direct_after_request_true_reply_query :
  @next_event_query coin_serviceE EnumQ MF
    FI
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (@accepts_true_reply) direct_after_request direct_true_reply_query.
Proof.
  exists direct_after_request_heads. split.
  - exact direct_after_request_weak.
  - apply sem_eq_refl.
Qed.

Lemma direct_true_reply_query_denotes_fair :
  free_omega_denotes (fun b : bool => b)
    direct_true_reply_query vn_fair.
Proof.
  Transparent service_direct_heads.
  exists service_direct_observation. split.
  -
  unfold direct_true_reply_query, direct_after_request_heads,
    service_direct_heads, direct_reply_front,
    stable_head_ret_bind_front, stable_head_bind_front.
  cbn [free_omega_bind mixed_bind sem_bind sem_ret
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticMeasure
    FreeOmegaSemanticMeasure observe_stable_head accepts_true_reply].
    unfold service_direct_observation. constructor. intro b. constructor.
  - rewrite service_direct_observation_eq. apply sem_eq_refl.
Qed.

Lemma direct_true_reply_probability_half :
  enumQ_expect (indicator (fun b => b)) vn_fair = (1 / 2 : rat).
Proof.
  by rewrite vn_fair_expect /indicator /= add0r mulr1.
Qed.

Lemma after_request_peutt : vn_after_request ≈ₚ direct_after_request.
Proof.
  unfold vn_after_request, direct_after_request.
  eapply peutt_bind.
  - exact service_sampler_equivalent.
  - intros b1 b2 ->. apply peutt_vis. intros [].
    exact interactive_von_neumann_service_equivalent.
Qed.

(** The implementation's unbounded retry loop has the same quantitative
    [Reply true] observation as the direct fair service.  The witness on the
    implementation side is coupled to the explicit fair query above, so a
    concrete observation backend reads probability [1/2] from it. *)
Theorem von_neumann_true_reply_probability_half :
  exists query,
    @next_event_query coin_serviceE EnumQ MF
      FI
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega bool
      (@accepts_true_reply) vn_after_request query /\
    @sem_lift MF
      FI bool bool eq
      direct_true_reply_query query.
Proof.
  eapply peutt_preserves_next_event_query.
  - eapply peutt_sym. exact after_request_peutt.
  - exact direct_after_request_true_reply_query.
Qed.

(** A genuine two-event cylinder.  A selector both recognizes a dependent
    event and supplies the unique client response used to continue the
    protocol. *)
Definition select_request {X} (e : coin_serviceE X) : option X :=
  match e in coin_serviceE X0 return option X0 with
  | CoinRequest => Some ServiceTT
  | CoinReply _ => None
  end.

Definition select_true_reply {X} (e : coin_serviceE X) : option X :=
  match e in coin_serviceE X0 return option X0 with
  | CoinRequest => None
  | CoinReply b => if b then Some ServiceTT else None
  end.

Definition request_true_reply_trace :
    @finite_interaction_pattern coin_serviceE :=
  cons (@select_request) (cons (@select_true_reply) nil).

Lemma select_request_accepts_request :
  @select_request service_unit CoinRequest = Some ServiceTT.
Proof. reflexivity. Qed.

Lemma selector_accept_true_reply :
  @selector_accept coin_serviceE (@select_true_reply) =
    @accepts_true_reply.
Proof.
  apply functional_extensionality_dep. intro X.
  apply functional_extensionality. intro e. destruct e; cbn.
  - reflexivity.
  - by destruct b.
Qed.

Lemma direct_after_request_true_reply_prefix_query :
  @finite_interaction_query coin_serviceE EnumQ MF
    FreeOmegaObservableSemanticMeasure
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega
    bool
    (cons (@select_true_reply) nil)
    direct_after_request direct_true_reply_query.
Proof.
  apply (proj2 (finite_interaction_query_singleton_iff_next_event_query
    (@select_true_reply) direct_after_request direct_true_reply_query)).
  rewrite selector_accept_true_reply.
  exact direct_after_request_true_reply_query.
Qed.

Lemma direct_request_true_reply_prefix_query :
  @finite_interaction_query coin_serviceE EnumQ MF
    FreeOmegaObservableSemanticMeasure
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega
    bool
    request_true_reply_trace direct_fair_service direct_true_reply_query.
Proof.
  unfold request_true_reply_trace.
  change (@finite_interaction_query coin_serviceE EnumQ MF
    FreeOmegaObservableSemanticMeasure
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (cons (@select_request) (cons (@select_true_reply) nil))
    (Vis CoinRequest (fun _ => direct_after_request))
    direct_true_reply_query).
  eapply finite_interaction_query_vis_match.
  - exact select_request_accepts_request.
  - exact direct_after_request_true_reply_prefix_query.
Qed.

Lemma direct_request_true_reply_sem_coupled_to_fair :
  @sem_lift MF FreeOmegaObservableSemanticMeasure bool bool eq
    (@finite_interaction_sem coin_serviceE EnumQ MF
      FreeOmegaObservableSemanticMeasure
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega bool
      request_true_reply_trace direct_fair_service)
    direct_true_reply_query.
Proof.
  eapply finite_interaction_sem_coupled_to_query.
  exact direct_request_true_reply_prefix_query.
Qed.

(** The unbounded implementation directly satisfies the two-event
    [Request; CoinReply true] cylinder.  Its witness is coupled to the same
    explicit fair measure whose true mass is [1/2]. *)
Theorem von_neumann_request_true_reply_probability_half :
  exists query,
    @finite_interaction_query coin_serviceE EnumQ MF
      FreeOmegaObservableSemanticMeasure
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega
      bool
      request_true_reply_trace von_neumann_service query /\
    @sem_lift MF
      FreeOmegaObservableSemanticMeasure bool bool eq
      direct_true_reply_query query.
Proof.
  eapply peutt_preserves_finite_interaction_query.
  - eapply peutt_sym.
    exact interactive_von_neumann_service_equivalent.
  - exact direct_request_true_reply_prefix_query.
Qed.

(** Paper-facing numeric statement: all FreeOmega witnesses and coupling
    plumbing are hidden behind the concrete EnumQ trace-probability API. *)
Theorem von_neumann_request_true_reply_trace_probability :
  Prₜ[ von_neumann_service | request_true_reply_trace ] = (1 / 2 : rat).
Proof.
  destruct von_neumann_request_true_reply_probability_half
    as [query [Hquery Hlift]].
  eapply enumQ_finite_interaction_probability_intro
    with (query := query) (representative := direct_true_reply_query)
      (out := vn_fair).
  - exact Hquery.
  - exact Hlift.
  - exact direct_true_reply_query_denotes_fair.
  - unfold enumQ_bool_indicator, indicator.
    exact direct_true_reply_probability_half.
Qed.

Theorem von_neumann_request_true_reply_sem_preserved :
  @sem_lift MF FreeOmegaObservableSemanticMeasure bool bool eq
    (@finite_interaction_sem coin_serviceE EnumQ MF
      FreeOmegaObservableSemanticMeasure
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega bool
      request_true_reply_trace direct_fair_service)
    (@finite_interaction_sem coin_serviceE EnumQ MF
      FreeOmegaObservableSemanticMeasure
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega bool
      request_true_reply_trace von_neumann_service).
Proof.
  eapply peutt_preserves_finite_interaction_sem.
  eapply peutt_sym.
  exact interactive_von_neumann_service_equivalent.
Qed.

(** A non-matching cylinder fails at the first event: the service initially
    offers [CoinRequest], not a reply. *)
Lemma direct_reply_first_prefix_rejected :
  @finite_interaction_query coin_serviceE EnumQ MF
    FreeOmegaObservableSemanticMeasure
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega
    bool
    (cons (@select_true_reply) nil)
    direct_fair_service (sem_ret false).
Proof.
  change (@finite_interaction_query coin_serviceE EnumQ MF
    FreeOmegaObservableSemanticMeasure
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (cons (@select_true_reply) nil)
    (Vis CoinRequest (fun _ => direct_after_request)) (sem_ret false)).
  eapply (@finite_interaction_query_vis_reject
    coin_serviceE EnumQ MF
    FreeOmegaObservableSemanticMeasure
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaObservableSemanticMeasureBindLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega
    FreeOmegaObservableSemanticOmegaLaws
    FreeOmegaObservableSemanticMeasureAEKleisliLaws
    FreeOmegaObservableSemanticOmegaCofinalityLaws
    bool service_unit (@select_true_reply) nil CoinRequest
    (fun _ => direct_after_request)).
  reflexivity.
Qed.

(** This is an infinite visible behavior, not a terminating sampler theorem:
    both roots expose [CoinRequest], both replies recurse to the original
    service, and the proof above closes that recursive continuation only via
    [peutt_coinduction_upto_bind].  The implementation nevertheless uses
    the genuinely unbounded AST certificate [service_von_neumann_ast] between
    every request and reply. *)
