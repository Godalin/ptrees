Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Logic.FunctionalExtensionality Program.Equality.
From mathcomp Require Import ssreflect ssralg rat.
From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import RatSubTypes DiscreteMC TwoLevelMeasure
  TwoLevelMeasureEnum FreeOmegaMeasure MeasureIteration EnumBindFacts.
From PTree.Prob Require Import EnumMap MeasureIterationEnum.
From PTree.Eq Require Import ShallowNew PrimitiveStableHitting UnifiedFrontier
  OperationalProbabilisticPTS
  ProbabilisticEutt
  OperationalProbabilisticPTSFreeOmega.
From PTree.Examples Require Import VonNeumannUnbounded OperationalVonNeumann.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import EnumMap.
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

Definition publish (b : bool) (next : ptree coin_serviceE Enum bool) :
    ptree coin_serviceE Enum bool :=
  Vis (CoinReply b) (fun _ => next).

(** One request is followed by a closed sampler and one visible reply. *)
Definition serve_round (sampler : ptree coin_serviceE Enum bool)
    (next : ptree coin_serviceE Enum bool) :
    ptree coin_serviceE Enum bool :=
  Vis CoinRequest (fun _ =>
    PTree.bind sampler (fun b => publish b next)).

(** The recursive call is guarded by the request [Vis]. *)
CoFixpoint von_neumann_service : ptree coin_serviceE Enum bool :=
  serve_round von_neumann_third_in von_neumann_service.

CoFixpoint direct_fair_service : ptree coin_serviceE Enum bool :=
  serve_round direct_fair_in direct_fair_service.

Lemma observe_von_neumann_service :
  observe von_neumann_service =
  VisF CoinRequest (fun _ =>
    PTree.bind von_neumann_third_in
      (fun b => publish b von_neumann_service)).
Proof. reflexivity. Qed.

Lemma observe_direct_fair_service :
  observe direct_fair_service =
  VisF CoinRequest (fun _ =>
    PTree.bind direct_fair_in
      (fun b => publish b direct_fair_service)).
Proof. reflexivity. Qed.

Local Notation MF := (FreeOmega Enum).
Local Notation service_head :=
  (frontier_head coin_serviceE Enum bool).

Definition service_head_value (h : service_head) : bool :=
  match h with
  | FHRet b => b
  | @FHVis _ _ _ X e k => false
  end.

Definition service_vn_after (next : unit + bool) :
    ptree coin_serviceE Enum bool :=
  match next with
  | inl u => Tau (PTree.iter vn_step_in u)
  | inr b => Ret b
  end.

Definition service_vn_second (b1 : bool) :
    ptree coin_serviceE Enum bool :=
  PTree.bind
    (Prob vn_biased_coin
      (fun b2 => Ret (vn_round_result b1 b2)))
    service_vn_after.

Lemma service_vn_observe :
  observe (@von_neumann_third_in coin_serviceE) =
  ProbF vn_biased_coin service_vn_second.
Proof.
  unfold von_neumann_third_in.
  pose proof (unfold_aloop_ (@vn_step_in coin_serviceE) tt) as Hunfold.
  rewrite (observing_observe Hunfold) observe_bind.
  assert (Hstep : observe (@vn_step_in coin_serviceE tt) =
    ProbF vn_biased_coin (fun b1 =>
      Prob vn_biased_coin
        (fun b2 => Ret (vn_round_result b1 b2)))) by reflexivity.
  rewrite Hstep. reflexivity.
Qed.

Lemma service_vn_second_observe b1 :
  observe (service_vn_second b1) =
  ProbF vn_biased_coin (fun b2 =>
    PTree.bind (Ret (vn_round_result b1 b2)) service_vn_after).
Proof.
  unfold service_vn_second. rewrite observe_bind. reflexivity.
Qed.

Definition service_vn_hitting (fuel : nat) : MF service_head :=
  operational_hitting_approx (MF := MF) fuel
    (observe (@von_neumann_third_in coin_serviceE)).

Lemma service_vn_hitting_three fuel :
  service_vn_hitting (S (S (S fuel))) =
  FOSample vn_biased_coin (fun b1 =>
    FOSample vn_biased_coin (fun b2 =>
      match vn_round_result b1 b2 with
      | inl _ => service_vn_hitting fuel
      | inr b => FORet (FHRet b)
      end)).
Proof.
  unfold service_vn_hitting. rewrite service_vn_observe.
  cbn [operational_hitting_approx operational_kernel
    operational_target_approx stable_hitting_approx stable_target_approx
    ptree_primitive_kernel sem_bind sem_ret mixed_bind free_omega_bind
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticMeasureInterface
    FreeOmegaSemanticMeasureInterface].
  f_equal. apply functional_extensionality. intro b1.
  rewrite service_vn_second_observe.
  cbn [operational_kernel operational_target_approx stable_target_approx
    ptree_primitive_kernel sem_bind sem_ret mixed_bind free_omega_bind
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticMeasureInterface
    FreeOmegaSemanticMeasureInterface].
  f_equal. apply functional_extensionality. intro b2.
  rewrite observe_bind.
  destruct (vn_round_result b1 b2) as [u|b]; [destruct u|]; reflexivity.
Qed.

Lemma service_vn_hitting_zero_observes :
  free_omega_observes service_head_value
    (service_vn_hitting 0) (sem_zero : Enum bool).
Proof.
  unfold service_vn_hitting. rewrite service_vn_observe.
  change (free_omega_observes service_head_value
    (FOSample vn_biased_coin (fun _ => FOZero)) (nil : Enum bool)).
  rewrite <- (enum_bind_nil (A := bool) bool vn_biased_coin).
  constructor. intro b. constructor.
Qed.

Lemma service_vn_hitting_rounds_observes rounds :
  free_omega_observes service_head_value
    (service_vn_hitting (operational_vn_raw_schedule rounds))
    (meas_iter_approx rounds (fun _ : unit => vn_transition) tt).
Proof.
  induction rounds as [|rounds IH].
  - exact service_vn_hitting_zero_observes.
  - cbn [operational_vn_raw_schedule].
    rewrite service_vn_hitting_three.
    assert (Hout :
      meas_iter_approx (S rounds) (fun _ : unit => vn_transition) tt =
      bind_Enum vn_biased_coin (fun b1 =>
        bind_Enum vn_biased_coin (fun b2 =>
          match vn_round_result b1 b2 with
          | inl _ => meas_iter_approx rounds
              (fun _ : unit => vn_transition) tt
          | inr b => ret_Enum b
          end))).
    { cbn [meas_iter_approx].
      change (bind_Enum vn_transition (fun next =>
        match next with
        | inl i' => meas_iter_approx rounds
            (fun _ : unit => vn_transition) i'
        | inr b => ret_Enum b
        end) =
        bind_Enum vn_biased_coin (fun b1 =>
          bind_Enum vn_biased_coin (fun b2 =>
            match vn_round_result b1 b2 with
            | inl _ => meas_iter_approx rounds
                (fun _ : unit => vn_transition) tt
            | inr b => ret_Enum b
            end))).
      rewrite <- vn_round_measure_eq. unfold vn_round_measure.
      rewrite bind_Enum_assoc.
      apply bind_Enum_ext=> b1. rewrite bind_Enum_assoc.
      apply bind_Enum_ext=> b2.
      rewrite operational_vn_bind_ret_eq.
      destruct (vn_round_result b1 b2) as [u|b];
        [destruct u|]; reflexivity. }
    rewrite Hout. constructor. intro b1.
    constructor. intro b2.
    destruct (vn_round_result b1 b2) as [u|b].
    + destruct u. exact IH.
    + constructor.
Qed.

Lemma service_vn_chains_cofinal :
  free_omega_chains_cofinal eq service_vn_hitting
    (fun rounds =>
      service_vn_hitting (operational_vn_raw_schedule rounds)).
Proof.
  split.
  - intro fuel. exists fuel. apply free_operational_hitting_mono.
    exact (operational_vn_raw_schedule_ge fuel).
  - intro rounds. exists (operational_vn_raw_schedule rounds).
    apply free_omega_approx_refl. intro h. reflexivity.
Qed.

Definition service_vn_heads : MF service_head :=
  FOLub (fun rounds =>
    service_vn_hitting (operational_vn_raw_schedule rounds)).

Lemma service_vn_heads_observes :
  free_omega_observes service_head_value service_vn_heads vn_fair.
Proof.
  unfold service_vn_heads. eapply FOOObserveLub.
  - exact service_vn_hitting_rounds_observes.
  - exact vn_iteration_converges.
Qed.

Lemma service_vn_weak :
  @operational_weak coin_serviceE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (@von_neumann_third_in coin_serviceE)) service_vn_heads.
Proof.
  unfold operational_weak, service_vn_heads, service_vn_hitting.
  cbn. apply FOQLSym. eapply FOQLMono.
  - apply FOQLCofinal. exact service_vn_chains_cofinal.
  - intros x y ->. reflexivity.
Qed.

Lemma service_vn_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface _ service_vn_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, service_head_value, vn_fair.
  split; [exact service_vn_heads_observes|exact vn_fair_total].
Qed.

Theorem service_von_neumann_ast :
  @operational_ast_weak coin_serviceE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (@von_neumann_third_in coin_serviceE)) service_vn_heads.
Proof. split; [exact service_vn_weak|exact service_vn_heads_total]. Qed.

Definition service_direct_heads : MF service_head :=
  @mixed_bind Enum MF FreeOmegaMixedMeasureInterface bool service_head
    vn_fair
    (fun b => @sem_ret MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface)) service_head (FHRet b)).

Definition service_direct_observation : Enum bool :=
  @sem_bind Enum Enum_SemanticMeasureInterface _ _ vn_fair
    (fun b => @sem_ret Enum Enum_SemanticMeasureInterface bool b).

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
  change (bind_Enum vn_fair (fun b => ret_Enum b) = vn_fair).
  rewrite bind_ret_emap. apply emap_id.
Qed.

Lemma service_direct_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface _ service_direct_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, service_head_value, service_direct_observation.
  split; [exact service_direct_heads_observes|].
  rewrite service_direct_observation_eq. exact vn_fair_total.
Qed.

Theorem service_direct_fair_ast :
  @operational_ast_weak coin_serviceE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (@direct_fair_in coin_serviceE)) service_direct_heads.
Proof.
  assert (Hobserve : observe (@direct_fair_in coin_serviceE) =
    ProbF vn_fair (fun b => Ret b)) by reflexivity.
  rewrite Hobserve.
  eapply operational_ast_weak_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. split.
    + apply operational_weak_ret.
    + apply free_omega_observable_total_intro.
      exists bool, service_head_value,
        (@sem_ret Enum Enum_SemanticMeasureInterface bool b).
      split; [constructor|].
      change (meas_total (ret_Enum b)).
      change (enum_expect (fun _ : bool => (1 : rat)) (ret_Enum b) =
        (1 : rat)).
      rewrite enum_expect_ret. reflexivity.
  - exact service_direct_heads_total.
Qed.

Definition service_head_is_ret (h : service_head) : Prop :=
  match h with
  | FHRet _ => True
  | @FHVis _ _ _ X e k => False
  end.

Lemma service_vn_hitting_rounds_ret_only rounds :
  free_omega_ae service_head_is_ret
    (service_vn_hitting (operational_vn_raw_schedule rounds)).
Proof.
  induction rounds as [|rounds IH].
  - unfold service_vn_hitting. rewrite service_vn_observe.
    cbn [operational_vn_raw_schedule operational_hitting_approx
      stable_hitting_approx ptree_primitive_kernel mixed_bind sem_bind
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticMeasureInterface
      FreeOmegaSemanticMeasureInterface stable_target_approx].
    eapply FOAESample with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros b _. constructor.
  - cbn [operational_vn_raw_schedule].
    rewrite service_vn_hitting_three.
    eapply FOAESample with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros b1 _. eapply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros b2 _. destruct (vn_round_result b1 b2) as [u|b].
        -- destruct u. exact IH.
        -- constructor. exact I.
Qed.

Lemma service_vn_heads_ret_only :
  free_omega_ae service_head_is_ret service_vn_heads.
Proof.
  unfold service_vn_heads. constructor.
  exact service_vn_hitting_rounds_ret_only.
Qed.

Lemma service_direct_heads_ret_only :
  free_omega_ae service_head_is_ret service_direct_heads.
Proof.
  unfold service_direct_heads.
  eapply FOAESample with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. constructor. exact I.
Qed.

Definition service_head_value_rel (h1 h2 : service_head) : Prop :=
  service_head_value h1 = service_head_value h2.

Lemma service_head_value_support_lift :
  free_omega_support_lift service_head_value_rel
    service_vn_heads service_direct_heads.
Proof.
  unfold free_omega_support_lift. split.
  - intros P HP. unfold service_vn_heads in HP.
    dependent destruction HP. specialize (H 1%nat).
    cbn [operational_vn_raw_schedule] in H.
    rewrite service_vn_hitting_three in H.
    pose proof (free_omega_ae_sample_inv H) as Hfirst.
    assert (Hfirst_false : free_omega_ae P
        (FOSample vn_biased_coin (fun b2 =>
          match vn_round_result false b2 with
          | inl _ => service_vn_hitting 0
          | inr b => FORet (FHRet b)
          end))).
    { apply Hfirst with (p := vn_one_third).
      - cbn. auto.
      - cbn. discriminate. }
    assert (Hfirst_true : free_omega_ae P
        (FOSample vn_biased_coin (fun b2 =>
          match vn_round_result true b2 with
          | inl _ => service_vn_hitting 0
          | inr b => FORet (FHRet b)
          end))).
    { apply Hfirst with (p := vn_two_thirds).
      - cbn. auto.
      - cbn. discriminate. }
    pose proof (free_omega_ae_sample_inv Hfirst_false) as Hsecond_false.
    pose proof (free_omega_ae_sample_inv Hfirst_true) as Hsecond_true.
    assert (HPfalse : P (FHRet false)).
    { specialize (Hsecond_false vn_two_thirds true).
      cbn in Hsecond_false.
      pose proof (Hsecond_false (or_intror (or_introl Logic.eq_refl))
        ltac:(cbn; discriminate)) as Hr.
      dependent destruction Hr. exact H0. }
    assert (HPtrue : P (FHRet true)).
    { specialize (Hsecond_true vn_one_third false).
      cbn in Hsecond_true.
      pose proof (Hsecond_true (or_introl Logic.eq_refl)
        ltac:(cbn; discriminate)) as Hr.
      dependent destruction Hr. exact H0. }
    unfold service_direct_heads, mixed_bind,
      FreeOmegaMixedMeasureInterface.
    eapply FOAESample with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros b _. constructor. exists (FHRet b). split.
      * reflexivity.
      * destruct b; assumption.
  - intros Q HQ.
    unfold service_direct_heads, mixed_bind,
      FreeOmegaMixedMeasureInterface in HQ.
    pose proof (free_omega_ae_sample_inv HQ) as Hfair.
    assert (HQfalse : Q (FHRet false)).
    { specialize (Hfair one_div_two false). cbn in Hfair.
      pose proof (Hfair (or_introl Logic.eq_refl)
        ltac:(cbn; discriminate)) as Hr.
      dependent destruction Hr. exact H. }
    assert (HQtrue : Q (FHRet true)).
    { specialize (Hfair one_div_two true). cbn in Hfair.
      pose proof (Hfair (or_intror (or_introl Logic.eq_refl))
        ltac:(cbn; discriminate)) as Hr.
      dependent destruction Hr. exact H. }
    eapply free_omega_ae_mono; [|exact service_vn_heads_ret_only].
    intros h Hret. destruct h as [b|X e k]; cbn in Hret.
    + exists (FHRet b). split; [reflexivity|].
      destruct b; assumption.
    + contradiction.
Qed.

Lemma service_vn_direct_heads_lift
    (sim : ptree coin_serviceE Enum bool ->
      ptree coin_serviceE Enum bool -> Prop) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _ _
    (frontier_head_rel eq sim)
    service_vn_heads service_direct_heads.
Proof.
  eapply FOQLAERestrict with
    (T := service_head_value_rel)
    (P := service_head_is_ret) (Q := service_head_is_ret).
  - eapply FOQLObserve with
      (obsA := service_head_value)
      (obsB := service_head_value)
      (outA := vn_fair)
      (outB := service_direct_observation)
      (S := eq).
    + exact service_vn_heads_observes.
    + exact service_direct_heads_observes.
    + rewrite service_direct_observation_eq.
      apply sem_lift_refl. intro b. reflexivity.
    + intros h1 h2 Hvalue. exact Hvalue.
    + exact service_head_value_support_lift.
  - exact service_vn_heads_ret_only.
  - exact service_direct_heads_ret_only.
  - intros h1 h2 [Hvalue [Hret1 Hret2]].
    destruct h1 as [b1|X e1 k1]; [|contradiction].
    destruct h2 as [b2|Y e2 k2]; [|contradiction].
    unfold service_head_value_rel in Hvalue. cbn in Hvalue.
    subst b2. constructor. reflexivity.
Qed.

Theorem service_sampler_equivalent :
  @probabilistic_eutt coin_serviceE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool bool eq
    von_neumann_third_in direct_fair_in.
Proof.
  eapply probabilistic_eutt_of_hitting_lift.
  - exact (proj1 service_von_neumann_ast).
  - exact (proj1 service_direct_fair_ast).
  - exact (service_vn_direct_heads_lift _).
Qed.

(** A finite service round is a congruence.  The infinite theorem below
    instead retains its recursive continuation in an explicit coinduction
    candidate. *)
Lemma serve_round_congruence
    (sampler1 sampler2 : ptree coin_serviceE Enum bool)
    (next1 next2 : ptree coin_serviceE Enum bool)
    (Hsampler :
      @probabilistic_eutt coin_serviceE Enum MF
        (FreeOmegaObservableSemanticMeasureInterface
          (NI := Enum_SemanticMeasureInterface)
          (NO := Enum_SemanticOmegaInterface))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface bool bool eq
        sampler1 sampler2)
    (Hnext :
      @probabilistic_eutt coin_serviceE Enum MF
        (FreeOmegaObservableSemanticMeasureInterface
          (NI := Enum_SemanticMeasureInterface)
          (NO := Enum_SemanticOmegaInterface))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface bool bool eq
        next1 next2) :
  @probabilistic_eutt coin_serviceE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool bool eq
    (serve_round sampler1 next1) (serve_round sampler2 next2).
Proof.
  unfold serve_round.
  apply probabilistic_eutt_vis. intros [].
  eapply free_probabilistic_eutt_bind.
  - exact Hsampler.
  - intros b1 b2 ->. unfold publish.
    apply probabilistic_eutt_vis. intros []. exact Hnext.
Qed.

Local Definition service_kernel {R} :
    ptree' coin_serviceE Enum R ->
    MF (stable_target (ptree' coin_serviceE Enum R)
      (frontier_head coin_serviceE Enum R)) :=
  @ptree_primitive_kernel coin_serviceE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface R.

Local Definition service_stable_rel {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree' coin_serviceE Enum R1 ->
      ptree' coin_serviceE Enum R2 -> Prop) :=
  @ptree_stable_head_rel coin_serviceE Enum R1 R2 RR sim.

Local Notation service_hitting :=
  (@operational_weak coin_serviceE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface
    bool).

Local Definition service_lift {A B} (R : A -> B -> Prop)
    (mu : MF A) (nu : MF B) : Prop :=
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    A B R mu nu.

Definition vn_after_request : ptree coin_serviceE Enum bool :=
  PTree.bind von_neumann_third_in
    (fun b => publish b von_neumann_service).

Definition direct_after_request : ptree coin_serviceE Enum bool :=
  PTree.bind direct_fair_in
    (fun b => publish b direct_fair_service).

Definition vn_reply_front (b : bool) :
    MF (frontier_head coin_serviceE Enum bool) :=
  sem_ret (FHVis (CoinReply b)
    (fun _ => von_neumann_service)).

Definition direct_reply_front (b : bool) :
    MF (frontier_head coin_serviceE Enum bool) :=
  sem_ret (FHVis (CoinReply b)
    (fun _ => direct_fair_service)).

Local Opaque von_neumann_service direct_fair_service
  service_vn_heads service_direct_heads.

Definition vn_after_request_heads :
    MF (frontier_head coin_serviceE Enum bool) :=
  free_omega_bind service_vn_heads
    (frontier_head_ret_bind_front vn_reply_front).

Definition direct_after_request_heads :
    MF (frontier_head coin_serviceE Enum bool) :=
  free_omega_bind service_direct_heads
    (frontier_head_ret_bind_front direct_reply_front).

Lemma vn_after_request_weak :
  service_hitting
    (observe vn_after_request) vn_after_request_heads.
Proof.
  unfold vn_after_request, vn_after_request_heads.
  eapply free_stable_hitting_weak_bind_ret_only.
  - exact service_vn_heads_ret_only.
  - exact service_vn_weak.
  - intro b. unfold publish, vn_reply_front.
    apply (stable_hitting_weak_vis
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)).
Qed.

Lemma direct_after_request_weak :
  service_hitting
    (observe direct_after_request) direct_after_request_heads.
Proof.
  unfold direct_after_request, direct_after_request_heads.
  eapply free_stable_hitting_weak_bind_ret_only.
  - exact service_direct_heads_ret_only.
  - exact (proj1 service_direct_fair_ast).
  - intro b. unfold publish, direct_reply_front.
    apply (stable_hitting_weak_vis
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)).
Qed.

(** The equivalence below is not structural reflexivity.  Immediately after
    the request, the implementation's first primitive sample is the biased
    [1/3,2/3] coin, whereas the specification samples [1/2,1/2]. *)
Lemma service_first_sampling_measure_not_direct :
  vn_biased_coin <> vn_fair.
Proof.
  intro Heq.
  have Hmass := f_equal
    (fun mu => enum_expect
      (fun b => if b then (0 : rat) else (1 : rat)) mu) Heq.
  cbn [vn_biased_coin vn_fair] in Hmass.
  vm_compute in Hmass. discriminate.
Qed.

Definition interactive_service_sim
    (s1 s2 : ptree' coin_serviceE Enum bool) : Prop :=
  (s1 = observe von_neumann_service /\
    s2 = observe direct_fair_service) \/
  (s1 = observe vn_after_request /\
    s2 = observe direct_after_request).

Definition interactive_service_upto
    (s1 s2 : ptree' coin_serviceE Enum bool) : Prop :=
  interactive_service_sim s1 s2 \/
  @probabilistic_eutt_state coin_serviceE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool bool eq s1 s2.

Lemma ISSRoot : interactive_service_sim
    (observe von_neumann_service) (observe direct_fair_service).
Proof. left. split; reflexivity. Qed.

Lemma ISSAfterRequest : interactive_service_sim
    (observe vn_after_request) (observe direct_after_request).
Proof. right. split; reflexivity. Qed.

Lemma after_request_heads_lift :
  service_lift (service_stable_rel eq interactive_service_sim)
    vn_after_request_heads direct_after_request_heads.
Proof.
  unfold service_lift, vn_after_request_heads, direct_after_request_heads.
  eapply free_sem_lift_ret_bind_front.
  - exact (service_vn_direct_heads_lift (fun _ _ => False)).
  - intros b1 b2 ->. unfold vn_reply_front, direct_reply_front.
    apply FOQLStructural. apply FOLRet. apply FHRVis. intros [].
    exact ISSRoot.
Qed.

Lemma after_request_heads_lift_upto :
  service_lift (service_stable_rel eq interactive_service_upto)
    vn_after_request_heads direct_after_request_heads.
Proof.
  eapply sem_lift_mono; [|exact after_request_heads_lift].
  apply frontier_head_rel_mono. intros x1 x2 Hsim.
  left. exact Hsim.
Qed.

Lemma interactive_service_sim_postfixed :
  forall s1 s2, interactive_service_sim s1 s2 ->
    @stable_hitting_match MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface))
      FreeOmegaObservableSemanticOmegaInterface
      (ptree' coin_serviceE Enum bool) (ptree' coin_serviceE Enum bool)
      service_head service_head service_kernel service_kernel
      (@service_stable_rel bool bool eq)
      interactive_service_upto s1 s2.
Proof.
  intros s1 s2 [[-> ->]|[-> ->]].
  - rewrite observe_von_neumann_service observe_direct_fair_service.
    apply stable_hitting_match_vis. intros [].
    left. exact ISSAfterRequest.
  - eapply stable_hitting_match_of_hitting_lift.
    + exact vn_after_request_weak.
    + exact direct_after_request_weak.
    + exact after_request_heads_lift_upto.
Qed.

Theorem interactive_von_neumann_service_equivalent :
  @probabilistic_eutt coin_serviceE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool bool eq
    von_neumann_service direct_fair_service.
Proof.
  eapply probabilistic_eutt_coinduction_upto
    with (sim := interactive_service_sim).
  - exact interactive_service_sim_postfixed.
  - exact ISSRoot.
Qed.

(** This is an infinite visible behavior, not a terminating sampler theorem:
    both roots expose [CoinRequest], both replies recurse to the original
    service, and the proof above closes that recursive continuation only via
    [probabilistic_eutt_coinduction].  The implementation nevertheless uses
    the genuinely unbounded AST certificate [service_von_neumann_ast] between
    every request and reply. *)
