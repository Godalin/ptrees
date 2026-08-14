Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.

Require Import Arith.PeanoNat FunctionalExtensionality Lia.
From mathcomp Require Import ssralg rat.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC FrontierLiftEnum TwoLevelMeasure
  TwoLevelMeasureEnum FreeOmegaMeasure MeasureIteration EnumMap.
From PTree.Prob Require Import MeasureIterationEnum.
From PTree.Eq Require Import ShallowNew OperationalProbabilisticPTS
  OperationalProbabilisticPTSFreeOmega UnifiedFrontier UnifiedFrontierEnumFacts
  UnifiedPWeak.
From PTree.Examples Require Import VonNeumannUnbounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import EnumMap.

Local Notation MF := (FreeOmega Enum).
Local Notation vn_head := (frontier_head vnE Enum bool).
Local Notation vn_head_eq := (@eq vn_head).

Definition operational_vn_compiled : ptree vnE Enum bool :=
  PTree.iter vn_compiled_step tt.

Definition operational_vn_hitting (fuel : nat) :
    MF (frontier_head vnE Enum bool) :=
  operational_hitting_approx (MF := MF) fuel
    (observe operational_vn_compiled).

Definition operational_vn_round_heads (rounds : nat) :
    MF (frontier_head vnE Enum bool) :=
  @operational_iter_round_approx vnE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface unit bool rounds
    (fun _ : unit => vn_transition) tt.

Definition operational_vn_round_branch (rounds : nat)
    (next : unit + bool) : MF (frontier_head vnE Enum bool) :=
  match next with
  | inl _ => operational_vn_round_heads rounds
  | inr b => FORet (FHRet b)
  end.

Definition operational_vn_after (next : unit + bool) : ptree vnE Enum bool :=
  match next with
  | inl _ => Tau operational_vn_compiled
  | inr b => Ret b
  end.

Definition operational_vn_cont (next : unit + bool) : ptree vnE Enum bool :=
  PTree.bind (Ret next) (fun lr =>
    match lr with
    | inl l => Tau (PTree.iter vn_compiled_step l)
    | inr b => Ret b
    end).

Lemma operational_vn_compiled_observe :
  observe operational_vn_compiled =
  ProbF vn_transition operational_vn_cont.
Proof.
  unfold operational_vn_compiled.
  pose proof (unfold_aloop_ vn_compiled_step tt) as Hunfold.
  rewrite (observing_observe Hunfold).
  rewrite observe_bind.
  assert (Hstep : observe (vn_compiled_step tt) =
    ProbF vn_transition (fun next => Ret next)) by reflexivity.
  rewrite Hstep.
  reflexivity.
Qed.

Lemma operational_vn_cont_observe next :
  observe (operational_vn_cont next) = observe (operational_vn_after next).
Proof.
  unfold operational_vn_cont. rewrite observe_bind.
  destruct next as [u|b]; cbn [operational_vn_after].
  - destruct u. reflexivity.
  - reflexivity.
Qed.

Lemma operational_vn_round_heads_zero :
  operational_vn_round_heads 0 = FOZero.
Proof. reflexivity. Qed.

Lemma operational_vn_round_heads_succ rounds :
  operational_vn_round_heads (Datatypes.S rounds) =
  FOSample vn_transition (operational_vn_round_branch rounds).
Proof.
  unfold operational_vn_round_branch, operational_vn_round_heads,
    operational_iter_round_approx.
  cbv [mixed_iter_approx sem_bind mixed_bind
    sem_ret free_omega_bind
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticMeasureInterface].
  f_equal. apply functional_extensionality. intros [u|b].
  - destruct u. reflexivity.
  - reflexivity.
Qed.

Lemma operational_vn_hitting_succ fuel :
  operational_vn_hitting (Datatypes.S fuel) =
  FOSample vn_transition (fun next =>
    operational_hitting_approx (MF := MF) fuel
      (observe (operational_vn_cont next))).
Proof.
  unfold operational_vn_hitting. rewrite operational_vn_compiled_observe.
  reflexivity.
Qed.

Lemma operational_vn_retry_hitting_zero :
  operational_hitting_approx (MF := MF) 0
    (observe (operational_vn_cont (inl tt))) = FOZero.
Proof. rewrite operational_vn_cont_observe. reflexivity. Qed.

Lemma operational_vn_retry_hitting_succ fuel :
  operational_hitting_approx (MF := MF) (Datatypes.S fuel)
    (observe (operational_vn_cont (inl tt))) =
  operational_vn_hitting fuel.
Proof.
  rewrite operational_vn_cont_observe.
  unfold operational_vn_after. reflexivity.
Qed.

Lemma operational_vn_success_hitting fuel b :
  operational_hitting_approx (MF := MF) fuel
    (observe (operational_vn_cont (inr b))) = FORet (FHRet b).
Proof.
  rewrite operational_vn_cont_observe. unfold operational_vn_after.
  assert (Hret : observe (Ret b : ptree vnE Enum bool) = RetF b) by reflexivity.
  rewrite Hret. unfold operational_hitting_approx, operational_kernel.
  cbn. rewrite operational_target_stableE. reflexivity.
Qed.

Lemma operational_vn_hitting_zero_le_round_one :
  free_omega_approx vn_head_eq (operational_vn_hitting 0)
    (operational_vn_round_heads 1).
Proof.
  rewrite operational_vn_round_heads_succ.
  unfold operational_vn_hitting, operational_vn_round_branch.
  rewrite operational_vn_compiled_observe.
  unfold operational_hitting_approx, operational_kernel. cbn.
  eapply FOApproxSample with (S := @eq (unit + bool)).
  - apply sem_lift_refl. intros x. reflexivity.
  - intros x y ->. destruct y as [u|b].
    + constructor.
    + constructor.
Qed.

Lemma operational_vn_approx_trans
    (mu nu xi : MF (frontier_head vnE Enum bool)) :
  free_omega_approx vn_head_eq mu nu ->
  free_omega_approx vn_head_eq nu xi ->
  free_omega_approx vn_head_eq mu xi.
Proof.
  apply free_omega_approx_trans.
Qed.

Lemma operational_vn_hitting_le_round fuel :
  free_omega_approx vn_head_eq (operational_vn_hitting fuel)
    (operational_vn_round_heads (Datatypes.S fuel)).
Proof.
  induction fuel as [|fuel IH].
  - apply operational_vn_hitting_zero_le_round_one.
  - rewrite operational_vn_hitting_succ,
      operational_vn_round_heads_succ.
    eapply FOApproxSample with (S := @eq (unit + bool)).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. destruct y as [u|b].
      * destruct u. cbn [operational_vn_round_branch].
        eapply operational_vn_approx_trans with
          (nu := operational_vn_hitting fuel); [|exact IH].
        destruct fuel as [|fuel].
        -- constructor.
        -- rewrite operational_vn_retry_hitting_succ.
           apply free_operational_hitting_mono.
           apply le_S. apply le_n.
      * rewrite operational_vn_success_hitting.
        apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma operational_vn_round_increasing :
  @sem_increasing MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _
    (fun rounds => @mixed_iter_approx Enum MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface unit bool rounds
      (fun _ => vn_transition) tt).
Proof.
  intro rounds. induction rounds as [|rounds IH].
  - cbn [mixed_iter_approx]. constructor.
  - change (free_omega_approx (@eq bool)
      (mixed_iter_approx rounds (fun _ : unit => vn_transition) tt)
      (mixed_iter_approx (Datatypes.S rounds)
        (fun _ : unit => vn_transition) tt)) in IH.
    cbn [mixed_iter_approx].
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros [u|b] [u'|b'] Heq; inversion Heq; subst.
      * destruct u'. exact IH.
      * apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma operational_vn_round_le_hitting rounds :
  free_omega_approx vn_head_eq
    (operational_vn_round_heads rounds)
    (operational_vn_hitting (2 * rounds)).
Proof.
  induction rounds as [|rounds IH].
  - rewrite operational_vn_round_heads_zero. constructor.
  - rewrite operational_vn_round_heads_succ.
    replace (2 * Datatypes.S rounds) with
      (Datatypes.S (Datatypes.S (2 * rounds))) by lia.
    rewrite operational_vn_hitting_succ.
    eapply FOApproxSample with (S := @eq (unit + bool)).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. destruct y as [u|b].
      * destruct u. cbn [operational_vn_round_branch].
        rewrite operational_vn_retry_hitting_succ. exact IH.
      * rewrite operational_vn_success_hitting.
        apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Theorem operational_vn_approx_cofinal :
  free_operational_iter_approx_cofinal vn_compiled_step
    (fun _ : unit => vn_transition) tt.
Proof.
  split.
  - intro fuel. exists (Datatypes.S fuel).
    exact (operational_vn_hitting_le_round fuel).
  - intro rounds. exists (2 * rounds).
    eapply free_omega_approx_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + exact (operational_vn_round_le_hitting rounds).
Qed.

Corollary operational_vn_cofinal :
  @operational_iter_cofinal vnE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface unit bool
    vn_compiled_step (fun _ : unit => vn_transition) tt.
Proof.
  apply free_operational_iter_cofinal.
  exact operational_vn_approx_cofinal.
Qed.

Definition operational_vn_iter_approx (fuel : nat) : MF bool :=
  @mixed_iter_approx Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface unit bool fuel
    (fun _ : unit => vn_transition) tt.

Definition operational_vn_limit : MF bool :=
  FOLub operational_vn_iter_approx.

Lemma operational_vn_mixed_iter :
  @mixed_iter Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface unit bool
    (fun _ : unit => vn_transition) tt operational_vn_limit.
Proof.
  unfold mixed_iter, operational_vn_limit, operational_vn_iter_approx.
  apply free_omega_qlift_refl. intros x. reflexivity.
Qed.

Lemma operational_vn_approx_observes fuel :
  free_omega_observes (fun b : bool => b)
    (operational_vn_iter_approx fuel)
    (meas_iter_approx fuel (fun _ : unit => vn_transition) tt).
Proof.
  unfold operational_vn_iter_approx. induction fuel as [|fuel IH].
  - constructor.
  - cbn [mixed_iter_approx meas_iter_approx mixed_bind
      FreeOmegaMixedMeasureInterface sem_bind
      Enum_SemanticMeasureInterface].
    change (free_omega_observes (fun b : bool => b)
      (FOSample vn_transition (fun next : unit + bool =>
        match next with
        | inl u => @mixed_iter_approx Enum MF
            (FreeOmegaObservableSemanticMeasureInterface
              (NI := Enum_SemanticMeasureInterface)
              (NO := Enum_SemanticOmegaInterface))
            FreeOmegaMixedMeasureInterface
            FreeOmegaObservableSemanticOmegaInterface unit bool fuel
            (fun _ : unit => vn_transition) u
        | inr b => FORet b
        end))
      (@sem_bind Enum Enum_SemanticMeasureInterface _ _ vn_transition
        (fun next : unit + bool =>
          match next with
          | inl u => meas_iter_approx fuel
              (fun _ : unit => vn_transition) u
          | inr b => @sem_ret Enum Enum_SemanticMeasureInterface bool b
          end))).
    eapply FOOObserveSample with
      (front := fun next : unit + bool =>
        match next with
        | inl u => meas_iter_approx fuel
            (fun _ : unit => vn_transition) u
        | inr b => @sem_ret Enum Enum_SemanticMeasureInterface bool b
        end).
    intros [u|b].
    + destruct u. exact IH.
    + constructor.
Qed.

Lemma operational_vn_limit_observes :
  free_omega_observes (fun b : bool => b)
    operational_vn_limit vn_fair.
Proof.
  unfold operational_vn_limit. eapply FOOObserveLub.
  - exact operational_vn_approx_observes.
  - exact vn_iteration_converges.
Qed.

Definition operational_vn_heads : MF vn_head :=
  @sem_bind MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _ _ operational_vn_limit
    (fun b => @sem_ret MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface)) vn_head (FHRet b)).

Definition operational_vn_direct_heads : MF vn_head :=
  @mixed_bind Enum MF FreeOmegaMixedMeasureInterface bool vn_head vn_fair
    (fun b => @sem_ret MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface)) vn_head (FHRet b)).

Definition operational_vn_direct_observation : Enum bool :=
  @sem_bind Enum Enum_SemanticMeasureInterface _ _ vn_fair
    (fun b => @sem_ret Enum Enum_SemanticMeasureInterface bool b).

Definition operational_vn_head_value (h : vn_head) : bool :=
  match h with
  | FHRet b => b
  | @FHVis _ _ _ X e _ => match e with end
  end.

Lemma operational_vn_heads_observes :
  free_omega_observes operational_vn_head_value
    operational_vn_heads vn_fair.
Proof.
  unfold operational_vn_heads.
  eapply free_omega_observes_bind_ret
    with (obsA := fun b : bool => b).
  - exact operational_vn_limit_observes.
  - intros b. reflexivity.
Qed.

Lemma operational_vn_direct_heads_observes :
  free_omega_observes operational_vn_head_value
    operational_vn_direct_heads operational_vn_direct_observation.
Proof.
  unfold operational_vn_direct_heads, operational_vn_direct_observation.
  eapply FOOObserveSample.
  intro b. constructor.
Qed.

Lemma operational_vn_direct_observation_eq :
  operational_vn_direct_observation = vn_fair.
Proof.
  unfold operational_vn_direct_observation.
  change (bind_Enum vn_fair (fun b => ret_Enum b) = vn_fair).
  rewrite bind_ret_emap. apply emap_id.
Qed.

Lemma operational_vn_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface _ operational_vn_heads.
Proof.
  exists bool, operational_vn_head_value, vn_fair.
  split; [exact operational_vn_heads_observes|exact vn_fair_total].
Qed.

Lemma operational_vn_direct_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface _ operational_vn_direct_heads.
Proof.
  exists bool, operational_vn_head_value, operational_vn_direct_observation.
  split; [exact operational_vn_direct_heads_observes|].
  rewrite operational_vn_direct_observation_eq. exact vn_fair_total.
Qed.

Theorem operational_vn_compiled_ast :
  @operational_ast_weak vnE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe operational_vn_compiled) operational_vn_heads.
Proof.
  unfold operational_vn_compiled, operational_vn_heads.
  eapply operational_ast_weak_iter.
  - exact operational_vn_round_increasing.
  - exact operational_vn_cofinal.
  - exact operational_vn_mixed_iter.
  - exact operational_vn_heads_total.
Qed.

Import GRing.Theory.
Local Open Scope ring_scope.

Theorem operational_vn_direct_ast :
  @operational_ast_weak vnE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe direct_fair) operational_vn_direct_heads.
Proof.
  assert (Hobserve : observe direct_fair =
    ProbF vn_fair (fun b => Ret b)) by reflexivity.
  rewrite Hobserve.
  eapply operational_ast_weak_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. split.
    + apply operational_weak_ret.
    + exists bool, operational_vn_head_value,
        (@sem_ret Enum Enum_SemanticMeasureInterface bool b).
      split; [constructor|].
      change (meas_total (ret_Enum b)).
      change (enum_expect (fun _ : bool => (1 : rat)) (ret_Enum b) =
        (1 : rat)).
      rewrite enum_expect_ret. reflexivity.
  - exact operational_vn_direct_heads_total.
Qed.

Lemma operational_vn_heads_lift :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _ _
    (frontier_head_rel eq
      (@operational_bisim vnE Enum MF
        Enum_SemanticMeasureInterface
        (FreeOmegaObservableSemanticMeasureInterface
          (NI := Enum_SemanticMeasureInterface)
          (NO := Enum_SemanticOmegaInterface))
        Enum_SemanticMeasureCoreLaws
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface bool bool eq))
    operational_vn_heads operational_vn_direct_heads.
Proof.
  eapply FOQLObserve with
    (obsA := operational_vn_head_value)
    (obsB := operational_vn_head_value)
    (outA := vn_fair)
    (outB := operational_vn_direct_observation)
    (S := eq).
  - exact operational_vn_heads_observes.
  - exact operational_vn_direct_heads_observes.
  - rewrite operational_vn_direct_observation_eq.
    apply sem_lift_refl. intros b. reflexivity.
  - intros h1 h2 Hvalue.
    destruct h1 as [b1|X e1 k1];
      destruct h2 as [b2|Y e2 k2];
      try destruct e1; try destruct e2.
    cbn in Hvalue. subst b2. constructor. reflexivity.
Qed.

(** The unbounded retrying implementation and the one-step fair sampler
    have different operational shapes and different FreeOmega witnesses.
    Their common low-level observation supplies the stable coupling. *)
Theorem operational_von_neumann_compiled_direct_bisim :
  @operational_bisim vnE Enum MF
    Enum_SemanticMeasureInterface
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    Enum_SemanticMeasureCoreLaws
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool bool eq
    operational_vn_compiled direct_fair.
Proof.
  apply operational_bisim_fold. eapply OPBStable.
  - exact operational_vn_compiled_ast.
  - exact operational_vn_direct_ast.
  - exact operational_vn_heads_lift.
Qed.
