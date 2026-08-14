Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.

From mathcomp Require Import ssralg rat.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC FrontierLiftEnum TwoLevelMeasure
  TwoLevelMeasureEnum FreeOmegaMeasure MeasureIteration EnumMap.
From PTree.Prob Require Import MeasureIterationEnum.
From PTree.Eq Require Import ShallowNew PrimitiveStableHitting
  OperationalProbabilisticPTS
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
Local Notation vn_round_head := (frontier_head vnE Enum (unit + bool)).

Definition operational_vn_round_head_value (h : vn_round_head) : unit + bool :=
  match h with
  | FHRet next => next
  | @FHVis _ _ _ X e _ => match e with end
  end.

(** Unlike [operational_vn_compiled], this is the source program's actual
    round: its two biased samples remain two separate primitive transitions.
    The lemma below isolates the finite scheduling fact from the later
    unbounded retry argument. *)
Definition operational_vn_raw_round : MF vn_round_head :=
  operational_hitting_approx (MF := MF) 2 (observe (vn_step tt)).

Lemma operational_vn_raw_round_one_observes_zero :
  free_omega_observes operational_vn_round_head_value
    (operational_hitting_approx (MF := MF) 1 (observe (vn_step tt)))
    (sem_zero : Enum (unit + bool)).
Proof.
  assert (Hstep : observe (vn_step tt) =
    ProbF vn_biased_coin (fun b1 =>
      Prob vn_biased_coin (fun b2 => Ret (vn_round_result b1 b2))))
    by reflexivity.
  rewrite Hstep.
  change (free_omega_observes operational_vn_round_head_value
    (FOSample vn_biased_coin (fun _ =>
      FOSample vn_biased_coin (fun _ => FOZero)))
    (nil : Enum (unit + bool))).
  rewrite <- (enum_bind_nil (A := bool) (unit + bool) vn_biased_coin).
  constructor. intro b1.
  rewrite <- (enum_bind_nil (A := bool) (unit + bool) vn_biased_coin).
  constructor. intro b2. constructor.
Qed.

Lemma operational_vn_raw_round_observes :
  free_omega_observes operational_vn_round_head_value
    operational_vn_raw_round vn_transition.
Proof.
  unfold operational_vn_raw_round.
  assert (Hstep : observe (vn_step tt) =
    ProbF vn_biased_coin (fun b1 =>
      Prob vn_biased_coin (fun b2 => Ret (vn_round_result b1 b2))))
    by reflexivity.
  rewrite Hstep.
  change (free_omega_observes operational_vn_round_head_value
    (FOSample vn_biased_coin (fun b1 =>
      FOSample vn_biased_coin (fun b2 =>
        FORet (FHRet (vn_round_result b1 b2))))) vn_transition).
  rewrite <- vn_round_measure_eq.
  unfold vn_round_measure.
  constructor. intro b1.
  constructor. intro b2. constructor.
Qed.

Corollary operational_vn_raw_round_is_transition :
  free_omega_observes operational_vn_round_head_value
    operational_vn_raw_round vn_round_measure.
Proof.
  rewrite vn_round_measure_eq. exact operational_vn_raw_round_observes.
Qed.

Definition operational_vn_compiled_round : MF vn_round_head :=
  operational_hitting_approx (MF := MF) 1
    (observe (vn_compiled_step tt)).

Lemma operational_vn_compiled_round_observes :
  free_omega_observes operational_vn_round_head_value
    operational_vn_compiled_round vn_transition.
Proof.
  unfold operational_vn_compiled_round, vn_compiled_step.
  change (free_omega_observes operational_vn_round_head_value
    (FOSample vn_transition (fun next => FORet (FHRet next)))
    vn_transition).
  assert (Hbind : bind_Enum vn_transition (fun next => ret_Enum next) =
      vn_transition).
  { rewrite bind_ret_emap. apply emap_id. }
  replace vn_transition with
    (bind_Enum vn_transition (fun next => ret_Enum next)) at 2
    by exact Hbind.
  constructor. intro next. constructor.
Qed.

Definition operational_vn_compiled : ptree vnE Enum bool :=
  PTree.iter vn_compiled_step tt.

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

Corollary operational_vn_cofinal :
  @operational_iter_cofinal vnE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface unit bool
    vn_compiled_step (fun _ : unit => vn_transition) tt.
Proof.
  change (@operational_iter_cofinal vnE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface unit bool
    (free_primitive_iter_step (fun _ : unit => vn_transition))
    (fun _ : unit => vn_transition) tt).
  apply free_primitive_iter_cofinal.
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

Corollary operational_vn_compiled_primitive_ast :
  @stable_hitting_ast MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface
    (ptree' vnE Enum bool) vn_head
    (@ptree_primitive_kernel vnE Enum MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface))
      FreeOmegaMixedMeasureInterface bool)
    (observe operational_vn_compiled) operational_vn_heads.
Proof.
  apply (proj2 (ptree_primitive_ast_adequate
    (observe operational_vn_compiled) operational_vn_heads)).
  exact operational_vn_compiled_ast.
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

Lemma operational_vn_heads_lift
    (sim : ptree vnE Enum bool -> ptree vnE Enum bool -> Prop) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _ _
    (frontier_head_rel eq sim)
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
  - exact (operational_vn_heads_lift _).
Qed.

Theorem primitive_von_neumann_compiled_direct_bisim :
  @primitive_ptree_bisim vnE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool bool eq
    operational_vn_compiled direct_fair.
Proof.
  eapply primitive_ptree_bisim_of_ast_lift.
  - exact operational_vn_compiled_ast.
  - exact operational_vn_direct_ast.
  - exact (operational_vn_heads_lift _).
Qed.
