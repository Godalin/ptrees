Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Lia Logic.FunctionalExtensionality Program.Equality.
From mathcomp Require Import ssreflect ssrnat eqtype ssralg ssrnum rat.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import RatSubTypes DiscreteMC FrontierLiftEnum TwoLevelMeasure
  TwoLevelMeasureEnum FreeOmegaMeasure MeasureIteration EnumMap EnumBindFacts.
From PTree.Prob Require Import MeasureIterationEnum.
From PTree.Eq Require Import ShallowNew PrimitiveStableHitting
  OperationalProbabilisticPTS
  OperationalProbabilisticPTSFreeOmega UnifiedFrontier UnifiedFrontierEnumFacts
  ProbabilisticEutt.
From PTree.Examples Require Import VonNeumannUnbounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import EnumMap.
Import GRing.Theory.
Import RatSubTypes.NonnegQNotations.
Local Open Scope ring_scope.

Lemma operational_vn_bind_ret_eq {A B} (x : A) (k : A -> Enum B) :
  bind_Enum (ret_Enum x) k = k x.
Proof.
  cbn [ret_Enum bind_Enum].
  change (List.app (scale_Enum (fst (1, x)) (k x)) nil = k x).
  have Hone : scale_Enum (fst (1, x)) (k x) = k x.
  { induction (k x) as [|[p y] tl IH]=> //=.
    rewrite IH. f_equal. f_equal. apply val_inj.
    exact: mul1r (Qval p). }
  rewrite Hone List.app_nil_r. reflexivity.
Qed.
Local Notation MF := (FreeOmega Enum).
Local Notation vn_head := (frontier_head vnE Enum bool).
Local Notation vn_round_head := (frontier_head vnE Enum (unit + bool)).

Definition operational_vn_head_value (h : vn_head) : bool :=
  match h with
  | FHRet b => b
  | @FHVis _ _ _ X e _ => match e with end
  end.

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

Definition operational_vn_raw_after (next : unit + bool) : ptree vnE Enum bool :=
  match next with
  | inl u => Tau (PTree.iter vn_step u)
  | inr b => Ret b
  end.

Definition operational_vn_raw_second (b1 : bool) : ptree vnE Enum bool :=
  PTree.bind
    (Prob vn_biased_coin (fun b2 => Ret (vn_round_result b1 b2)))
    operational_vn_raw_after.

Lemma operational_vn_raw_observe :
  observe von_neumann_third =
  ProbF vn_biased_coin operational_vn_raw_second.
Proof.
  unfold von_neumann_third.
  pose proof (unfold_aloop_ vn_step tt) as Hunfold.
  rewrite (observing_observe Hunfold). rewrite observe_bind.
  assert (Hstep : observe (vn_step tt) =
    ProbF vn_biased_coin (fun b1 =>
      Prob vn_biased_coin (fun b2 => Ret (vn_round_result b1 b2))))
    by reflexivity.
  rewrite Hstep. reflexivity.
Qed.

Lemma operational_vn_raw_second_observe b1 :
  observe (operational_vn_raw_second b1) =
  ProbF vn_biased_coin (fun b2 =>
    PTree.bind (Ret (vn_round_result b1 b2)) operational_vn_raw_after).
Proof.
  unfold operational_vn_raw_second. rewrite observe_bind. reflexivity.
Qed.

Definition operational_vn_raw_hitting (fuel : nat) : MF vn_head :=
  operational_hitting_approx (MF := MF) fuel
    (observe von_neumann_third).

Lemma operational_vn_raw_hitting_three fuel :
  operational_vn_raw_hitting (Datatypes.S (Datatypes.S (Datatypes.S fuel))) =
  FOSample vn_biased_coin (fun b1 =>
    FOSample vn_biased_coin (fun b2 =>
      match vn_round_result b1 b2 with
      | inl _ => operational_vn_raw_hitting fuel
      | inr b => FORet (FHRet b)
      end)).
Proof.
  unfold operational_vn_raw_hitting. rewrite operational_vn_raw_observe.
  cbn [operational_hitting_approx operational_kernel operational_target_approx
    stable_hitting_approx stable_target_approx ptree_primitive_kernel
    sem_bind sem_ret mixed_bind free_omega_bind FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticMeasureInterface
    FreeOmegaSemanticMeasureInterface].
  f_equal. apply functional_extensionality. intro b1.
  rewrite operational_vn_raw_second_observe.
  cbn [operational_kernel operational_target_approx stable_target_approx
    ptree_primitive_kernel sem_bind sem_ret
    mixed_bind free_omega_bind FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticMeasureInterface FreeOmegaSemanticMeasureInterface].
  f_equal. apply functional_extensionality. intro b2.
  rewrite observe_bind.
  destruct (vn_round_result b1 b2) as [u|b]; [destruct u|]; reflexivity.
Qed.

Lemma operational_vn_raw_hitting_zero_observes :
  free_omega_observes operational_vn_head_value
    (operational_vn_raw_hitting 0) (sem_zero : Enum bool).
Proof.
  unfold operational_vn_raw_hitting. rewrite operational_vn_raw_observe.
  change (free_omega_observes operational_vn_head_value
    (FOSample vn_biased_coin (fun _ => FOZero)) (nil : Enum bool)).
  rewrite <- (enum_bind_nil (A := bool) bool vn_biased_coin).
  constructor. intro b. constructor.
Qed.

Fixpoint operational_vn_raw_schedule (rounds : nat) : nat :=
  match rounds with
  | O => O
  | Datatypes.S rounds' =>
      Datatypes.S (Datatypes.S (Datatypes.S
        (operational_vn_raw_schedule rounds')))
  end.

Lemma operational_vn_raw_hitting_rounds_observes rounds :
  free_omega_observes operational_vn_head_value
    (operational_vn_raw_hitting (operational_vn_raw_schedule rounds))
    (meas_iter_approx rounds (fun _ : unit => vn_transition) tt).
Proof.
  induction rounds as [|rounds IH].
  - exact operational_vn_raw_hitting_zero_observes.
  - cbn [operational_vn_raw_schedule].
    rewrite operational_vn_raw_hitting_three.
    assert (Hout :
      meas_iter_approx (Datatypes.S rounds)
        (fun _ : unit => vn_transition) tt =
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
      destruct (vn_round_result b1 b2) as [u|b]; [destruct u|]; reflexivity. }
    rewrite Hout.
    constructor. intro b1.
    constructor. intro b2.
    destruct (vn_round_result b1 b2) as [u|b].
    + destruct u. exact IH.
    + constructor.
Qed.

Lemma operational_vn_raw_schedule_ge rounds :
  Peano.le rounds (operational_vn_raw_schedule rounds).
Proof.
  induction rounds as [|rounds IH]; [apply le_n|].
  cbn [operational_vn_raw_schedule]. apply le_n_S.
  apply le_S, le_S. exact IH.
Qed.

Lemma operational_vn_raw_chains_cofinal :
  free_omega_chains_cofinal eq operational_vn_raw_hitting
    (fun rounds => operational_vn_raw_hitting
      (operational_vn_raw_schedule rounds)).
Proof.
  split.
  - intro fuel. exists fuel. apply free_operational_hitting_mono.
    exact (operational_vn_raw_schedule_ge fuel).
  - intro rounds. exists (operational_vn_raw_schedule rounds).
    apply free_omega_approx_refl. intro h. reflexivity.
Qed.

Definition operational_vn_raw_limit : MF vn_head :=
  FOLub (fun rounds => operational_vn_raw_hitting
    (operational_vn_raw_schedule rounds)).

Lemma operational_vn_raw_limit_observes :
  free_omega_observes operational_vn_head_value
    operational_vn_raw_limit vn_fair.
Proof.
  unfold operational_vn_raw_limit. eapply FOOObserveLub.
  - exact operational_vn_raw_hitting_rounds_observes.
  - exact vn_iteration_converges.
Qed.

Definition operational_vn_raw_heads : MF vn_head :=
  operational_vn_raw_limit.

Lemma operational_vn_raw_weak :
  @operational_weak vnE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe von_neumann_third) operational_vn_raw_heads.
Proof.
  unfold operational_weak, operational_vn_raw_heads,
    operational_vn_raw_limit, operational_vn_raw_hitting.
  cbn. apply FOQLSym. eapply FOQLMono.
  - apply FOQLCofinal. exact operational_vn_raw_chains_cofinal.
  - intros x y ->. reflexivity.
Qed.

Lemma operational_vn_raw_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface _ operational_vn_raw_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, operational_vn_head_value, vn_fair.
  split; [exact operational_vn_raw_limit_observes|exact vn_fair_total].
Qed.

Theorem operational_von_neumann_raw_ast :
  @operational_ast_weak vnE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe von_neumann_third) operational_vn_raw_heads.
Proof.
  split; [exact operational_vn_raw_weak|exact operational_vn_raw_heads_total].
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
  apply free_omega_observable_total_intro.
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
  apply free_omega_observable_total_intro.
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

Definition operational_vn_compiled_after (next : unit + bool) :
    ptree vnE Enum bool :=
  match next with
  | inl u => Tau (PTree.iter vn_compiled_step u)
  | inr b => Ret b
  end.

Definition operational_vn_compiled_body : ptree vnE Enum bool :=
  PTree.bind (vn_compiled_step tt) operational_vn_compiled_after.

Definition operational_vn_compiled_cont (next : unit + bool) :
    ptree vnE Enum bool :=
  PTree.bind (Ret next) operational_vn_compiled_after.

Lemma operational_vn_compiled_observe_unfold :
  observe operational_vn_compiled = observe operational_vn_compiled_body.
Proof.
  unfold operational_vn_compiled, operational_vn_compiled_body,
    operational_vn_compiled_after.
  exact (observing_observe (unfold_aloop_ vn_compiled_step tt)).
Qed.

Lemma operational_vn_compiled_body_observe :
  observe operational_vn_compiled_body =
  ProbF vn_transition operational_vn_compiled_cont.
Proof.
  unfold operational_vn_compiled_body, vn_compiled_step.
  rewrite observe_bind.
  assert (Hstep : observe
      (Prob vn_transition (fun next : unit + bool => Ret next) :
        ptree vnE Enum (unit + bool)) =
      ProbF vn_transition (fun next => Ret next)) by reflexivity.
  rewrite Hstep. reflexivity.
Qed.

Lemma operational_vn_compiled_cont_observe next :
  observe (operational_vn_compiled_cont next) =
  observe (operational_vn_compiled_after next).
Proof.
  unfold operational_vn_compiled_cont.
  rewrite observe_bind. reflexivity.
Qed.

Lemma operational_vn_limit_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface bool operational_vn_limit.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, id, vn_fair. split.
  - exact operational_vn_limit_observes.
  - exact vn_fair_total.
Qed.

Lemma operational_vn_compiled_frontier :
  @frontier vnE Enum MF Enum_SemanticMeasureInterface
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe operational_vn_compiled) operational_vn_heads.
Proof.
  unfold operational_vn_compiled, operational_vn_heads.
  eapply frontier_iter_intro with
    (transition := fun _ : unit => vn_transition).
  - intro u. unfold vn_compiled_step. cbn.
    rewrite -free_omega_mixed_bindE.
    eapply UFProb with (Good := fun _ => True)
      (front := fun next => FORet (FHRet next)).
    + apply sem_ae_true.
    + intros next _. rewrite -free_omega_observable_sem_retE. apply UFRet.
  - exact operational_vn_mixed_iter.
  - exact operational_vn_limit_total.
Qed.

Definition operational_vn_compiled_after_heads (next : unit + bool) :
    MF vn_head :=
  match next with
  | inl _ => operational_vn_heads
  | inr b => FORet (FHRet b)
  end.

Lemma operational_vn_compiled_after_frontier next :
  @frontier vnE Enum MF Enum_SemanticMeasureInterface
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (operational_vn_compiled_after next))
    (operational_vn_compiled_after_heads next).
Proof.
  destruct next as [u|b].
  - destruct u. unfold operational_vn_compiled_after,
      operational_vn_compiled_after_heads.
    apply UFTau. exact operational_vn_compiled_frontier.
  - unfold operational_vn_compiled_after, operational_vn_compiled_after_heads.
    rewrite -free_omega_observable_sem_retE. apply UFRet.
Qed.

Lemma operational_vn_compiled_cont_frontier next :
  @frontier vnE Enum MF Enum_SemanticMeasureInterface
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (operational_vn_compiled_cont next))
    (operational_vn_compiled_after_heads next).
Proof.
  rewrite operational_vn_compiled_cont_observe.
  apply operational_vn_compiled_after_frontier.
Qed.

Definition operational_vn_compiled_body_heads : MF vn_head :=
  @sem_bind MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _ _
    operational_vn_compiled_round
    (frontier_head_bind_front
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      operational_vn_compiled_after
      operational_vn_compiled_after_heads).

Lemma operational_vn_compiled_body_frontier :
  @frontier vnE Enum MF Enum_SemanticMeasureInterface
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe operational_vn_compiled_body)
    operational_vn_compiled_body_heads.
Proof.
  unfold operational_vn_compiled_body, operational_vn_compiled_body_heads.
  eapply UFBind.
  - unfold operational_vn_compiled_round, vn_compiled_step.
    assert (Hstep : observe
      (Prob vn_transition (fun next : unit + bool => Ret next) :
        ptree vnE Enum (unit + bool)) =
      ProbF vn_transition (fun next => Ret next)) by reflexivity.
    rewrite Hstep.
    cbn [operational_hitting_approx operational_kernel
      operational_target_approx].
    change (@frontier vnE Enum MF Enum_SemanticMeasureInterface
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface (unit + bool)
      (ProbF vn_transition (fun next => Ret next))
      (FOSample vn_transition (fun next => FORet (FHRet next)))).
    rewrite -free_omega_mixed_bindE.
    eapply UFProb with
      (Good := fun _ => True) (front := fun next => FORet (FHRet next)).
    + apply sem_ae_true.
    + intros next _. rewrite -free_omega_observable_sem_retE. apply UFRet.
  - exact operational_vn_compiled_after_frontier.
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
    + apply free_omega_observable_total_intro.
      exists bool, operational_vn_head_value,
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
  - unfold free_omega_support_lift. split.
    + intros P HP.
      apply free_omega_ae_bind_inv in HP.
      unfold operational_vn_limit in HP. dependent destruction HP.
      specialize (H 1%nat).
      unfold operational_vn_iter_approx in H.
      cbn [mixed_iter_approx mixed_bind FreeOmegaMixedMeasureInterface] in H.
      pose proof (free_omega_ae_sample_inv H) as Hround.
      assert (HPfalse : P (FHRet false)).
      { specialize (Hround vn_two_ninths (inr false)). cbn in Hround.
        pose proof (Hround (or_intror (or_introl Logic.eq_refl))
          ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. dependent destruction H0. exact H0. }
      assert (HPtrue : P (FHRet true)).
      { specialize (Hround vn_two_ninths (inr true)). cbn in Hround.
        pose proof (Hround (or_intror (or_intror (or_introl Logic.eq_refl)))
          ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. dependent destruction H0. exact H0. }
      unfold operational_vn_direct_heads.
      eapply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros b _. constructor. exists (FHRet b). split.
        -- constructor. reflexivity.
        -- destruct b; assumption.
    + intros Q HQ.
      unfold operational_vn_direct_heads in HQ.
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
      apply free_omega_ae_mono with (P := fun _ => True).
      * intros h _. destruct h as [b|X e k]; [|destruct e].
        exists (FHRet b). split; [constructor; reflexivity|].
        destruct b; assumption.
      * generalize operational_vn_heads. intro mu. induction mu.
        -- constructor. exact I.
        -- constructor.
        -- eapply FOAESample with (Good := fun _ => True).
           ++ apply (@sem_ae_true Enum Enum_SemanticMeasureInterface
                Enum_SemanticMeasureCoreLaws).
           ++ intros x _. exact (H x).
        -- constructor. exact H.
Qed.

Lemma operational_vn_raw_heads_lift
    (sim : ptree vnE Enum bool -> ptree vnE Enum bool -> Prop) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _ _
    (frontier_head_rel eq sim)
    operational_vn_raw_heads operational_vn_direct_heads.
Proof.
  eapply FOQLObserve with
    (obsA := operational_vn_head_value)
    (obsB := operational_vn_head_value)
    (outA := vn_fair)
    (outB := operational_vn_direct_observation)
    (S := eq).
  - exact operational_vn_raw_limit_observes.
  - exact operational_vn_direct_heads_observes.
  - rewrite operational_vn_direct_observation_eq.
    apply sem_lift_refl. intro b. reflexivity.
  - intros h1 h2 Hvalue.
    destruct h1 as [b1|X e1 k1];
      destruct h2 as [b2|Y e2 k2];
      try destruct e1; try destruct e2.
    cbn in Hvalue. subst b2. constructor. reflexivity.
  - unfold free_omega_support_lift. split.
    + intros P HP. unfold operational_vn_raw_heads,
        operational_vn_raw_limit in HP.
      dependent destruction HP. specialize (H 1%nat).
      cbn [operational_vn_raw_schedule] in H.
      rewrite operational_vn_raw_hitting_three in H.
      pose proof (free_omega_ae_sample_inv H) as Hfirst.
      assert (Hfirst_false : free_omega_ae P
          (FOSample vn_biased_coin (fun b2 =>
            match vn_round_result false b2 with
            | inl _ => operational_vn_raw_hitting 0
            | inr b => FORet (FHRet b)
            end))).
      { apply Hfirst with (p := vn_one_third).
        - cbn. auto.
        - cbn. discriminate. }
      assert (Hfirst_true : free_omega_ae P
          (FOSample vn_biased_coin (fun b2 =>
            match vn_round_result true b2 with
            | inl _ => operational_vn_raw_hitting 0
            | inr b => FORet (FHRet b)
            end))).
      { apply Hfirst with (p := vn_two_thirds).
        - cbn. auto.
        - cbn. discriminate. }
      pose proof (free_omega_ae_sample_inv Hfirst_false) as Hsecond_false.
      pose proof (free_omega_ae_sample_inv Hfirst_true) as Hsecond_true.
      assert (HPfalse : P (FHRet false)).
      { specialize (Hsecond_false vn_two_thirds true). cbn in Hsecond_false.
        pose proof (Hsecond_false (or_intror (or_introl Logic.eq_refl))
          ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. exact H0. }
      assert (HPtrue : P (FHRet true)).
      { specialize (Hsecond_true vn_one_third false). cbn in Hsecond_true.
        pose proof (Hsecond_true (or_introl Logic.eq_refl)
          ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. exact H0. }
      unfold operational_vn_direct_heads.
      eapply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros b _. constructor. exists (FHRet b). split.
        -- constructor. reflexivity.
        -- destruct b; assumption.
    + intros Q HQ. unfold operational_vn_direct_heads in HQ.
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
      apply free_omega_ae_mono with (P := fun _ => True).
      * intros h _. destruct h as [b|X e k]; [|destruct e].
        exists (FHRet b). split; [constructor; reflexivity|].
        destruct b; assumption.
      * generalize operational_vn_raw_heads. intro mu. induction mu.
        -- constructor. exact I.
        -- constructor.
        -- eapply FOAESample with (Good := fun _ => True).
           ++ apply (@sem_ae_true Enum Enum_SemanticMeasureInterface
                Enum_SemanticMeasureCoreLaws).
           ++ intros x _. exact (H x).
        -- constructor. exact H.
Qed.

(** Canonical endpoint: the unbounded retrying implementation and the
    one-step fair coin are compared only at their subprobabilistic
    stable-hitting limits. *)
Theorem probabilistic_eutt_von_neumann_raw_direct :
  @probabilistic_eutt vnE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool bool eq
    von_neumann_third direct_fair.
Proof.
  eapply probabilistic_eutt_of_hitting_lift.
  - apply (proj2 (ptree_primitive_weak_adequate _ _)).
    exact (proj1 operational_von_neumann_raw_ast).
  - apply (proj2 (ptree_primitive_weak_adequate _ _)).
    exact (proj1 operational_vn_direct_ast).
  - exact (operational_vn_raw_heads_lift _).
Qed.

Theorem probabilistic_eutt_von_neumann_compiled_direct :
  @probabilistic_eutt vnE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool bool eq
    operational_vn_compiled direct_fair.
Proof.
  eapply probabilistic_eutt_of_hitting_lift.
  - apply (proj2 (ptree_primitive_weak_adequate _ _)).
    exact (proj1 operational_vn_compiled_ast).
  - apply (proj2 (ptree_primitive_weak_adequate _ _)).
    exact (proj1 operational_vn_direct_ast).
  - exact (operational_vn_heads_lift _).
Qed.

Lemma operational_vn_direct_frontier :
  @frontier vnE Enum MF Enum_SemanticMeasureInterface
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe direct_fair) operational_vn_direct_heads.
Proof.
  unfold direct_fair, operational_vn_direct_heads. cbn.
  rewrite -free_omega_mixed_bindE.
  eapply UFProb with (Good := fun _ => True)
    (front := fun b => FORet (FHRet b)).
  - apply sem_ae_true.
  - intros b _. rewrite -free_omega_observable_sem_retE. apply UFRet.
Qed.
