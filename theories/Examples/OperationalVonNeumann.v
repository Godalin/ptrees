Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Lia Logic.FunctionalExtensionality Program.Equality.
From mathcomp Require Import ssreflect ssrnat eqtype ssralg ssrnum rat.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import RatSubTypes DiscreteMC FrontierLiftEnum TwoLevelMeasure
  TwoLevelMeasureEnum FreeOmegaMeasure MeasureIteration EnumMap EnumBindFacts.
From PTree.Prob Require Import MeasureIterationEnum.
From PTree.Eq Require Import Shallow PrimitiveStableHitting
  PTreeKernel
  FreeOmega UnifiedFrontier
  PEutt.
From PTree.Examples Require Import VonNeumannUnbounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import EnumMap.
Import GRing.Theory.
Import RatSubTypes.NonnegQNotations.
Local Open Scope ring_scope.

Lemma ptree_vn_bind_ret_eq {A B} (x : A) (k : A -> Enum B) :
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
Local Notation vn_head := (stable_head vnE Enum bool).
Local Notation vn_round_head := (stable_head vnE Enum (unit + bool)).

Definition ptree_vn_head_value (h : vn_head) : bool :=
  match h with
  | FHRet b => b
  | @FHVis _ _ _ X e _ => match e with end
  end.

Definition ptree_vn_round_head_value (h : vn_round_head) : unit + bool :=
  match h with
  | FHRet next => next
  | @FHVis _ _ _ X e _ => match e with end
  end.

(** Unlike [ptree_vn_compiled], this is the source program's actual
    round: its two biased samples remain two separate primitive transitions.
    The lemma below isolates the finite scheduling fact from the later
    unbounded retry argument. *)
Definition ptree_vn_raw_round : MF vn_round_head :=
  ptree_hitting_approx (MF := MF) 2 (observe (vn_step tt)).

Lemma ptree_vn_raw_round_one_observes_zero :
  free_omega_observes ptree_vn_round_head_value
    (ptree_hitting_approx (MF := MF) 1 (observe (vn_step tt)))
    (sem_zero : Enum (unit + bool)).
Proof.
  assert (Hstep : observe (vn_step tt) =
    ProbF vn_biased_coin (fun b1 =>
      Prob vn_biased_coin (fun b2 => Ret (vn_round_result b1 b2))))
    by reflexivity.
  rewrite Hstep.
  change (free_omega_observes ptree_vn_round_head_value
    (FOSample vn_biased_coin (fun _ =>
      FOSample vn_biased_coin (fun _ => FOZero)))
    (nil : Enum (unit + bool))).
  rewrite <- (enum_bind_nil (A := bool) (unit + bool) vn_biased_coin).
  constructor. intro b1.
  rewrite <- (enum_bind_nil (A := bool) (unit + bool) vn_biased_coin).
  constructor. intro b2. constructor.
Qed.

Lemma ptree_vn_raw_round_observes :
  free_omega_observes ptree_vn_round_head_value
    ptree_vn_raw_round vn_transition.
Proof.
  unfold ptree_vn_raw_round.
  assert (Hstep : observe (vn_step tt) =
    ProbF vn_biased_coin (fun b1 =>
      Prob vn_biased_coin (fun b2 => Ret (vn_round_result b1 b2))))
    by reflexivity.
  rewrite Hstep.
  change (free_omega_observes ptree_vn_round_head_value
    (FOSample vn_biased_coin (fun b1 =>
      FOSample vn_biased_coin (fun b2 =>
        FORet (FHRet (vn_round_result b1 b2))))) vn_transition).
  rewrite <- vn_round_measure_eq.
  unfold vn_round_measure.
  constructor. intro b1.
  constructor. intro b2. constructor.
Qed.

Corollary ptree_vn_raw_round_is_transition :
  free_omega_observes ptree_vn_round_head_value
    ptree_vn_raw_round vn_round_measure.
Proof.
  rewrite vn_round_measure_eq. exact ptree_vn_raw_round_observes.
Qed.

Definition ptree_vn_compiled_round : MF vn_round_head :=
  ptree_hitting_approx (MF := MF) 1
    (observe (vn_compiled_step tt)).

Lemma ptree_vn_compiled_round_observes :
  free_omega_observes ptree_vn_round_head_value
    ptree_vn_compiled_round vn_transition.
Proof.
  unfold ptree_vn_compiled_round, vn_compiled_step.
  change (free_omega_observes ptree_vn_round_head_value
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

Definition ptree_vn_raw_after (next : unit + bool) : ptree vnE Enum bool :=
  match next with
  | inl u => Tau (PTree.iter vn_step u)
  | inr b => Ret b
  end.

Definition ptree_vn_raw_second (b1 : bool) : ptree vnE Enum bool :=
  PTree.bind
    (Prob vn_biased_coin (fun b2 => Ret (vn_round_result b1 b2)))
    ptree_vn_raw_after.

Lemma ptree_vn_raw_observe :
  observe von_neumann_third =
  ProbF vn_biased_coin ptree_vn_raw_second.
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

Lemma ptree_vn_raw_second_observe b1 :
  observe (ptree_vn_raw_second b1) =
  ProbF vn_biased_coin (fun b2 =>
    PTree.bind (Ret (vn_round_result b1 b2)) ptree_vn_raw_after).
Proof.
  unfold ptree_vn_raw_second. rewrite observe_bind. reflexivity.
Qed.

Definition ptree_vn_raw_hitting (fuel : nat) : MF vn_head :=
  ptree_hitting_approx (MF := MF) fuel
    (observe von_neumann_third).

Lemma ptree_vn_raw_hitting_three fuel :
  ptree_vn_raw_hitting (Datatypes.S (Datatypes.S (Datatypes.S fuel))) =
  FOSample vn_biased_coin (fun b1 =>
    FOSample vn_biased_coin (fun b2 =>
      match vn_round_result b1 b2 with
      | inl _ => ptree_vn_raw_hitting fuel
      | inr b => FORet (FHRet b)
      end)).
Proof.
  unfold ptree_vn_raw_hitting. rewrite ptree_vn_raw_observe.
  cbn [ptree_hitting_approx ptree_primitive_kernel ptree_stable_target_approx
    stable_hitting_approx stable_target_approx ptree_primitive_kernel
    sem_bind sem_ret mixed_bind free_omega_bind FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticMeasure
    FreeOmegaSemanticMeasure].
  f_equal. apply functional_extensionality. intro b1.
  rewrite ptree_vn_raw_second_observe.
  cbn [ptree_primitive_kernel ptree_stable_target_approx stable_target_approx
    ptree_primitive_kernel sem_bind sem_ret
    mixed_bind free_omega_bind FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticMeasure FreeOmegaSemanticMeasure].
  f_equal. apply functional_extensionality. intro b2.
  rewrite observe_bind.
  destruct (vn_round_result b1 b2) as [u|b]; [destruct u|]; reflexivity.
Qed.

Lemma ptree_vn_raw_hitting_zero_observes :
  free_omega_observes ptree_vn_head_value
    (ptree_vn_raw_hitting 0) (sem_zero : Enum bool).
Proof.
  unfold ptree_vn_raw_hitting. rewrite ptree_vn_raw_observe.
  change (free_omega_observes ptree_vn_head_value
    (FOSample vn_biased_coin (fun _ => FOZero)) (nil : Enum bool)).
  rewrite <- (enum_bind_nil (A := bool) bool vn_biased_coin).
  constructor. intro b. constructor.
Qed.

Fixpoint ptree_vn_raw_schedule (rounds : nat) : nat :=
  match rounds with
  | O => O
  | Datatypes.S rounds' =>
      Datatypes.S (Datatypes.S (Datatypes.S
        (ptree_vn_raw_schedule rounds')))
  end.

Lemma ptree_vn_raw_hitting_rounds_observes rounds :
  free_omega_observes ptree_vn_head_value
    (ptree_vn_raw_hitting (ptree_vn_raw_schedule rounds))
    (meas_iter_approx rounds (fun _ : unit => vn_transition) tt).
Proof.
  induction rounds as [|rounds IH].
  - exact ptree_vn_raw_hitting_zero_observes.
  - cbn [ptree_vn_raw_schedule].
    rewrite ptree_vn_raw_hitting_three.
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
      rewrite ptree_vn_bind_ret_eq.
      destruct (vn_round_result b1 b2) as [u|b]; [destruct u|]; reflexivity. }
    rewrite Hout.
    constructor. intro b1.
    constructor. intro b2.
    destruct (vn_round_result b1 b2) as [u|b].
    + destruct u. exact IH.
    + constructor.
Qed.

Lemma ptree_vn_raw_schedule_ge rounds :
  Peano.le rounds (ptree_vn_raw_schedule rounds).
Proof.
  induction rounds as [|rounds IH]; [apply le_n|].
  cbn [ptree_vn_raw_schedule]. apply le_n_S.
  apply le_S, le_S. exact IH.
Qed.

Lemma ptree_vn_raw_chains_cofinal :
  free_omega_chains_cofinal eq ptree_vn_raw_hitting
    (fun rounds => ptree_vn_raw_hitting
      (ptree_vn_raw_schedule rounds)).
Proof.
  split.
  - intro fuel. exists fuel. apply ptree_hitting_mono.
    exact (ptree_vn_raw_schedule_ge fuel).
  - intro rounds. exists (ptree_vn_raw_schedule rounds).
    apply free_omega_approx_refl. intro h. reflexivity.
Qed.

Definition ptree_vn_raw_limit : MF vn_head :=
  FOLub (fun rounds => ptree_vn_raw_hitting
    (ptree_vn_raw_schedule rounds)).

Lemma ptree_vn_raw_limit_observes :
  free_omega_observes ptree_vn_head_value
    ptree_vn_raw_limit vn_fair.
Proof.
  unfold ptree_vn_raw_limit. eapply FOOObserveLub.
  - exact ptree_vn_raw_hitting_rounds_observes.
  - exact vn_iteration_converges.
  - intro n. apply ptree_hitting_mono.
    cbn [ptree_vn_raw_schedule]. repeat apply le_S. apply le_n.
Qed.

Definition ptree_vn_raw_heads : MF vn_head :=
  ptree_vn_raw_limit.

Lemma ptree_vn_raw_weak :
  @ptree_stable_hitting vnE Enum MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe von_neumann_third) ptree_vn_raw_heads.
Proof.
  change (free_omega_qlift eq
    (FOLub (fun n => ptree_vn_raw_hitting (ptree_vn_raw_schedule n)))
    (FOLub ptree_vn_raw_hitting)).
  apply FOQLSym. eapply FOQLMono.
  - apply FOQLCofinal.
    + intro n. apply ptree_hitting_mono. apply le_S, le_n.
    + intro n. apply ptree_hitting_mono.
      cbn [ptree_vn_raw_schedule]. repeat apply le_S. apply le_n.
    + exact ptree_vn_raw_chains_cofinal.
  - intros x y ->. reflexivity.
Qed.

Lemma ptree_vn_raw_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticOmega _ ptree_vn_raw_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, ptree_vn_head_value, vn_fair.
  split; [exact ptree_vn_raw_limit_observes|exact vn_fair_total].
Qed.

Theorem ptree_von_neumann_raw_ast :
  @ptree_stable_hitting_ast vnE Enum MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe von_neumann_third) ptree_vn_raw_heads.
Proof.
  split; [exact ptree_vn_raw_weak|exact ptree_vn_raw_heads_total].
Qed.

Definition ptree_vn_compiled : ptree vnE Enum bool :=
  PTree.iter vn_compiled_step tt.

Lemma ptree_vn_round_increasing :
  @sem_increasing MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    (FreeOmegaObservableSemanticOmega
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega)) _
    (fun rounds => @mixed_iter_approx Enum MF
      (FreeOmegaObservableSemanticMeasure
        (NI := Enum_SemanticMeasure)
        (NO := Enum_SemanticOmega))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega unit bool rounds
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

Corollary ptree_vn_cofinal :
  @PTreeKernel.ptree_iter_cofinal vnE Enum MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega unit bool
    vn_compiled_step (fun _ : unit => vn_transition) tt.
Proof.
  change (@PTreeKernel.ptree_iter_cofinal vnE Enum MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega unit bool
    (primitive_iter_step (fun _ : unit => vn_transition))
    (fun _ : unit => vn_transition) tt).
  apply primitive_iter_cofinal.
Qed.

Definition ptree_vn_iter_approx (fuel : nat) : MF bool :=
  @mixed_iter_approx Enum MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega unit bool fuel
    (fun _ : unit => vn_transition) tt.

Definition ptree_vn_limit : MF bool :=
  FOLub ptree_vn_iter_approx.

Lemma ptree_vn_mixed_iter :
  @mixed_iter Enum MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega unit bool
    (fun _ : unit => vn_transition) tt ptree_vn_limit.
Proof.
  unfold mixed_iter, ptree_vn_limit, ptree_vn_iter_approx.
  apply free_omega_qlift_refl. intros x. reflexivity.
Qed.

Lemma ptree_vn_approx_observes fuel :
  free_omega_observes (fun b : bool => b)
    (ptree_vn_iter_approx fuel)
    (meas_iter_approx fuel (fun _ : unit => vn_transition) tt).
Proof.
  unfold ptree_vn_iter_approx. induction fuel as [|fuel IH].
  - constructor.
  - cbn [mixed_iter_approx meas_iter_approx mixed_bind
      FreeOmegaMixedMeasure sem_bind
      Enum_SemanticMeasure].
    change (free_omega_observes (fun b : bool => b)
      (FOSample vn_transition (fun next : unit + bool =>
        match next with
        | inl u => @mixed_iter_approx Enum MF
            (FreeOmegaObservableSemanticMeasure
              (NI := Enum_SemanticMeasure)
              (NO := Enum_SemanticOmega))
            FreeOmegaMixedMeasure
            FreeOmegaObservableSemanticOmega unit bool fuel
            (fun _ : unit => vn_transition) u
        | inr b => FORet b
        end))
      (@sem_bind Enum Enum_SemanticMeasure _ _ vn_transition
        (fun next : unit + bool =>
          match next with
          | inl u => meas_iter_approx fuel
              (fun _ : unit => vn_transition) u
          | inr b => @sem_ret Enum Enum_SemanticMeasure bool b
          end))).
    eapply FOOObserveSample with
      (front := fun next : unit + bool =>
        match next with
        | inl u => meas_iter_approx fuel
            (fun _ : unit => vn_transition) u
        | inr b => @sem_ret Enum Enum_SemanticMeasure bool b
        end).
    intros [u|b].
    + destruct u. exact IH.
    + constructor.
Qed.

Lemma ptree_vn_limit_observes :
  free_omega_observes (fun b : bool => b)
    ptree_vn_limit vn_fair.
Proof.
  unfold ptree_vn_limit. eapply FOOObserveLub.
  - exact ptree_vn_approx_observes.
  - exact vn_iteration_converges.
  - exact ptree_vn_round_increasing.
Qed.

Definition ptree_vn_heads : MF vn_head :=
  @sem_bind MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega)) _ _ ptree_vn_limit
    (fun b => @sem_ret MF
      (FreeOmegaObservableSemanticMeasure
        (NI := Enum_SemanticMeasure)
        (NO := Enum_SemanticOmega)) vn_head (FHRet b)).

Definition ptree_vn_direct_heads : MF vn_head :=
  @mixed_bind Enum MF FreeOmegaMixedMeasure bool vn_head vn_fair
    (fun b => @sem_ret MF
      (FreeOmegaObservableSemanticMeasure
        (NI := Enum_SemanticMeasure)
        (NO := Enum_SemanticOmega)) vn_head (FHRet b)).

Definition ptree_vn_direct_observation : Enum bool :=
  @sem_bind Enum Enum_SemanticMeasure _ _ vn_fair
    (fun b => @sem_ret Enum Enum_SemanticMeasure bool b).

Lemma ptree_vn_heads_observes :
  free_omega_observes ptree_vn_head_value
    ptree_vn_heads vn_fair.
Proof.
  unfold ptree_vn_heads.
  eapply free_omega_observes_bind_ret
    with (obsA := fun b : bool => b).
  - exact ptree_vn_limit_observes.
  - intros b. reflexivity.
Qed.

Lemma ptree_vn_direct_heads_observes :
  free_omega_observes ptree_vn_head_value
    ptree_vn_direct_heads ptree_vn_direct_observation.
Proof.
  unfold ptree_vn_direct_heads, ptree_vn_direct_observation.
  eapply FOOObserveSample.
  intro b. constructor.
Qed.

Lemma ptree_vn_direct_observation_eq :
  ptree_vn_direct_observation = vn_fair.
Proof.
  unfold ptree_vn_direct_observation.
  change (bind_Enum vn_fair (fun b => ret_Enum b) = vn_fair).
  rewrite bind_ret_emap. apply emap_id.
Qed.

Lemma ptree_vn_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticOmega _ ptree_vn_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, ptree_vn_head_value, vn_fair.
  split; [exact ptree_vn_heads_observes|exact vn_fair_total].
Qed.

Lemma ptree_vn_direct_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticOmega _ ptree_vn_direct_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, ptree_vn_head_value, ptree_vn_direct_observation.
  split; [exact ptree_vn_direct_heads_observes|].
  rewrite ptree_vn_direct_observation_eq. exact vn_fair_total.
Qed.

Theorem ptree_vn_compiled_ast :
  @ptree_stable_hitting_ast vnE Enum MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe ptree_vn_compiled) ptree_vn_heads.
Proof.
  unfold ptree_vn_compiled, ptree_vn_heads.
  eapply ptree_stable_hitting_ast_iter.
  - exact ptree_vn_round_increasing.
  - exact ptree_vn_cofinal.
  - exact ptree_vn_mixed_iter.
  - exact ptree_vn_heads_total.
Qed.

Corollary ptree_vn_compiled_primitive_ast :
  @stable_hitting_ast MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticOmega
    (ptree' vnE Enum bool) vn_head
    (@ptree_primitive_kernel vnE Enum MF
      (FreeOmegaObservableSemanticMeasure
        (NI := Enum_SemanticMeasure)
        (NO := Enum_SemanticOmega))
      FreeOmegaMixedMeasure bool)
    (observe ptree_vn_compiled) ptree_vn_heads.
Proof.
  apply (proj2 (ptree_primitive_ast_adequate
    (observe ptree_vn_compiled) ptree_vn_heads)).
  exact ptree_vn_compiled_ast.
Qed.

Definition ptree_vn_compiled_after (next : unit + bool) :
    ptree vnE Enum bool :=
  match next with
  | inl u => Tau (PTree.iter vn_compiled_step u)
  | inr b => Ret b
  end.

Definition ptree_vn_compiled_body : ptree vnE Enum bool :=
  PTree.bind (vn_compiled_step tt) ptree_vn_compiled_after.

Definition ptree_vn_compiled_cont (next : unit + bool) :
    ptree vnE Enum bool :=
  PTree.bind (Ret next) ptree_vn_compiled_after.

Lemma ptree_vn_compiled_observe_unfold :
  observe ptree_vn_compiled = observe ptree_vn_compiled_body.
Proof.
  unfold ptree_vn_compiled, ptree_vn_compiled_body,
    ptree_vn_compiled_after.
  exact (observing_observe (unfold_aloop_ vn_compiled_step tt)).
Qed.

Lemma ptree_vn_compiled_body_observe :
  observe ptree_vn_compiled_body =
  ProbF vn_transition ptree_vn_compiled_cont.
Proof.
  unfold ptree_vn_compiled_body, vn_compiled_step.
  rewrite observe_bind.
  assert (Hstep : observe
      (Prob vn_transition (fun next : unit + bool => Ret next) :
        ptree vnE Enum (unit + bool)) =
      ProbF vn_transition (fun next => Ret next)) by reflexivity.
  rewrite Hstep. reflexivity.
Qed.

Lemma ptree_vn_compiled_cont_observe next :
  observe (ptree_vn_compiled_cont next) =
  observe (ptree_vn_compiled_after next).
Proof.
  unfold ptree_vn_compiled_cont.
  rewrite observe_bind. reflexivity.
Qed.

Lemma ptree_vn_limit_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticOmega bool ptree_vn_limit.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, id, vn_fair. split.
  - exact ptree_vn_limit_observes.
  - exact vn_fair_total.
Qed.

Lemma ptree_vn_compiled_frontier :
  @frontier_certificate vnE Enum MF Enum_SemanticMeasure
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe ptree_vn_compiled) ptree_vn_heads.
Proof.
  unfold ptree_vn_compiled, ptree_vn_heads.
  eapply certificate_iter_intro with
    (transition := fun _ : unit => vn_transition).
  - intro u. unfold vn_compiled_step. cbn.
    rewrite -free_omega_mixed_bindE.
    eapply UFProb with (Good := fun _ => True)
      (front := fun next => FORet (FHRet next)).
    + apply sem_ae_true.
    + intros next _. rewrite -free_omega_observable_sem_retE. apply UFRet.
  - exact ptree_vn_mixed_iter.
  - exact ptree_vn_limit_total.
Qed.

Definition ptree_vn_compiled_after_heads (next : unit + bool) :
    MF vn_head :=
  match next with
  | inl _ => ptree_vn_heads
  | inr b => FORet (FHRet b)
  end.

Lemma ptree_vn_compiled_after_frontier next :
  @frontier_certificate vnE Enum MF Enum_SemanticMeasure
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe (ptree_vn_compiled_after next))
    (ptree_vn_compiled_after_heads next).
Proof.
  destruct next as [u|b].
  - destruct u. unfold ptree_vn_compiled_after,
      ptree_vn_compiled_after_heads.
    apply UFTau. exact ptree_vn_compiled_frontier.
  - unfold ptree_vn_compiled_after, ptree_vn_compiled_after_heads.
    rewrite -free_omega_observable_sem_retE. apply UFRet.
Qed.

Lemma ptree_vn_compiled_cont_frontier next :
  @frontier_certificate vnE Enum MF Enum_SemanticMeasure
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe (ptree_vn_compiled_cont next))
    (ptree_vn_compiled_after_heads next).
Proof.
  rewrite ptree_vn_compiled_cont_observe.
  apply ptree_vn_compiled_after_frontier.
Qed.

Definition ptree_vn_compiled_body_heads : MF vn_head :=
  @sem_bind MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega)) _ _
    ptree_vn_compiled_round
    (stable_head_bind_front
      (FI := FreeOmegaObservableSemanticMeasure)
      ptree_vn_compiled_after
      ptree_vn_compiled_after_heads).

Lemma ptree_vn_compiled_body_frontier :
  @frontier_certificate vnE Enum MF Enum_SemanticMeasure
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe ptree_vn_compiled_body)
    ptree_vn_compiled_body_heads.
Proof.
  unfold ptree_vn_compiled_body, ptree_vn_compiled_body_heads.
  eapply UFBind.
  - unfold ptree_vn_compiled_round, vn_compiled_step.
    assert (Hstep : observe
      (Prob vn_transition (fun next : unit + bool => Ret next) :
        ptree vnE Enum (unit + bool)) =
      ProbF vn_transition (fun next => Ret next)) by reflexivity.
    rewrite Hstep.
    cbn [ptree_hitting_approx ptree_primitive_kernel
      ptree_stable_target_approx].
    change (@frontier_certificate vnE Enum MF Enum_SemanticMeasure
      (FreeOmegaObservableSemanticMeasure
        (NI := Enum_SemanticMeasure)
        (NO := Enum_SemanticOmega))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega (unit + bool)
      (ProbF vn_transition (fun next => Ret next))
      (FOSample vn_transition (fun next => FORet (FHRet next)))).
    rewrite -free_omega_mixed_bindE.
    eapply UFProb with
      (Good := fun _ => True) (front := fun next => FORet (FHRet next)).
    + apply sem_ae_true.
    + intros next _. rewrite -free_omega_observable_sem_retE. apply UFRet.
  - exact ptree_vn_compiled_after_frontier.
Qed.

Import GRing.Theory.
Local Open Scope ring_scope.

Theorem ptree_vn_direct_ast :
  @ptree_stable_hitting_ast vnE Enum MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe direct_fair) ptree_vn_direct_heads.
Proof.
  assert (Hobserve : observe direct_fair =
    ProbF vn_fair (fun b => Ret b)) by reflexivity.
  rewrite Hobserve.
  eapply ptree_stable_hitting_ast_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. split.
    + apply ptree_stable_hitting_ret.
    + apply free_omega_observable_total_intro.
      exists bool, ptree_vn_head_value,
        (@sem_ret Enum Enum_SemanticMeasure bool b).
      split; [constructor|].
      change (meas_total (ret_Enum b)).
      change (enum_expect (fun _ : bool => (1 : rat)) (ret_Enum b) =
        (1 : rat)).
      rewrite enum_expect_ret. reflexivity.
  - exact ptree_vn_direct_heads_total.
Qed.

Lemma ptree_vn_heads_lift
    (sim : ptree vnE Enum bool -> ptree vnE Enum bool -> Prop) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega)) _ _
    (stable_head_rel eq sim)
    ptree_vn_heads ptree_vn_direct_heads.
Proof.
  eapply FOQLObserve with
    (obsA := ptree_vn_head_value)
    (obsB := ptree_vn_head_value)
    (outA := vn_fair)
    (outB := ptree_vn_direct_observation)
    (S := eq).
  - exact ptree_vn_heads_observes.
  - exact ptree_vn_direct_heads_observes.
  - rewrite ptree_vn_direct_observation_eq.
    apply sem_lift_refl. intros b. reflexivity.
  - intros h1 h2 Hvalue.
    destruct h1 as [b1|X e1 k1];
      destruct h2 as [b2|Y e2 k2];
      try destruct e1; try destruct e2.
    cbn in Hvalue. subst b2. constructor. reflexivity.
  - unfold free_omega_support_lift. split.
    + intros P HP.
      apply free_omega_ae_bind_inv in HP.
      unfold ptree_vn_limit in HP. dependent destruction HP.
      specialize (H 1%nat).
      unfold ptree_vn_iter_approx in H.
      cbn [mixed_iter_approx mixed_bind FreeOmegaMixedMeasure] in H.
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
      unfold ptree_vn_direct_heads.
      eapply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros b _. constructor. exists (FHRet b). split.
        -- constructor. reflexivity.
        -- destruct b; assumption.
    + intros Q HQ.
      unfold ptree_vn_direct_heads in HQ.
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
      * generalize ptree_vn_heads. intro mu. induction mu.
        -- constructor. exact I.
        -- constructor.
        -- eapply FOAESample with (Good := fun _ => True).
           ++ apply (@sem_ae_true Enum Enum_SemanticMeasure
                Enum_SemanticMeasureCoreLaws).
           ++ intros x _. exact (H x).
        -- constructor. exact H.
Qed.

Lemma ptree_vn_raw_heads_lift
    (sim : ptree vnE Enum bool -> ptree vnE Enum bool -> Prop) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega)) _ _
    (stable_head_rel eq sim)
    ptree_vn_raw_heads ptree_vn_direct_heads.
Proof.
  eapply FOQLObserve with
    (obsA := ptree_vn_head_value)
    (obsB := ptree_vn_head_value)
    (outA := vn_fair)
    (outB := ptree_vn_direct_observation)
    (S := eq).
  - exact ptree_vn_raw_limit_observes.
  - exact ptree_vn_direct_heads_observes.
  - rewrite ptree_vn_direct_observation_eq.
    apply sem_lift_refl. intro b. reflexivity.
  - intros h1 h2 Hvalue.
    destruct h1 as [b1|X e1 k1];
      destruct h2 as [b2|Y e2 k2];
      try destruct e1; try destruct e2.
    cbn in Hvalue. subst b2. constructor. reflexivity.
  - unfold free_omega_support_lift. split.
    + intros P HP. unfold ptree_vn_raw_heads,
        ptree_vn_raw_limit in HP.
      dependent destruction HP. specialize (H 1%nat).
      cbn [ptree_vn_raw_schedule] in H.
      rewrite ptree_vn_raw_hitting_three in H.
      pose proof (free_omega_ae_sample_inv H) as Hfirst.
      assert (Hfirst_false : free_omega_ae P
          (FOSample vn_biased_coin (fun b2 =>
            match vn_round_result false b2 with
            | inl _ => ptree_vn_raw_hitting 0
            | inr b => FORet (FHRet b)
            end))).
      { apply Hfirst with (p := vn_one_third).
        - cbn. auto.
        - cbn. discriminate. }
      assert (Hfirst_true : free_omega_ae P
          (FOSample vn_biased_coin (fun b2 =>
            match vn_round_result true b2 with
            | inl _ => ptree_vn_raw_hitting 0
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
      unfold ptree_vn_direct_heads.
      eapply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros b _. constructor. exists (FHRet b). split.
        -- constructor. reflexivity.
        -- destruct b; assumption.
    + intros Q HQ. unfold ptree_vn_direct_heads in HQ.
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
      * generalize ptree_vn_raw_heads. intro mu. induction mu.
        -- constructor. exact I.
        -- constructor.
        -- eapply FOAESample with (Good := fun _ => True).
           ++ apply (@sem_ae_true Enum Enum_SemanticMeasure
                Enum_SemanticMeasureCoreLaws).
           ++ intros x _. exact (H x).
        -- constructor. exact H.
Qed.

(** Canonical endpoint: the unbounded retrying implementation and the
    one-step fair coin are compared only at their subprobabilistic
    stable-hitting limits. *)
Theorem peutt_von_neumann_raw_direct :
  @peutt vnE Enum MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool bool eq
    von_neumann_third direct_fair.
Proof.
  eapply peutt_of_hitting_lift.
  - exact (proj1 ptree_von_neumann_raw_ast).
  - exact (proj1 ptree_vn_direct_ast).
  - exact (ptree_vn_raw_heads_lift _).
Qed.

Theorem peutt_von_neumann_compiled_direct :
  @peutt vnE Enum MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool bool eq
    ptree_vn_compiled direct_fair.
Proof.
  eapply peutt_of_hitting_lift.
  - exact (proj1 ptree_vn_compiled_ast).
  - exact (proj1 ptree_vn_direct_ast).
  - exact (ptree_vn_heads_lift _).
Qed.

Lemma ptree_vn_direct_frontier :
  @frontier_certificate vnE Enum MF Enum_SemanticMeasure
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure)
      (NO := Enum_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe direct_fair) ptree_vn_direct_heads.
Proof.
  unfold direct_fair, ptree_vn_direct_heads. cbn.
  rewrite -free_omega_mixed_bindE.
  eapply UFProb with (Good := fun _ => True)
    (front := fun b => FORet (FHRet b)).
  - apply sem_ae_true.
  - intros b _. rewrite -free_omega_observable_sem_retE. apply UFRet.
Qed.
