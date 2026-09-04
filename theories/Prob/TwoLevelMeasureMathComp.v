Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From mathcomp Require Import ssreflect ssralg reals boolp classical_sets.
From mathcomp.analysis Require Import measure ereal.

From PTree.Prob Require Import FrontierLift MeasureIteration MathCompMeasure
  TwoLevelMeasure FreeOmegaMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Import GRing.Theory.
Local Open Scope ring_scope.

Section MathCompNodeLayer.
Context (R : realType).

(** MathComp kernels instantiate the low-universe node layer.  This adapter
    does not claim that the same sealed HB type can also contain recursive
    frontier heads; the behavior layer is intentionally separate. *)
#[global] Instance MathCompNodeSemanticMeasure :
    SemanticMeasure (MathCompKernelMeasure R) := {
  sem_ret := @mathcomp_kernel_ret R;
  sem_bind := @mathcomp_kernel_bind R;
  sem_eq := @mathcomp_kernel_eq R;
  sem_ae := @mathcomp_kernel_ae R;
  sem_lift := @mathcomp_kernel_lift R
}.

(** The HB carrier is intrinsically a subprobability kernel.  Unlike raw
    Enum, no per-value side condition is needed at a [Prob] node. *)
Definition mathcomp_node_subprob {A}
    (mu : MathCompKernelMeasure R A) : Prop :=
  is_true (mathcomp_kernel_root mu [set: mc_carrier A] <= (1 : R)%:E).

#[global] Instance MathCompNodeSemanticSubprobability :
    @SemanticSubprobability (MathCompKernelMeasure R)
      MathCompNodeSemanticMeasure := {
  sem_subprob := @mathcomp_node_subprob
}.

#[global] Instance MathCompNodeSemanticSubprobabilityLaws :
    @SemanticSubprobabilityLaws (MathCompKernelMeasure R)
      MathCompNodeSemanticMeasure MathCompNodeSemanticSubprobability.
Proof.
  constructor.
  - intros. apply mathcomp_kernel_root_le1.
  - intros. apply mathcomp_kernel_root_le1.
  - intros. split; intros; apply mathcomp_kernel_root_le1.
Qed.

#[global] Instance MathCompNodeSemanticSubprobabilityCarrierLaws :
    @SemanticSubprobabilityCarrierLaws (MathCompKernelMeasure R)
      MathCompNodeSemanticMeasure MathCompNodeSemanticSubprobability.
Proof. constructor. exact (@mathcomp_kernel_root_le1 R). Qed.

Lemma mathcomp_node_sem_retE {A} (x : A) :
  @sem_ret (MathCompKernelMeasure R)
    MathCompNodeSemanticMeasure A x = @mathcomp_kernel_ret R A x.
Proof. reflexivity. Qed.

Lemma mathcomp_node_sem_bindE {A B} (mu : MathCompKernelMeasure R A)
    (k : A -> MathCompKernelMeasure R B) :
  @sem_bind (MathCompKernelMeasure R)
    MathCompNodeSemanticMeasure A B mu k =
  @mathcomp_kernel_bind R A B mu k.
Proof. reflexivity. Qed.

Lemma mathcomp_legacy_ret_semE {A} (x : A) :
  @meas_ret (MathCompKernelMeasure R)
    (MathCompKernelMeasureInterface R) A x =
  @sem_ret (MathCompKernelMeasure R)
    MathCompNodeSemanticMeasure A x.
Proof. reflexivity. Qed.

Lemma mathcomp_legacy_bind_semE {A B}
    (mu : MathCompKernelMeasure R A)
    (k : A -> MathCompKernelMeasure R B) :
  @meas_bind (MathCompKernelMeasure R)
    (MathCompKernelMeasureInterface R) A B mu k =
  @sem_bind (MathCompKernelMeasure R)
    MathCompNodeSemanticMeasure A B mu k.
Proof. reflexivity. Qed.

#[global] Instance MathCompNodeSemanticMeasureCoreLaws
    `{MathCompCouplingGluing R} :
    @SemanticMeasureCoreLaws (MathCompKernelMeasure R)
      MathCompNodeSemanticMeasure.
Proof.
  constructor.
  - exact (@mathcomp_kernel_eq_refl R).
  - exact (@mathcomp_kernel_eq_sym R).
  - exact (@mathcomp_kernel_eq_trans R).
  - exact (@mathcomp_kernel_ae_true R).
  - exact (@meas_ae_mono (MathCompKernelMeasure R)
      (MathCompKernelMeasureInterface R)
      (MathCompKernelMeasureCoreLaws R)).
  - exact (@mathcomp_kernel_ae_conj R).
  - exact (@meas_lift_mono (MathCompKernelMeasure R)
      (MathCompKernelMeasureInterface R)
      (MathCompKernelMeasureCoreLaws R)).
  - exact (@mathcomp_kernel_lift_refl R).
  - exact (@mathcomp_kernel_lift_ret R).
  - exact (@mathcomp_kernel_lift_proper_l R).
  - exact (@mathcomp_kernel_lift_proper_r R).
  - exact (@mathcomp_kernel_lift_sym R).
  - exact (@mathcomp_kernel_lift_comp R H).
Qed.

Lemma mathcomp_kernel_lift_refl_ae {A}
    (mu : MathCompKernelMeasure R A) (P : A -> Prop) :
  mathcomp_kernel_ae mu P ->
  mathcomp_kernel_lift (fun x y => x = y /\ P x) mu mu.
Proof.
  move=> Hae.
  rewrite /mathcomp_kernel_ae /mathcomp_measure_ae in Hae.
  exists (mathcomp_diagonal_joint mu). split.
  - move=> U _ _. exact: mathcomp_diagonal_left.
  - split.
    + move=> U _ _. exact: mathcomp_diagonal_right.
    + rewrite /almost_everywhere.
      apply/negligibleP; first by [].
      change (mathcomp_kernel_root mu
        ((mc_joint_diagonal A) @^-1`
          (~` mc_relation (fun x y => x = y /\ P x))) = 0).
      have Eset :
          (mc_joint_diagonal A) @^-1`
            (~` mc_relation (fun x y => x = y /\ P x)) =
          (~` mc_predicate P).
      { apply/seteqP; split.
        - move=> [|a] /= Hx.
          + exact Hx.
          + move=> HP. apply: Hx. split=> //.
        - move=> [|a] /= Hx.
          + exact Hx.
          + move=> [_ HP]. exact: Hx HP. }
      rewrite Eset.
      have Hm : measurable (~` mc_predicate P) by [].
      exact: measure_negligible Hm Hae.
Qed.

#[global] Instance MathCompNodeSemanticMeasureAELiftLaws :
    @SemanticMeasureAELiftLaws (MathCompKernelMeasure R)
      MathCompNodeSemanticMeasure.
Proof.
  constructor. exact @mathcomp_kernel_lift_refl_ae.
Qed.

#[global] Instance MathCompNodeSemanticMeasureDiracAELaws :
    @SemanticMeasureDiracAELaws (MathCompKernelMeasure R)
      MathCompNodeSemanticMeasure.
Proof.
  constructor. exact (@mathcomp_kernel_ae_ret_iff R).
Qed.

#[global] Instance MathCompNodeSemanticMeasureCountableAELaws :
    @SemanticMeasureCountableAELaws (MathCompKernelMeasure R)
      MathCompNodeSemanticMeasure.
Proof.
  constructor. exact (@mathcomp_kernel_ae_countable R).
Qed.

#[global] Instance MathCompNodeSemanticMeasureAEKleisliLaws :
    @SemanticMeasureAEKleisliLaws (MathCompKernelMeasure R)
      MathCompNodeSemanticMeasure.
Proof.
  constructor.
  - intros A P x Hx.
    exact (@meas_ae_ret (MathCompKernelMeasure R)
      (MathCompKernelMeasureInterface R)
      (MathCompKernelMeasureMonadLaws R) A x P Hx).
  - exact (@mathcomp_kernel_ae_bind R).
Qed.

#[global] Instance MathCompNodeSemanticMeasureCouplingAELaws :
    @SemanticMeasureCouplingAELaws (MathCompKernelMeasure R)
      MathCompNodeSemanticMeasure.
Proof.
  constructor.
  - exact (@mathcomp_kernel_lift_ae_transport_r R).
  - exact (@mathcomp_kernel_lift_ae_restrict R).
Qed.

#[global] Instance MathCompNodeSemanticMeasureBindAEExactLaws :
    @SemanticMeasureBindAEExactLaws (MathCompKernelMeasure R)
      MathCompNodeSemanticMeasure.
Proof.
  constructor. exact (@mathcomp_kernel_ae_bind_iff R).
Qed.

(** Setwise order on returned-value events.  As in the existing MathComp
    omega semantics, events containing [MCBottom] are excluded because their
    unfinished mass decreases while returned mass increases. *)
Definition mathcomp_node_le {A}
    (mu nu : MathCompKernelMeasure R A) : Prop :=
  forall U : set (mc_carrier A), measurable U -> ~ U MCBottom ->
    mathcomp_kernel_root mu U <= mathcomp_kernel_root nu U = true.

#[global] Instance MathCompNodeSemanticOmega :
    @SemanticOmega (MathCompKernelMeasure R)
      MathCompNodeSemanticMeasure := {
  sem_zero := @mathcomp_kernel_zero R;
  sem_le := @mathcomp_node_le;
  sem_lub := @mathcomp_kernel_lub R;
  sem_total := @mathcomp_kernel_total R
}.

Lemma mathcomp_node_sem_zeroE {A} :
  @sem_zero (MathCompKernelMeasure R)
    MathCompNodeSemanticMeasure
    MathCompNodeSemanticOmega A = @mathcomp_kernel_zero R A.
Proof. reflexivity. Qed.

Lemma mathcomp_node_sem_lubE {A}
    (chain : nat -> MathCompKernelMeasure R A) out :
  @sem_lub (MathCompKernelMeasure R)
    MathCompNodeSemanticMeasure
    MathCompNodeSemanticOmega A chain out <->
  @mathcomp_kernel_lub R A chain out.
Proof. reflexivity. Qed.

Lemma mathcomp_node_sem_totalE {A} (mu : MathCompKernelMeasure R A) :
  @sem_total (MathCompKernelMeasure R)
    MathCompNodeSemanticMeasure
    MathCompNodeSemanticOmega A mu <->
  @mathcomp_kernel_total R A mu.
Proof. reflexivity. Qed.

End MathCompNodeLayer.

(** The high-universe behavior instance is the free omega completion over
    MathComp sampling nodes.  Unlike [MathCompKernelMeasure] itself, this type
    constructor can be instantiated at the universe containing recursive
    frontier heads. *)
Polymorphic Definition MathCompBehaviorMeasure (R : realType) :=
  FreeOmega (MathCompKernelMeasure R).
