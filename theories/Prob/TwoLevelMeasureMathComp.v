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
#[global] Instance MathCompNodeSemanticMeasureInterface :
    SemanticMeasureInterface (MathCompKernelMeasure R) := {
  sem_ret := @mathcomp_kernel_ret R;
  sem_bind := @mathcomp_kernel_bind R;
  sem_eq := @mathcomp_kernel_eq R;
  sem_ae := @mathcomp_kernel_ae R;
  sem_lift := @mathcomp_kernel_lift R
}.

#[global] Instance MathCompNodeSemanticMeasureCoreLaws
    `{MathCompCouplingGluing R} :
    @SemanticMeasureCoreLaws (MathCompKernelMeasure R)
      MathCompNodeSemanticMeasureInterface.
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
      MathCompNodeSemanticMeasureInterface.
Proof.
  constructor. exact @mathcomp_kernel_lift_refl_ae.
Qed.

(** Setwise order on returned-value events.  As in the existing MathComp
    omega semantics, events containing [MCBottom] are excluded because their
    unfinished mass decreases while returned mass increases. *)
Definition mathcomp_node_le {A}
    (mu nu : MathCompKernelMeasure R A) : Prop :=
  forall U : set (mc_carrier A), measurable U -> ~ U MCBottom ->
    mathcomp_kernel_root mu U <= mathcomp_kernel_root nu U = true.

#[global] Instance MathCompNodeSemanticOmegaInterface :
    @SemanticOmegaInterface (MathCompKernelMeasure R)
      MathCompNodeSemanticMeasureInterface := {
  sem_zero := @mathcomp_kernel_zero R;
  sem_le := @mathcomp_node_le;
  sem_lub := @mathcomp_kernel_lub R;
  sem_total := @mathcomp_kernel_total R
}.

End MathCompNodeLayer.

(** The high-universe behavior instance is the free omega completion over
    MathComp sampling nodes.  Unlike [MathCompKernelMeasure] itself, this type
    constructor can be instantiated at the universe containing recursive
    frontier heads. *)
Polymorphic Definition MathCompBehaviorMeasure (R : realType) :=
  FreeOmega (MathCompKernelMeasure R).
