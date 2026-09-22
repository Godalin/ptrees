(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Classes Require Import RelationClasses.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Native PTree.Prob.FreeOmega.Recovery PTree.Prob.FreeOmega.Coupling.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.Recovery.
Require Import PTree.Prob.Backend.EnumQ.SemanticCoupling.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.EquivalenceJoint PTree.Prob.Backend.SubEnumQ.FreeOmega.NativeCoupling.
From PTree.Regression.Infrastructure Require Import FiniteInternalPlan.
From PTree.Regression.Backend Require Import SubEnumQRegression.
From PTree.Regression.Infrastructure Require Import HiddenRandomState CouplingReferences.
From PTree.Eq Require Import PStrong.
From PTree.Eq.Internal Require Import FiniteInternal FiniteInternalPlan.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternalNative FiniteInternalRoundCoupling FiniteInternalNativeJoint FiniteInternalJointRows.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma fair_paths_normalized :
  free_omega_qlift (fun _ _ => True)
    (FOSample subenumQ_fair (fun b => FORet b)) (FORet tt).
Proof.
  eapply free_omega_sample_to_constant with (point := false).
  - intro P. apply sem_ae_ret_iff.
  - exact fair_discard_same_mass.
  - intro b. apply FOQLStructural, FOLRet. exact I.
Qed.

(** Both guards really sample: the right coin has split native
    weights.  Native realization couples the outcomes rather than drawing
    the two guards independently. *)
Definition coin_left_plan := FIPStop subenumQ_direct_coin.
Definition coin_right_plan := FIPStop subenumQ_split_coin.

Example split_coin_native_joint_round :
  exists (W : Type) (round : SubEnumQ W)
    (left : W -> native_sample_type (internal_plan_round_native coin_left_plan))
    (right : W -> native_sample_type (internal_plan_round_native coin_right_plan)),
    free_omega_qlift (fun w x => left w = x)
      (FOSample round (fun w => FORet w))
      (FOSample (native_sample_measure (internal_plan_round_native coin_left_plan)) (fun x => FORet x)) /\
    free_omega_qlift (fun w y => right w = y)
      (FOSample round (fun w => FORet w))
      (FOSample (native_sample_measure (internal_plan_round_native coin_right_plan)) (fun y => FORet y)) /\
    sem_ae round (fun w => internal_round_path_rel eq eq
      coin_left_plan coin_right_plan (left w) (right w)).
Proof.
  eapply finite_internal_native_joint_round with (joint := subenumQ_ret tt)
    (left := fun z : unit => z) (right := fun z : unit => z).
  - exact (@subenumQ_coupling_realization).
  - apply free_omega_qlift_refl. intro z. reflexivity.
  - apply free_omega_qlift_refl. intro z. reflexivity.
  - apply (@sem_ae_ret_iff SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticMeasureDiracAELaws).
    cbn beta. constructor.
    eapply sem_lift_mono; [|exact subenumQ_fair_split_lift].
    intros x y ->. reflexivity.
Qed.

Lemma direct_path_normalized :
  free_omega_qlift (fun _ _ => True)
    (FOSample (subenumQ_ret tt) (fun x => FORet x)) (FORet tt).
Proof.
  apply (@FOQLSampleRetL SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).
  - apply sem_ae_ret_iff.
  - apply FOQLStructural, FOLRet. exact I.
Qed.

(** Both sample outcomes decode to the same HIGHER-UNIVERSE residual tree.
    Recovery must retain the fair bit, not choose a representative branch. *)
Definition latent_presentation :=
  constant_native_presentation subenumQ_fair (Ret true : ptree planE SubEnumQ bool).
Definition direct_presentation :=
  constant_native_presentation (subenumQ_ret tt) (Ret true : ptree planE SubEnumQ bool).
Definition latent_recovery : free_omega_native_recovery latent_presentation :=
  constant_native_recovery _ fair_paths_normalized.
Definition direct_recovery : free_omega_native_recovery direct_presentation :=
  constant_native_recovery _ direct_path_normalized.

Example latent_recovery_resamples_the_whole_coin t :
  recovery_kernel latent_recovery t = FOSample subenumQ_fair (fun b => FORet b).
Proof. reflexivity. Qed.

Example latent_recovery_preserves_distribution :
  free_omega_qlift eq
    (free_omega_bind (free_omega_native latent_presentation) (recovery_kernel latent_recovery))
    (FOSample subenumQ_fair (fun b => FORet b)).
Proof. exact (recovery_reconstruct latent_recovery). Qed.

Lemma discarded_coin_decoded_coupling :
  free_omega_qlift eq (free_omega_native latent_presentation)
    (free_omega_native direct_presentation).
Proof.
  eapply FOQLComp with (T := eq) (U := eq) (mid := FORet (Ret true)).
  - apply constant_native_collapse. exact fair_paths_normalized.
  - apply FOQLMono with (T := fun x y => y = x).
    + apply FOQLSym, constant_native_collapse. exact direct_path_normalized.
    + intros x y Hyx. symmetry. exact Hyx.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

Example discarded_coin_path_coupling :
  free_omega_qlift
    (fun b u => native_sample_value latent_presentation b =
      native_sample_value direct_presentation u)
    (FOSample subenumQ_fair (fun b => FORet b))
    (FOSample (subenumQ_ret tt) (fun u => FORet u)).
Proof.
  exact (free_omega_native_coupling_pullback latent_recovery direct_recovery
    discarded_coin_decoded_coupling).
Qed.

(** Inverse recovery also works for a zero-mass sample; normalization is
    a law of the conditional kernel, NOT a totality premise on the input. *)
Definition empty_presentation : free_omega_native_presentation SubEnumQ bool :=
  {| native_sample_type := bool; native_sample_measure := subenumQ_zero;
     native_sample_value := fun b => b |}.
Definition empty_recovery : free_omega_native_recovery empty_presentation :=
  inverse_native_recovery (p := empty_presentation) (inverse := fun b => b)
    (fun b => eq_refl b).

Example zero_mass_recovery_reconstructs :
  free_omega_qlift eq
    (free_omega_bind (free_omega_native empty_presentation) (recovery_kernel empty_recovery))
    (FOSample (@subenumQ_zero bool) (fun b => FORet b)).
Proof. exact (recovery_reconstruct empty_recovery). Qed.

(** The general constructor is neither an inverse nor a constant-decoder
    shortcut.  The source loses half its mass; each of the two distinct
    returned trees has two latent paths (the second bit is forgotten). *)
Definition partial_latent_sample : SubEnumQ (bool * bool) :=
  subenumQ_bind subenumQ_fair (fun keep =>
    if keep then subenumQ_two_coins else subenumQ_zero).

Definition partial_latent_presentation : free_omega_native_presentation SubEnumQ
    (ptree planE SubEnumQ bool) :=
  {| native_sample_type := bool * bool;
     native_sample_measure := partial_latent_sample;
     native_sample_value := fun bits => Ret (fst bits) |}.

Definition partial_latent_recovery :=
  subenumQ_native_recovery partial_latent_presentation.

Example partial_latent_source_is_not_total : ~ subenumQ_total partial_latent_sample.
Proof. unfold subenumQ_total. native_compute. discriminate. Qed.

Example partial_latent_recovery_reconstructs :
  free_omega_qlift eq
    (free_omega_bind (free_omega_native partial_latent_presentation)
      (recovery_kernel partial_latent_recovery))
    (FOSample partial_latent_sample (fun bits => FORet bits)).
Proof. exact (recovery_reconstruct partial_latent_recovery). Qed.

Definition partial_visible_presentation : free_omega_native_presentation SubEnumQ
    (ptree planE SubEnumQ bool) :=
  {| native_sample_type := bool;
     native_sample_measure := subenumQ_bind partial_latent_sample
       (fun bits => subenumQ_ret (fst bits));
     native_sample_value := fun b => Ret b |}.

Lemma partial_decoded_coupling :
  free_omega_qlift eq (free_omega_native partial_latent_presentation)
    (free_omega_native partial_visible_presentation).
Proof.
  apply FOQLMono with (T := fun x y => y = x).
  - apply FOQLSym. exact (@free_omega_sample_map SubEnumQ
      SubEnumQ_SemanticMeasure SubEnumQ_SemanticMeasureCoreLaws
      SubEnumQ_SemanticOmega SubEnumQ_SemanticMeasureDiracAELaws
      SubEnumQ_SemanticMeasureBindAEExactLaws _ _ _ partial_latent_sample fst
      (fun b => FORet (Ret b : ptree planE SubEnumQ bool))).
  - intros x y Hyx. symmetry. exact Hyx.
Qed.

Example partial_noninjective_path_coupling :
  free_omega_qlift
    (fun bits b => (Ret (fst bits) : ptree planE SubEnumQ bool) = Ret b)
    (FOSample partial_latent_sample (fun bits => FORet bits))
    (FOSample (native_sample_measure partial_visible_presentation) (fun b => FORet b)).
Proof.
  exact (subenumQ_native_coupling_pullback
    (p := partial_latent_presentation) (q := partial_visible_presentation)
    partial_decoded_coupling).
Qed.

(** The extracted joint preserves a non-total source and a noninjective
    high-tree decoder.  Conditional rows are not assumed total everywhere. *)
Example partial_noninjective_native_quotient_joint :
  exists (Z : Type) (joint : SubEnumQ Z) (left : Z -> bool * bool) (right : Z -> bool),
    free_omega_qlift (fun z bits => left z = bits)
      (FOSample joint (fun z => FORet z))
      (FOSample partial_latent_sample (fun bits => FORet bits)) /\
    free_omega_qlift (fun z b => right z = b)
      (FOSample joint (fun z => FORet z))
      (FOSample (native_sample_measure partial_visible_presentation) (fun b => FORet b)) /\
    sem_ae joint (fun z => (Ret (fst (left z)) : ptree planE SubEnumQ bool) = Ret (right z)).
Proof.
  exact (subenumQ_equivalence_quotient_joint eq_equivalence partial_decoded_coupling).
Qed.

(** A null source with the SAME noninjective high decoder is also valid;
    conditional normalization is required only almost everywhere. *)
Definition null_latent_presentation : free_omega_native_presentation SubEnumQ
    (ptree planE SubEnumQ bool) :=
  {| native_sample_type := bool * bool;
     native_sample_measure := subenumQ_zero;
     native_sample_value := fun bits => Ret (fst bits) |}.

Example null_noninjective_recovery_reconstructs :
  free_omega_qlift eq
    (free_omega_bind (free_omega_native null_latent_presentation)
      (recovery_kernel (subenumQ_native_recovery null_latent_presentation)))
    (FOSample (@subenumQ_zero (bool * bool)) (fun bits => FORet bits)).
Proof. apply recovery_reconstruct. Qed.

(** Actual use beneath high-tree decoded coupling: no hand-written
    recovery certificate or injectivity premise is left for the client. *)
Example discarded_coin_general_pullback :
  free_omega_qlift
    (fun b u => native_sample_value latent_presentation b =
      native_sample_value direct_presentation u)
    (FOSample subenumQ_fair (fun b => FORet b))
    (FOSample (subenumQ_ret tt) (fun u => FORet u)).
Proof.
  exact (subenumQ_native_coupling_pullback
    (p := latent_presentation) (q := direct_presentation)
    discarded_coin_decoded_coupling).
Qed.
