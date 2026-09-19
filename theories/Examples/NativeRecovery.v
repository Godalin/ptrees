Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum
  FreeOmegaMeasure FreeOmegaNative FreeOmegaRecovery FreeOmegaCoupling.
From PTree.Examples Require Import FiniteInternalPlan SubEnumRegression HiddenRandomState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma fair_paths_normalized :
  free_omega_qlift (fun _ _ => True)
    (FOSample subenum_fair (fun b => FORet b)) (FORet tt).
Proof.
  eapply free_omega_sample_to_constant with (point := false).
  - intro P. apply sem_ae_ret_iff.
  - exact hidden_fair_same_mass.
  - intro b. apply FOQLStructural, FOLRet. exact I.
Qed.

Lemma direct_path_normalized :
  free_omega_qlift (fun _ _ => True)
    (FOSample (subenum_ret tt) (fun x => FORet x)) (FORet tt).
Proof.
  apply (@FOQLSampleRetL SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
  - apply sem_ae_ret_iff.
  - apply FOQLStructural, FOLRet. exact I.
Qed.

(** Both sample outcomes decode to the same HIGHER-UNIVERSE residual tree.
    Recovery must retain the fair bit, not choose a representative branch. *)
Definition latent_presentation :=
  constant_native_presentation subenum_fair (Ret true : ptree planE SubEnum bool).
Definition direct_presentation :=
  constant_native_presentation (subenum_ret tt) (Ret true : ptree planE SubEnum bool).
Definition latent_recovery : free_omega_native_recovery latent_presentation :=
  constant_native_recovery _ fair_paths_normalized.
Definition direct_recovery : free_omega_native_recovery direct_presentation :=
  constant_native_recovery _ direct_path_normalized.

Example latent_recovery_resamples_the_whole_coin t :
  recovery_kernel latent_recovery t = FOSample subenum_fair (fun b => FORet b).
Proof. reflexivity. Qed.

Example latent_recovery_preserves_distribution :
  free_omega_qlift eq
    (free_omega_bind (free_omega_native latent_presentation) (recovery_kernel latent_recovery))
    (FOSample subenum_fair (fun b => FORet b)).
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
    (FOSample subenum_fair (fun b => FORet b))
    (FOSample (subenum_ret tt) (fun u => FORet u)).
Proof.
  exact (free_omega_native_coupling_pullback latent_recovery direct_recovery
    discarded_coin_decoded_coupling).
Qed.

(** Inverse recovery also works for a zero-mass sample; normalization is
    a law of the conditional kernel, NOT a totality premise on the input. *)
Definition empty_presentation : free_omega_native_presentation SubEnum bool :=
  {| native_sample_type := bool; native_sample_measure := subenum_zero;
     native_sample_value := fun b => b |}.
Definition empty_recovery : free_omega_native_recovery empty_presentation :=
  inverse_native_recovery (p := empty_presentation) (inverse := fun b => b)
    (fun b => eq_refl b).

Example zero_mass_recovery_reconstructs :
  free_omega_qlift eq
    (free_omega_bind (free_omega_native empty_presentation) (recovery_kernel empty_recovery))
    (FOSample (@subenum_zero bool) (fun b => FORet b)).
Proof. exact (recovery_reconstruct empty_recovery). Qed.
