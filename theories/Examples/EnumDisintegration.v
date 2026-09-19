Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg rat.
From PTree.Prob Require Import RatSubTypes DiscreteMC EnumMap Coupling FrontierLiftEnum
  TwoLevelMeasure TwoLevelMeasureEnum TwoLevelMeasureSubEnum EnumDisintegration.
From PTree.Examples Require Import EnumMeasureRegression SubEnumRegression.

Import Enum EnumMap RatSubTypes GRing.Theory.
Local Open Scope ring_scope.

(** Conditioning on a constant visible component must retain the latent
    fair bit.  Picking just one supported partner would fail this test. *)
Definition latent_coin : SubEnum (bool * bool) :=
  subenum_bind subenum_fair (fun b => subenum_ret (true,b)).

Example conditional_latent_coin :
  sem_eq (subenum_fiber_kernel latent_coin true) latent_coin.
Proof.
  apply enum_meas_eq_of_eqenum. intros [a b].
  destruct a, b;
    rewrite /latent_coin /subenum_fiber_kernel /enum_fiber_kernel
      /enum_fiber_row /subenum_bind /subenum_ret /subenum_fair
      /reg_fair /enum_as_subprob /= /bind_Enum /ret_Enum /emap
      /acc_mass /Coupling.nnq_div /=;
    apply val_inj; cbn; ring_to_rat; reflexivity.
Qed.

Example absent_fiber_zero_mass :
  enum_mass (subenum_raw (subenum_fiber_kernel latent_coin false)) = 0.
Proof. reflexivity. Qed.

Example latent_coin_reconstruction :
  sem_eq
    (subenum_bind (subenum_first_marginal latent_coin)
      (subenum_fiber_kernel latent_coin)) latent_coin.
Proof. apply subenum_disintegration_reconstruct. Qed.

(** A subprobability need not be total.  Reconstructing the zero joint
    must not introduce probability mass on its null fibers. *)
Example zero_joint_reconstruction :
  sem_eq
    (subenum_bind (subenum_first_marginal (@subenum_zero (bool * bool)))
      (subenum_fiber_kernel (@subenum_zero (bool * bool))))
    (@subenum_zero (bool * bool)).
Proof. apply subenum_disintegration_reconstruct. Qed.

(** Public existential API also accepts function-valued states, without
    a client eqType or an extensional equality decision procedure. *)
Example function_state_disintegration
    (joint : SubEnum ((nat -> bool) * (nat -> nat))) :
  exists conditional,
    sem_eq (subenum_bind (subenum_first_marginal joint) conditional) joint /\
    sem_ae (subenum_first_marginal joint)
      (fun a => subenum_total (conditional a)).
Proof.
  destruct (subenum_disintegration joint) as [k [Hreconstruct [_ [_ Htotal]]]].
  exists k. split; assumption.
Qed.
