(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg rat.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling PTree.Prob.Backend.EnumQ.FrontierLift.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.Disintegration.
From PTree.Regression.Backend Require Import EnumQMeasureRegression SubEnumQRegression.

Import EnumQ PTree.Prob.Backend.EnumQ.Map RatSubTypes GRing.Theory.
Local Open Scope ring_scope.

(** Conditioning on a constant visible component must retain the latent
    fair bit.  Picking just one supported partner would fail this test. *)
Definition latent_coin : SubEnumQ (bool * bool) :=
  subenumQ_bind subenumQ_fair (fun b => subenumQ_ret (true,b)).

Example conditional_latent_coin :
  sem_eq (subenumQ_fiber_kernel latent_coin true) latent_coin.
Proof.
  apply enumQ_meas_eq_of_eqenum. intros [a b].
  destruct a, b;
    rewrite /latent_coin /subenumQ_fiber_kernel /enumQ_fiber_kernel
      /enumQ_fiber_row /subenumQ_bind /subenumQ_ret /subenumQ_fair
      /reg_fair /enumQ_as_subprob /= /bind_EnumQ /ret_EnumQ /emap
      /acc_mass /Coupling.nnq_div /=;
    apply val_inj; cbn; ring_to_rat; reflexivity.
Qed.

Example absent_fiber_zero_mass :
  enumQ_mass (subenumQ_raw (subenumQ_fiber_kernel latent_coin false)) = 0.
Proof. reflexivity. Qed.

Example latent_coin_reconstruction :
  sem_eq
    (subenumQ_bind (subenumQ_first_marginal latent_coin)
      (subenumQ_fiber_kernel latent_coin)) latent_coin.
Proof. apply subenumQ_disintegration_reconstruct. Qed.

(** A subprobability need not be total.  Reconstructing the zero joint
    must not introduce probability mass on its null fibers. *)
Example zero_joint_reconstruction :
  sem_eq
    (subenumQ_bind (subenumQ_first_marginal (@subenumQ_zero (bool * bool)))
      (subenumQ_fiber_kernel (@subenumQ_zero (bool * bool))))
    (@subenumQ_zero (bool * bool)).
Proof. apply subenumQ_disintegration_reconstruct. Qed.

(** Public existential API also accepts function-valued states, without
    a client eqType or an extensional equality decision procedure. *)
Example function_state_disintegration
    (joint : SubEnumQ ((nat -> bool) * (nat -> nat))) :
  exists conditional,
    sem_eq (subenumQ_bind (subenumQ_first_marginal joint) conditional) joint /\
    sem_ae (subenumQ_first_marginal joint)
      (fun a => subenumQ_total (conditional a)).
Proof.
  destruct (subenumQ_disintegration joint) as [k [Hreconstruct [_ [_ Htotal]]]].
  exists k. split; assumption.
Qed.
