(** One actual ITree source, lowered probability, and interpreted State.
    Probability coefficients need not be total or fair. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ITree.Core Require Import ITreeDefinition.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree Require Import PTree PTreeFacts.
From PTree.Core Require Import ITreeBridge.
From PTree.Eq.Backend Require Import SubEnumQ.
From PTree.Interp.Algebra Require Import Computation State.
From PTree.Interp.FreeOmega Require Import ITreeCompletion State.
Set Implicit Arguments.
Unset Strict Implicit.

Definition count_sample (mu : SubEnumQ bool) :
    itree (probE SubEnumQ +' (stateE nat +' void1)) bool :=
  ITreeDefinition.Vis (inl1 (Sample mu)) (fun b =>
  ITreeDefinition.Vis (inr1 (inl1 (Get nat))) (fun n =>
  ITreeDefinition.Vis (inr1 (inl1 (Put nat (S n)))) (fun _ =>
  ITreeDefinition.Ret b))).

Theorem lower_then_count (mu : SubEnumQ bool) n :
  run_state (elaborate (count_sample mu)) n ≈ₚ
  Prob mu (fun b => Ret (S n,b)).
Proof.
  unfold count_sample.
  eapply peutt_trans.
  - apply PTree.Interp.FreeOmega.State.run_state_peutt_eq. apply free_omega_elab_sample.
  - eapply peutt_trans; [apply PTree.Interp.Algebra.State.run_state_prob|].
    apply peutt_prob_Proper. intro b.
    eapply peutt_trans.
    + apply PTree.Interp.FreeOmega.State.run_state_peutt_eq. apply free_omega_elab_vis.
    + eapply peutt_trans; [apply state_get_step|].
      eapply peutt_trans.
      * apply PTree.Interp.FreeOmega.State.run_state_peutt_eq. apply free_omega_elab_vis.
      * eapply peutt_trans; [apply state_put_step|].
        apply peutt_observe_eq. reflexivity.
Qed.

(** The already-proved StateT square applies to this same lowered program,
    including residual effects and arbitrary lawful sampling algebras. *)
From ITree.Basics Require Import Basics Monad.
From PTree.Core Require Import Fold IterationLaws.
From PTree.Interp Require Import StateFold StateFoldFacts.

Theorem count_sample_transformer_agreement {T : Type -> Type}
    `{MT : Monad T} `{IT : MonadIter T} `{QT : Eq1 T}
    `{QE : @Eq1Equivalence T MT QT} `{ML : @MonadLawsE T QT MT}
    (Hunif : @iteration_uniform T MT IT QT)
    (handle : forall X, void1 X -> T X) (sample : forall X, SubEnumQ X -> T X) mu n :
  eq1 (fold_state handle sample (elaborate (count_sample mu)) n)
    (fold handle sample (run_state (elaborate (count_sample mu)) n)).
Proof. apply fold_run_state. exact Hunif. Qed.
