(** Case role: supporting example.
    Reading entry: lower_then_count; count_sample_transformer_agreement.
    Scope: SubEnumQ; no totality assumption on the sampled distribution.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
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
From PTree.Interp.FreeOmega Require Import Rewriting.
Import FreeOmegaRewriting.
Set Implicit Arguments.
Unset Strict Implicit.

Definition count_sample (mu : SubEnumQ bool) :
    itree (probE SubEnumQ +' (stateE nat +' void1)) bool :=
  ITreeDefinition.Vis (inl1 (Sample mu)) (fun b =>
  ITreeDefinition.Vis (inr1 (inl1 (Get nat))) (fun n =>
  ITreeDefinition.Vis (inr1 (inl1 (Put nat (S n)))) (fun _ =>
  ITreeDefinition.Ret b))).

(** Local State calculation, independent of the distribution that supplied b. *)
Lemma lower_count_tail (b : bool) n :
  run_state (elaborate
    (ITreeDefinition.Vis (inr1 (inl1 (Get nat))) (fun s =>
     ITreeDefinition.Vis (inr1 (inl1 (Put nat (S s)))) (fun _ =>
     ITreeDefinition.Ret b)))) n ≈ₚ
  (Ret (S n,b) : ptree void1 SubEnumQ (nat * bool)).
Proof.
  setoid_rewrite free_omega_elab_vis.
  setoid_rewrite state_get_step.
  setoid_rewrite free_omega_elab_vis.
  setoid_rewrite state_put_step.
  apply peutt_observe_eq. reflexivity.
Qed.

Theorem lower_then_count (mu : SubEnumQ bool) n :
  run_state (elaborate (count_sample mu)) n ≈ₚ
  Prob mu (fun b => Ret (S n,b)).
Proof.
  unfold count_sample.
  setoid_rewrite free_omega_elab_sample.
  setoid_rewrite PTree.Interp.Algebra.State.run_state_prob.
  setoid_rewrite lower_count_tail. reflexivity.
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
