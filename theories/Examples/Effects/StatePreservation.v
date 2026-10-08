(** Role: supporting program/semantic example, not a flagship claim. *)
(** Stateful weak rewrites, heterogeneous results and infinite probabilistic
    interaction. Source peutt is not restricted to lockstep trees. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms List.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Interp Require Import State StatePreservation StateFacts StateIter.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.
From PTree.Eq Require Import PEutt.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure RelationalLimit.
Require PTree.Interp.FreeOmega.State.
From PTree.Eq.FreeOmega Require Import Relation.
From PTree.Interp.FreeOmega Require Import Rewriting.
From PTree.Interp.Algebra Require Import State.
Import FreeOmegaRewriting.
From PTree.Examples Require Import StateCounter.
From PTree.Execution Require Import Runner.
From PTree.Execution.Backend Require Import SubEnumQ.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation W E A B RR := (@peutt E SubEnumQ MF FI FC FreeOmegaMixedMeasure FO A B RR).

Section GenericClient.
Context {S : Type} {E : Type → Type}.
Example weak_source_preserved {A B} (RR : A → B → Prop) s
    (t : ptree (stateE S +' E) SubEnumQ A) (u : ptree (stateE S +' E) SubEnumQ B) :
  W _ _ _ RR t u → W _ _ _ (state_result_rel RR) (run_state t s) (run_state u s).
Proof. apply PTree.Interp.FreeOmega.State.run_state_peutt. Qed.

(** The opt-in library registration supplies State congruence; no local
    copy of the generic Proper proof is needed. *)
Example actual_state_setoid_rewrite s (t u : ptree (stateE S +' E) SubEnumQ nat)
    (H : W _ _ _ eq t u) : W _ _ _ eq (run_state t s) (run_state u s).
Proof. setoid_rewrite H. apply peutt_refl. Qed.

Example get_is_eliminated {A} (k : S → ptree (stateE S +' E) SubEnumQ A) s :
  W _ _ _ eq (run_state (Vis (inl1 (Get S)) k) s) (run_state (k s) s).
Proof.
  apply state_get_step.
Qed.

Example put_is_eliminated {A} (k : unit → ptree (stateE S +' E) SubEnumQ A) s s' :
  W _ _ _ eq (run_state (Vis (inl1 (Put S s')) k) s) (run_state (k tt) s').
Proof.
  apply state_put_step.
Qed.

Example state_bind_algebra {A B} (t : ptree (stateE S +' E) SubEnumQ A)
    (k : A → ptree (stateE S +' E) SubEnumQ B) s :
  W _ _ _ eq (run_state (PTree.bind t k) s)
    (PTree.bind (run_state t s) (λ sa, run_state (k (snd sa)) (fst sa))).
Proof. apply peutt_of_pstruct. apply run_state_bind. Qed.

Example state_iter_algebra {I A} (step : I → ptree (stateE S +' E) SubEnumQ (I+A)) i s :
  W _ _ _ eq (run_state (PTree.iter step i) s) (PTree.iter (state_iter_step step) (s,i)).
Proof. apply peutt_of_pstruct. apply run_state_iter. Qed.
End GenericClient.

Definition boolean_result : ptree (stateE nat +' void1) SubEnumQ bool :=
  Vis (inl1 (Put nat 9)) (λ _, Ret true).
Definition numeric_result : ptree (stateE nat +' void1) SubEnumQ nat :=
  Vis (inl1 (Put nat 9)) (λ _, Ret 1).
Definition bool_nat (b : bool) (n : nat) := n = if b then 1 else 0.

Example heterogeneous_state_result :
  W _ _ _ (state_result_rel bool_nat) (run_state boolean_result 3) (run_state numeric_result 3).
Proof.
  apply weak_source_preserved. apply peutt_vis. intro u. apply peutt_ret. reflexivity.
Qed.

Example retry_source_weak_rewrite s :
  W _ _ _ eq (run_state (Tau count_until_success) s) (run_state count_until_success s).
Proof. setoid_rewrite (peutt_tau_l (MF := MF) count_until_success). reflexivity. Qed.

Definition put_then_get : ptree (stateE nat +' void1) SubEnumQ nat :=
  Vis (inl1 (Put nat 9)) (λ _, Vis (inl1 (Get nat)) (λ s, Ret s)).
Example state_update_is_not_reordered :
  run (@replay_sample) 2 (run_state put_then_get 3) [] = (Returned (9,9), []).
Proof. native_compute. reflexivity. Qed.

From mathcomp Require Import reals.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.
Example real_state_preservation (R : realType) {S E A B} (RR : A → B → Prop) s
    (t : ptree (stateE S +' E) (SubEnumR R) A) (u : ptree (stateE S +' E) (SubEnumR R) B) :
  peutt (MF := FreeOmega (SubEnumR R)) RR t u →
  peutt (MF := FreeOmega (SubEnumR R)) (state_result_rel RR) (run_state t s) (run_state u s).
Proof. apply PTree.Interp.FreeOmega.State.run_state_peutt. Qed.
