(** Case role: supporting example.
    Reading entry: two_coins_elaborates; retry_elaborates.
    Scope: SubEnumQ / observable FreeOmega; iteration preservation does not assert AST.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDIES.md. *)
(** ITree sampling-as-an-effect elaborated to primitive PTree probability.
    The source really is an [itree], not a PTree reusing an event signature. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List Bool.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From ITree.Core Require Import ITreeDefinition.
From ITree.Indexed Require Import Sum.
From PTree Require Import PTree PTreeFacts.
From PTree.Core Require Import ITreeBridge.
From PTree.Interp.FreeOmega Require Import ITreeCompletion.
From PTree.Interp.FreeOmega Require Import Rewriting.
From PTree.Eq.Backend Require Import SubEnumQ.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.
Import FreeOmegaRewriting.

Definition fair_entries : list (rat * bool) := [(2^-1,true); (2^-1,false)].
Definition fair_coin : SubEnumQ bool.
Proof. finite_distribution fair_entries. Defined.

Definition two_coins : itree (probE SubEnumQ) bool :=
  ITree.bind (ITree.trigger (Sample fair_coin)) (λ x,
  ITree.bind (ITree.trigger (Sample fair_coin)) (λ y,
  ITreeDefinition.Ret (xorb x y))).

Definition native_two_coins : ptree void1 SubEnumQ bool :=
  PTree.bind (Prob fair_coin (λ x, Ret x)) (λ x,
  PTree.bind (Prob fair_coin (λ y, Ret y)) (λ y,
  Ret (xorb x y))).

Theorem two_coins_elaborates : elaborate_closed two_coins ≈ₚ native_two_coins.
Proof.
  unfold two_coins, native_two_coins, elaborate_closed.
  setoid_rewrite free_omega_elab_bind.
  setoid_rewrite free_omega_elab_sample_trigger.
  setoid_rewrite free_omega_elab_bind.
  setoid_rewrite free_omega_elab_sample_trigger.
  setoid_rewrite free_omega_elab_ret.
  reflexivity.
Qed.

(** No fuel is added by elaboration: this source can retry indefinitely.
    Iteration preservation does not assert almost-sure termination. *)
Definition retry_step (_ : unit) : itree (probE SubEnumQ) (unit + bool) :=
  ITree.bind (ITree.trigger (Sample fair_coin)) (λ b,
    ITreeDefinition.Ret (if b then inr b else inl tt)).
Definition retry : itree (probE SubEnumQ) bool := ITree.iter retry_step tt.

Theorem retry_elaborates :
  elaborate_closed retry ≈ₚ PTree.iter (λ i, elaborate_closed (retry_step i)) tt.
Proof. apply free_omega_elab_iter. Qed.
