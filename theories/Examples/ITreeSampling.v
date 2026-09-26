(** Case role: supporting example.
    Proof mode: algebraic rewriting.
    Reading entry: two_coins_elaborates; retry_elaborates.
    Scope: SubEnumQ / observable FreeOmega; iteration preservation does not assert AST.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
(** ITree sampling-as-an-effect elaborated to primitive PTree probability.
    The source really is an [itree], not a PTree reusing an event signature. *)
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
From PTree.Prob.Backend.Common Require Import FiniteEnum.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.
Import FreeOmegaRewriting.

Definition fair_entries : list (rat * bool) := [(2^-1,true); (2^-1,false)].
Lemma fair_nonnegative : finite_nonnegative fair_entries.
Proof. intros p b [H|[H|[]]]; inversion H; subst; native_compute; reflexivity. Qed.
Lemma fair_bounded : finite_expect (fun _ => 1) fair_entries <= 1.
Proof. native_compute. reflexivity. Qed.
Definition fair_coin : SubEnumQ bool := subenumQ_of_list fair_nonnegative fair_bounded.

Definition two_coins : itree (probE SubEnumQ) bool :=
  ITree.bind (ITree.trigger (Sample fair_coin)) (fun x =>
  ITree.bind (ITree.trigger (Sample fair_coin)) (fun y =>
  ITreeDefinition.Ret (xorb x y))).

Definition native_two_coins : ptree void1 SubEnumQ bool :=
  PTree.bind (Prob fair_coin (fun x => Ret x)) (fun x =>
  PTree.bind (Prob fair_coin (fun y => Ret y)) (fun y =>
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
  ITree.bind (ITree.trigger (Sample fair_coin)) (fun b =>
    ITreeDefinition.Ret (if b then inr b else inl tt)).
Definition retry : itree (probE SubEnumQ) bool := ITree.iter retry_step tt.

Theorem retry_elaborates :
  elaborate_closed retry ≈ₚ PTree.iter (fun i => elaborate_closed (retry_step i)) tt.
Proof. apply free_omega_elab_iter. Qed.
