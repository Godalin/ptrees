(** State elimination commutes with the separate Vis/Prob fold in a lawful
    monad with uniform iteration. No probability law is needed: handle and
    sample are arbitrary algebras. Uniformity is stated independently of
    PTree and is proved for an actual target in Execution/ITreeFold. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms.
From ExtLib.Structures Require Import Monad.
From ITree.Basics Require Import Basics Monad.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold IterationLaws.
From PTree.Interp Require Import State StateFold.
Set Implicit Arguments.
Unset Strict Implicit.
Local Open Scope type_scope.

Section StateFoldFacts.
Context {S : Type} {E MN T : Type -> Type}.
Context `{MT : Monad T} `{IT : MonadIter T} `{QT : Eq1 T}.
Context `{QE : @Eq1Equivalence T MT QT} `{ML : @MonadLawsE T QT MT}.
Variable handle : forall X, E X -> T X.
Variable sample : forall X, MN X -> T X.

Definition state_fold_step {A} (st : S * ptree (stateE S +' E) MN A) :
    T ((S * ptree (stateE S +' E) MN A) + (S * A)) :=
  bind (fold_step (@state_effect S E T MT handle)
                  (@state_sample S MN T MT sample) (snd st) (fst st))
    (fun sv => ret (match snd sv with
      | inl t => inl (fst sv, t)
      | inr a => inr (fst sv, a)
      end)).

Lemma fold_state_as_iter {A} (t : ptree (stateE S +' E) MN A) s :
  fold_state handle sample t s = iter state_fold_step (s,t).
Proof. reflexivity. Qed.

Lemma state_fold_square {A} (st : S * ptree (stateE S +' E) MN A) :
  eq1
    (bind (state_fold_step st)
      (fun v => ret (iteration_map (fun st => run_state (snd st) (fst st)) v)))
    (fold_step handle sample (run_state (snd st) (fst st))).
Proof.
  destruct st as [s t].
  unfold state_fold_step, fold_step. cbn [fst snd].
  rewrite observe_run_state.
  destruct (observe t) as [a|u|X e k|X mu k];
    cbn [state_effect state_sample Monads.Monad_stateT
         Monad.bind Monad.ret fst snd iteration_map].
  - rewrite !bind_ret_l. reflexivity.
  - rewrite !bind_ret_l. reflexivity.
  - destruct e as [se|fe].
    + destruct se; cbn [state_effect state_response Monads.Monad_stateT
        Monad.bind Monad.ret fst snd iteration_map];
        rewrite !bind_ret_l; reflexivity.
    + cbn [state_effect Monads.Monad_stateT Monad.bind Monad.ret fst snd].
      rewrite !bind_bind. apply Proper_bind; [reflexivity|]. intro x.
      rewrite !bind_ret_l. reflexivity.
  - unfold state_sample. rewrite !bind_bind. apply Proper_bind; [reflexivity|]. intro x.
    rewrite !bind_ret_l. reflexivity.
Qed.

Theorem fold_run_state (Hunif : @iteration_uniform T MT IT QT)
    {A} (t : ptree (stateE S +' E) MN A) s :
  eq1 (fold_state handle sample t s)
      (fold handle sample (run_state t s)).
Proof.
  rewrite fold_state_as_iter. unfold fold.
  apply (Hunif _ _ _ state_fold_step (fold_step handle sample)
    (fun st => run_state (snd st) (fst st))).
  apply state_fold_square.
Qed.
End StateFoldFacts.
