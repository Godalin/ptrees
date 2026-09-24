(** A genuine transformer/eliminator commuting square. Uniform iteration is
    an explicit target law; arbitrary MonadIter operations do not suffice.
    No probability capability, totality, or FreeOmega model is involved. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms.
From ExtLib.Structures Require Import Monad.
From ExtLib.Data.Monads Require Import EitherMonad.
From ITree.Basics Require Import Basics Monad.
From ITree.Events Require Import Exception.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold IterationLaws ExceptT.
From PTree.Interp Require Import Exception ExceptionFold.
Set Implicit Arguments.
Unset Strict Implicit.
Local Open Scope type_scope.

Section ExceptionFoldFacts.
Context {Err : Type} {E MN T : Type -> Type}.
Context `{MT : Monad T} `{IT : MonadIter T} `{QT : Eq1 T}.
Context `{QE : @Eq1Equivalence T MT QT} `{ML : @MonadLawsE T QT MT}.
Variable handle : forall X, E X -> T X.
Variable sample : forall X, MN X -> T X.

Definition exception_fold_step {A} (t : ptree (exceptE Err +' E) MN A) :
    T (ptree (exceptE Err +' E) MN A + (Err+A)) :=
  exceptT_step (fold_step (@exception_effect Err E T MT handle)
                         (@exception_sample Err MN T MT sample)) t.

Lemma fold_exception_as_iter {A} (t : ptree (exceptE Err +' E) MN A) :
  fold_exception handle sample t = iter exception_fold_step t.
Proof. reflexivity. Qed.

Lemma exception_fold_square {A} (t : ptree (exceptE Err +' E) MN A) :
  eq1
    (bind (exception_fold_step t)
      (fun v => ret (iteration_map (@run_exception Err E MN A) v)))
    (fold_step handle sample (run_exception t)).
Proof.
  unfold exception_fold_step, exceptT_step, fold_step.
  rewrite observe_run_exception.
  destruct (observe t) as [a|u|X e k|X mu k];
    cbn [exception_effect exception_sample Monad_eitherT
         Monad.bind Monad.ret unEitherT iteration_map].
  - rewrite !bind_ret_l. reflexivity.
  - rewrite !bind_ret_l. reflexivity.
  - destruct e as [ex|fe].
    + cbn [exception_effect Monad_eitherT Monad.bind Monad.ret unEitherT].
      rewrite !bind_ret_l. reflexivity.
    + cbn [exception_effect Monad_eitherT Monad.bind Monad.ret unEitherT].
      rewrite !bind_bind. apply Proper_bind; [reflexivity|]. intro x.
      rewrite !bind_ret_l. reflexivity.
  - unfold exception_sample. rewrite !bind_bind.
    apply Proper_bind; [reflexivity|]. intro x.
    rewrite !bind_ret_l. reflexivity.
Qed.

Theorem fold_run_exception (Hunif : @iteration_uniform T MT IT QT)
    {A} (t : ptree (exceptE Err +' E) MN A) :
  eq1 (fold_exception handle sample t)
      (fold handle sample (run_exception t)).
Proof.
  rewrite fold_exception_as_iter. unfold fold.
  apply (Hunif _ _ _ exception_fold_step (fold_step handle sample)
    (@run_exception Err E MN A)).
  apply exception_fold_square.
Qed.
End ExceptionFoldFacts.
