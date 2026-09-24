(** Explicit laws for ExtLib ReaderT and ITree's pointwise iterator.
    No competing transformer or global instance is introduced. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms RelationClasses.
From ExtLib.Structures Require Import Monad.
From ExtLib.Data.Monads Require Import ReaderMonad.
From ITree.Basics Require Import Basics Monad.
From PTree.Core Require Import IterationLaws.
Set Implicit Arguments.
Unset Strict Implicit.

Section ReaderT.
Context {Env : Type} {T : Type -> Type}.
Context `{MT : Monad T} `{QT : Eq1 T}.

Definition readerT_eq1 : Eq1 (readerT Env T) :=
  fun A x y => forall env, eq1 (runReaderT x env) (runReaderT y env).

Definition readerT_eq_equivalence (QE : @Eq1Equivalence T MT QT) :
    @Eq1Equivalence (readerT Env T) (@Monad_readerT Env T MT) readerT_eq1.
Proof.
  intro A. destruct (QE A) as [Hr Hs Ht].
  split; unfold Reflexive, Symmetric, Transitive, eq1, readerT_eq1; eauto.
Defined.

Context `{QE : @Eq1Equivalence T MT QT} `{ML : @MonadLawsE T QT MT}.

Definition readerT_monad_laws :
    @MonadLawsE (readerT Env T) readerT_eq1 (@Monad_readerT Env T MT).
Proof.
  constructor; intros; unfold eq1, readerT_eq1;
    cbn [Monad.bind Monad.ret Monad_readerT runReaderT].
  - intro env. apply (@bind_ret_l T QT MT ML).
  - intro env. apply (@bind_ret_r T QT MT ML).
  - intro env. apply (@bind_bind T QT MT ML).
  - intros x y Hxy f g Hfg env.
    apply Proper_bind; [apply Hxy|]. intro a. apply Hfg.
Defined.

Theorem readerT_iteration_uniform `{IT : MonadIter T}
    (Hunif : @iteration_uniform T MT IT QT) :
    @iteration_uniform (readerT Env T) (@Monad_readerT Env T MT)
      (@MonadIter_readerT T Env IT) readerT_eq1.
Proof.
  intros I J A f g h Hsquare i env.
  apply (Hunif I J A (fun i => runReaderT (f i) env)
    (fun j => runReaderT (g j) env) h).
  intro j. exact (Hsquare j env).
Qed.
End ReaderT.
