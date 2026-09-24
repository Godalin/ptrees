(** ReaderT fold: the environment is fixed and native sampling is lifted
    independently of it. Uses ExtLib's existing record transformer. *)
Set Universe Polymorphism.
From ExtLib.Structures Require Import Monad.
From ExtLib.Data.Monads Require Import ReaderMonad.
From ITree.Basics Require Import Basics.
From ITree.Events Require Import Reader.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold.
Set Implicit Arguments.
Unset Strict Implicit.

Section ReaderFold.
Context {Env : Type} {E MN T : Type -> Type} `{MT : Monad T} `{IT : MonadIter T}.
Variable handle : forall X, E X -> T X.
Variable sample : forall X, MN X -> T X.

Definition reader_effect {X} (e : (readerE Env +' E) X) : readerT Env T X :=
  mkReaderT (fun env => match e with
    | inl1 re => match re in readerE _ X return T X with Ask => ret env end
    | inr1 fe => @handle X fe end).

Definition reader_sample {X} (mu : MN X) : readerT Env T X :=
  mkReaderT (fun _ => @sample X mu).

Definition fold_reader {A} (t : ptree (readerE Env +' E) MN A) env : T A :=
  runReaderT (fold (@reader_effect) (@reader_sample) t) env.

Definition reader_fold_step {A} env (t : ptree (readerE Env +' E) MN A) :=
  runReaderT (fold_step (@reader_effect) (@reader_sample) t) env.

Lemma fold_reader_as_iter {A} (t : ptree (readerE Env +' E) MN A) env :
  fold_reader t env = iter (reader_fold_step env) t.
Proof. reflexivity. Qed.

Lemma reader_sample_independent {X} (mu : MN X) env :
  runReaderT (reader_sample mu) env = @sample X mu.
Proof. reflexivity. Qed.
End ReaderFold.
