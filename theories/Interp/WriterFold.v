(** Canonical log-first WriterT fold, separate from the existing State-based
    PTree eliminator. Probability contributes no log and is not normalized. *)
Set Universe Polymorphism.
From ExtLib.Structures Require Import Monad Monoid.
From ITree.Basics Require Import Basics.
From ITree.Events Require Import Writer.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold WriterT.
Set Implicit Arguments.
Unset Strict Implicit.
Local Open Scope type_scope.

Section WriterFold.
Context {W : Type} {E MN T : Type -> Type} (op : Monoid W).
Context `{MT : Monad T} `{IT : MonadIter T}.
Variable handle : forall X, E X -> T X.
Variable sample : forall X, MN X -> T X.

Definition writer_effect {X} (e : (writerE W +' E) X) : Monads.writerT W T X :=
  match e with
  | inl1 we => match we in writerE _ X return T (W*X) with
      | Tell w => @ret T MT _ (w,tt) end
  | inr1 fe => @bind T MT _ _ (@handle X fe) (fun x => @ret T MT _ (monoid_unit op,x))
  end.

Definition writer_sample {X} (mu : MN X) : Monads.writerT W T X :=
  @bind T MT _ _ (@sample X mu) (fun x => @ret T MT _ (monoid_unit op,x)).

Definition fold_writer {A} (t : ptree (writerE W +' E) MN A) : T (W*A) :=
  @fold _ _ (Monads.writerT W T) (writerT_monad op) (writerT_iter op)
    (@writer_effect) (@writer_sample) A t.

Definition writer_fold_step {A} (st : W * ptree (writerE W +' E) MN A) :=
  writerT_step op
    (@fold_step _ _ (Monads.writerT W T) (writerT_monad op)
      (@writer_effect) (@writer_sample) A) st.

Lemma fold_writer_as_iter {A} (t : ptree (writerE W +' E) MN A) :
  fold_writer t = iter writer_fold_step (monoid_unit op,t).
Proof. reflexivity. Qed.

Lemma writer_sample_empty_log {X} (mu : MN X) :
  writer_sample mu = @bind T MT _ _ (@sample X mu) (fun x => @ret T MT _ (monoid_unit op,x)).
Proof. reflexivity. Qed.
End WriterFold.
