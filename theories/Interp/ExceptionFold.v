(** Exception elimination into ExtLib [eitherT]. Native sampling is lifted
    through [inr], never interpreted as an exception or normalized. *)
Set Universe Polymorphism.
From ExtLib.Structures Require Import Monad.
From ExtLib.Data.Monads Require Import EitherMonad.
From ITree.Basics Require Import Basics.
From ITree.Events Require Import Exception.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold.
From PTree.Interp Require Import Exception.
Set Implicit Arguments.
Unset Strict Implicit.

Section ExceptionFold.
Context {Err : Type} {E MN T : Type -> Type} `{MT : Monad T} `{IT : MonadIter T}.
Variable handle : forall X, E X -> T X.
Variable sample : forall X, MN X -> T X.

Definition exception_effect {X} (e : (exceptE Err +' E) X) : eitherT Err T X :=
  mkEitherT (match e with
    | inl1 ex => ret (inl (exception_value ex))
    | inr1 fe => bind (@handle X fe) (fun x => ret (inr x))
    end).

Definition exception_sample {X} (mu : MN X) : eitherT Err T X :=
  mkEitherT (bind (@sample X mu) (fun x => ret (inr x))).

Definition fold_exception {A} (t : ptree (exceptE Err +' E) MN A) : T (Err+A) :=
  unEitherT (fold (@exception_effect) (@exception_sample) t).

Lemma exception_effect_throw err :
  unEitherT (exception_effect (inl1 (Throw err))) = ret (inl err).
Proof. reflexivity. Qed.
Lemma exception_effect_forward {X} (e : E X) :
  unEitherT (exception_effect (inr1 e)) = bind (@handle X e) (fun x => ret (inr x)).
Proof. reflexivity. Qed.
Lemma exception_sample_success {X} (mu : MN X) :
  unEitherT (exception_sample mu) = bind (@sample X mu) (fun x => ret (inr x)).
Proof. reflexivity. Qed.
End ExceptionFold.
