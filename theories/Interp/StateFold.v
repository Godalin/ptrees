(** StateT consumer of the separate effect and sampling algebras. The target
    is ITree's state-first [Monads.stateT], not a newly defined transformer.
    These are definitional interfaces, not a claim that MonadIter operations
    alone imply handler/fold commutation or behavioral congruence. *)
Set Universe Polymorphism.
From ExtLib.Structures Require Import Monad.
From ITree.Basics Require Import Basics.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold.
Set Implicit Arguments.
Unset Strict Implicit.

Section StateFold.
Context {S : Type} {E MN T : Type -> Type} `{MT : Monad T} `{IT : MonadIter T}.
Variable handle : forall X, E X -> T X.
Variable sample : forall X, MN X -> T X.

Definition state_effect {X} (e : (stateE S +' E) X) : Monads.stateT S T X :=
  match e with
  | inl1 se =>
      match se in stateE _ X return Monads.stateT S T X with
      | Get => fun s => ret (s, s)
      | Put s' => fun _ => ret (s', tt)
      end
  | inr1 fe => fun s => bind (@handle _ fe) (fun x => ret (s, x))
  end.

Definition state_sample {X} (mu : MN X) : Monads.stateT S T X :=
  fun s => bind (@sample X mu) (fun x => ret (s, x)).

Definition fold_state {A} (t : ptree (stateE S +' E) MN A) : S -> T (S * A) :=
  fold (@state_effect) (@state_sample) t.

Lemma state_effect_get s : state_effect (inl1 (Get S)) s = ret (s, s).
Proof. reflexivity. Qed.
Lemma state_effect_put s s' : state_effect (inl1 (Put S s')) s = ret (s', tt).
Proof. reflexivity. Qed.
Lemma state_effect_forward {X} (e : E X) s :
  state_effect (inr1 e) s = bind (@handle X e) (fun x => ret (s, x)).
Proof. reflexivity. Qed.
Lemma state_sample_preserves_state {X} (mu : MN X) s :
  state_sample mu s = bind (@sample X mu) (fun x => ret (s, x)).
Proof. reflexivity. Qed.
End StateFold.
