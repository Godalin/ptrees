(** StateT consumer of the separate effect and sampling algebras. The target
    is ITree's state-first [Monads.stateT], not a newly defined transformer.
    These are definitional interfaces, not a claim that MonadIter operations
    alone imply handler/fold commutation or behavioral congruence. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
From ExtLib.Structures Require Import Monad.
From ITree.Basics Require Import Basics.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold.
Set Implicit Arguments.
Unset Strict Implicit.

Section StateFold.
Context {S : Type} {E MN T : Type → Type} `{MT : Monad T} `{IT : MonadIter T}.
Variable handle : ∀ X, E X → T X.
Variable sample : ∀ X, MN X → T X.

Definition state_effect {X} (e : (stateE S +' E) X) : Monads.stateT S T X :=
  match e with
  | inl1 se =>
      match se in stateE _ X return Monads.stateT S T X with
      | Get => λ s, ret (s, s)
      | Put s' => λ _, ret (s', tt)
      end
  | inr1 fe => λ s, bind (@handle _ fe) (λ x, ret (s, x))
  end.

Definition state_sample {X} (mu : MN X) : Monads.stateT S T X :=
  λ s, bind (@sample X mu) (λ x, ret (s, x)).

Definition fold_state {A} (t : ptree (stateE S +' E) MN A) : S → T (S * A) :=
  fold (@state_effect) (@state_sample) t.

Lemma state_effect_get s : state_effect (inl1 (Get S)) s = ret (s, s).
Proof. reflexivity. Qed.
Lemma state_effect_put s s' : state_effect (inl1 (Put S s')) s = ret (s', tt).
Proof. reflexivity. Qed.
Lemma state_effect_forward {X} (e : E X) s :
  state_effect (inr1 e) s = bind (@handle X e) (λ x, ret (s, x)).
Proof. reflexivity. Qed.
Lemma state_sample_preserves_state {X} (mu : MN X) s :
  state_sample mu s = bind (@sample X mu) (λ x, ret (s, x)).
Proof. reflexivity. Qed.
End StateFold.

Local Unset Universe Minimization ToSet.

(** Lift precisely the existing sampling algebra; state is threaded, not
    sampled or reset. There is no additional probability-law assumption. *)
#[global] Instance MonadSample_stateT {S MN T}
    `{MT : Monad T} `{ST : MonadSample MN T} :
    MonadSample MN (Monads.stateT S T) :=
  {| msample := @state_sample S MN T MT (λ X mu, @msample MN T ST X mu) |}.

Definition interp_state {S : Type} {E MN T : Type → Type} `{MT : Monad T} `{IT : MonadIter T}
    `{ST : MonadSample MN T} (handle : ∀ X, E X → T X)
    {A} (t : ptree (stateE S +' E) MN A) : S → T (S * A)%type :=
  interp (@state_effect S E T MT handle) t.

Lemma interp_state_as_fold {S : Type} {E MN T : Type → Type} `{MT : Monad T} `{IT : MonadIter T}
    `{ST : MonadSample MN T} (handle : ∀ X, E X → T X)
    {A} (t : ptree (stateE S +' E) MN A) :
  interp_state handle t =
    fold_state handle (λ X mu, @msample MN T ST X mu) t.
Proof. reflexivity. Qed.
