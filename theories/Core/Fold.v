(** General monadic interpretation: [fold] takes both the event and native
    sampling algebras; [interpM] selects the latter from the target.
    Monad/MonadIter operations suffice to define these functions, not to
    prove their equational laws. The productive [PTree.interp] remains the
    tree-to-tree interface; agreement is a separate behavioral theorem. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
From ExtLib.Structures Require Import Monad.
From ITree.Basics Require Import Basics.
From PTree.Core Require Import PTreeDefinition.
From PTree.Core Require Export MonadSample.
Set Implicit Arguments.
Unset Strict Implicit.

Section Fold.
Context {E MN T : Type → Type} `{MT : Monad T} `{IT : MonadIter T}.
Variable handle : ∀ X, E X → T X.
Variable sample : ∀ X, MN X → T X.

Definition fold_step {A} (t : ptree E MN A) : T (ptree E MN A + A) :=
  match observe t with
  | RetF a => ret (inr a)
  | TauF u => ret (inl u)
  | @VisF _ _ _ _ X e k => bind (@handle X e) (λ x, ret (inl (k x)))
  | @ProbF _ _ _ _ X mu k => bind (@sample X mu) (λ x, ret (inl (k x)))
  end.

Definition fold {A} (t : ptree E MN A) : T A :=
  iter fold_step t.

Lemma fold_step_ret {A} (a : A) : fold_step (Ret a) = ret (inr a).
Proof. reflexivity. Qed.
Lemma fold_step_tau {A} (t : ptree E MN A) : fold_step (Tau t) = ret (inl t).
Proof. reflexivity. Qed.
Lemma fold_step_vis {A X} (e : E X) (k : X → ptree E MN A) :
  fold_step (Vis e k) = bind (@handle X e) (λ x, ret (inl (k x))).
Proof. reflexivity. Qed.
Lemma fold_step_prob {A X} (mu : MN X) (k : X → ptree E MN A) :
  fold_step (Prob mu k) = bind (@sample X mu) (λ x, ret (inl (k x))).
Proof. reflexivity. Qed.
End Fold.

Definition interpM {E MN T : Type → Type}
    `{MT : Monad T} `{IT : MonadIter T} `{ST : MonadSample MN T}
    (handle : ∀ X, E X → T X) {A} (t : ptree E MN A) : T A :=
  fold handle (λ X mu, @msample MN T ST X mu) t.

Lemma interpM_as_fold {E MN T : Type → Type}
    `{MT : Monad T} `{IT : MonadIter T} `{ST : MonadSample MN T}
    (handle : ∀ X, E X → T X) {A} (t : ptree E MN A) :
  interpM handle t = fold handle (λ X mu, @msample MN T ST X mu) t.
Proof. reflexivity. Qed.
