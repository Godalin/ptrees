(** Monadic execution algebra. Unlike tree-to-tree [PTree.interp], [fold]
    consumes visible events AND native probability nodes. Probability is a
    separate algebra, never re-encoded as a visible event. Monad/MonadIter
    operations suffice to define it; equational laws are separate obligations. *)
Set Universe Polymorphism.
From ExtLib.Structures Require Import Monad.
From ITree.Basics Require Import Basics.
From PTree.Core Require Import PTreeDefinition.
Set Implicit Arguments.
Unset Strict Implicit.

Section Fold.
Context {E MN T : Type -> Type} `{MT : Monad T} `{IT : MonadIter T}.
Variable handle : forall X, E X -> T X.
Variable sample : forall X, MN X -> T X.

Definition fold_step {A} (t : ptree E MN A) : T (ptree E MN A + A) :=
  match observe t with
  | RetF a => ret (inr a)
  | TauF u => ret (inl u)
  | @VisF _ _ _ _ X e k => bind (@handle X e) (fun x => ret (inl (k x)))
  | @ProbF _ _ _ _ X mu k => bind (@sample X mu) (fun x => ret (inl (k x)))
  end.

Definition fold {A} (t : ptree E MN A) : T A :=
  iter fold_step t.

Lemma fold_step_ret {A} (a : A) : fold_step (Ret a) = ret (inr a).
Proof. reflexivity. Qed.
Lemma fold_step_tau {A} (t : ptree E MN A) : fold_step (Tau t) = ret (inl t).
Proof. reflexivity. Qed.
Lemma fold_step_vis {A X} (e : E X) (k : X -> ptree E MN A) :
  fold_step (Vis e k) = bind (@handle X e) (fun x => ret (inl (k x))).
Proof. reflexivity. Qed.
Lemma fold_step_prob {A X} (mu : MN X) (k : X -> ptree E MN A) :
  fold_step (Prob mu k) = bind (@sample X mu) (fun x => ret (inl (k x))).
Proof. reflexivity. Qed.
End Fold.
