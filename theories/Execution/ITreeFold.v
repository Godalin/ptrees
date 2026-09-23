(** An actual lawful target for the generic execution fold. Sampling remains
    a separate supplied algebra into ITree; no claim of random correctness or
    peutt preservation follows merely from being such an algebra. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms.
From ITree.Basics Require Import Basics Monad.
From ITree.Core Require Import ITreeDefinition ITreeMonad KTreeFacts.
From ITree.Eq Require Import Eqit.
From ITree.Indexed Require Import Relation.
From PTree.Core Require Import PTreeDefinition Fold IterationLaws.
Set Implicit Arguments.
Unset Strict Implicit.

Theorem itree_iteration_uniform {E : Type -> Type} :
  @iteration_uniform (itree E) _ _ Eq1_ITree.
Proof.
  intros I J A f g h Hsquare i.
  cbn [eq1 Eq1_ITree Basics.iter MonadIter_itree] in *.
  eapply (eutt_iter' (fun i j => h i = j) eq).
  - intros x y Hy. subst y.
    rewrite <- (Hsquare x).
    rewrite <- (bind_ret_r (f x)) at 1.
    cbn [Monad.bind Monad.ret Monad_itree].
    eapply eutt_clo_bind with (UU := eq); [reflexivity|].
    intros v w Hw. subst w.
    apply eqit_Ret. destruct v; constructor; reflexivity.
  - reflexivity.
Qed.

Section FoldEquations.
Context {E MN F : Type -> Type}.
Variable handle : forall X, E X -> itree F X.
Variable sample : forall X, MN X -> itree F X.

Lemma itree_fold_unfold {A} (t : ptree E MN A) :
  eutt eq (fold handle sample t)
    (ITree.bind (fold_step handle sample t) (fun v =>
      match v with inl u => fold handle sample u | inr a => ITreeDefinition.Ret a end)).
Proof.
  change (eutt eq (ITree.iter (fold_step handle sample) t)
    (ITree.bind (fold_step handle sample t) (fun v =>
      match v with inl u => fold handle sample u | inr a => ITreeDefinition.Ret a end))).
  rewrite unfold_iter.
  apply eqit_bind; [reflexivity|]. intros [u|a]; cbn.
  - apply tau_eutt.
  - reflexivity.
Qed.

Lemma itree_fold_ret {A} (a : A) :
  eutt eq (fold handle sample (Ret a)) (ITreeDefinition.Ret a).
Proof.
  rewrite itree_fold_unfold, fold_step_ret.
  cbn [Monad.ret Monad_itree]. rewrite bind_ret_l. reflexivity.
Qed.

Lemma itree_fold_tau {A} (t : ptree E MN A) :
  eutt eq (fold handle sample (Tau t)) (fold handle sample t).
Proof.
  rewrite itree_fold_unfold, fold_step_tau.
  cbn [Monad.ret Monad_itree]. rewrite bind_ret_l. reflexivity.
Qed.

Lemma itree_fold_vis {A X} (e : E X) (k : X -> ptree E MN A) :
  eutt eq (fold handle sample (Vis e k))
    (ITree.bind (@handle X e) (fun x => fold handle sample (k x))).
Proof.
  rewrite itree_fold_unfold, fold_step_vis. cbn [Monad.bind Monad.ret Monad_itree].
  rewrite bind_bind. apply eqit_bind; [reflexivity|]. intro x.
  rewrite bind_ret_l. reflexivity.
Qed.

Lemma itree_fold_prob {A X} (mu : MN X) (k : X -> ptree E MN A) :
  eutt eq (fold handle sample (Prob mu k))
    (ITree.bind (@sample X mu) (fun x => fold handle sample (k x))).
Proof.
  rewrite itree_fold_unfold, fold_step_prob. cbn [Monad.bind Monad.ret Monad_itree].
  rewrite bind_bind. apply eqit_bind; [reflexivity|]. intro x.
  rewrite bind_ret_l. reflexivity.
Qed.
End FoldEquations.
