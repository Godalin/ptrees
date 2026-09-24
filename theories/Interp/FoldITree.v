(** Computational algebra of the actual ITree fold. Iteration-generated Tau
    is retained in strong equations and supplies guards in the bind proof.
    Sampling is still an arbitrary, separate supplied algebra. *)
Set Universe Polymorphism.
From Coq Require Import RelationClasses Morphisms.
From Paco Require Import paco.
From ITree.Basics Require Import Basics Monad.
From ITree.Core Require Import ITreeDefinition ITreeMonad KTreeFacts.
From ITree.Eq Require Import Eqit UpToTaus Paco2.
From PTree.Core Require Import PTreeDefinition Fold.
From PTree.Eq Require Import Shallow.
Set Implicit Arguments.
Unset Strict Implicit.

Definition itree_strong_eq1 {F} : Eq1 (itree F) := fun A => @eq_itree F A A eq.
Definition itree_strong_equivalence {F} :
    @Eq1Equivalence (itree F) _ itree_strong_eq1.
Proof. intro A. apply Equivalence_eqit; typeclasses eauto. Defined.
Definition itree_strong_monad_laws {F} :
    @MonadLawsE (itree F) itree_strong_eq1 _.
Proof.
  constructor; intros; unfold eq1, itree_strong_eq1;
    cbn [Monad.bind Monad.ret ITreeDefinition.Monad_itree].
  - rewrite bind_ret_l. reflexivity.
  - apply bind_ret_r.
  - apply bind_bind.
  - intros x y Hxy f g Hfg. apply eqit_bind; assumption.
Defined.

Section ITreeAlgebra.
Context {E MN F : Type -> Type}.
Variable handle : forall X, E X -> itree F X.
Variable sample : forall X, MN X -> itree F X.

Lemma itree_fold_observe {A} (t : ptree E MN A) :
  eq_itree eq (fold handle sample t)
    (match observe t with
     | RetF a => ITreeDefinition.Ret a
     | TauF u => ITreeDefinition.Tau (fold handle sample u)
     | @VisF _ _ _ _ X e k => ITree.bind (@handle X e)
         (fun x => ITreeDefinition.Tau (fold handle sample (k x)))
     | @ProbF _ _ _ _ X mu k => ITree.bind (@sample X mu)
         (fun x => ITreeDefinition.Tau (fold handle sample (k x)))
     end).
Proof.
  unfold fold at 1.
  change (Basics.iter (fold_step handle sample) t) with (ITree.iter (fold_step handle sample) t).
  rewrite unfold_iter. unfold fold_step. destruct (observe t);
    cbn [Monad.bind Monad.ret Monad_itree]; rewrite ?bind_ret_l; try reflexivity.
  all: rewrite bind_bind; apply eqit_bind; [reflexivity|intro x]; rewrite bind_ret_l; reflexivity.
Qed.

Lemma itree_fold_observe_eq {A} (t u : ptree E MN A) :
  observe t = observe u -> eq_itree eq (fold handle sample t) (fold handle sample u).
Proof. intro H. rewrite (itree_fold_observe t), (itree_fold_observe u), H. reflexivity. Qed.

Lemma itree_fold_bind {A B} (t : ptree E MN A) (k : A -> ptree E MN B) :
  eq_itree eq (fold handle sample (PTree.bind t k))
    (ITree.bind (fold handle sample t) (fun a => fold handle sample (k a))).
Proof.
  revert t. ginit. pcofix CIH. intro t.
  rewrite (itree_fold_observe (PTree.bind t k)), (itree_fold_observe t).
  rewrite observe_bind. destruct (observe t); cbn.
  - rewrite bind_ret_l. rewrite <- itree_fold_observe. apply reflexivity.
  - rewrite bind_tau. gstep. constructor. eauto with paco.
  - rewrite bind_bind. guclo eqit_clo_bind. econstructor; [reflexivity|].
    intros x y Hxy. subst y. rewrite bind_tau. gstep. constructor. eauto with paco.
  - rewrite bind_bind. guclo eqit_clo_bind. econstructor; [reflexivity|].
    intros x y Hxy. subst y. rewrite bind_tau. gstep. constructor. eauto with paco.
Qed.
End ITreeAlgebra.
