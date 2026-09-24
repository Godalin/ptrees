(** Agreement with the existing interp-based Reader eliminator in an actual
    lawful ITree target. Administrative Tau is proved harmless, not removed
    from the PTree implementation. This is not a bare-MonadIter theorem. *)
Set Universe Polymorphism.
From Coq Require Import RelationClasses Morphisms.
From Paco Require Import paco.
From ExtLib.Data.Monads Require Import ReaderMonad.
From ITree.Basics Require Import Basics Monad.
From ITree.Core Require Import ITreeDefinition ITreeMonad KTreeFacts.
From ITree.Eq Require Import Eqit UpToTaus Paco2.
From ITree.Events Require Import Reader.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold.
From PTree.Eq Require Import Shallow.
From PTree.Interp Require Import Reader ReaderFold FoldITree.
Set Implicit Arguments.
Unset Strict Implicit.

Section ReaderFoldITree.
Context {Env : Type} {E MN F : Type -> Type}.
Variable handle : forall X, E X -> itree F X.
Variable sample : forall X, MN X -> itree F X.

Lemma itree_reader_fold_observe {A} (t : ptree (readerE Env +' E) MN A) env :
  eq_itree eq (fold_reader handle sample t env)
    (match observe t with
     | RetF a => ITreeDefinition.Ret a
     | TauF u => ITreeDefinition.Tau (fold_reader handle sample u env)
     | @VisF _ _ _ _ X e k => match e with
         | inl1 re => match re in readerE _ X return (X -> _) -> _ with
             | Ask => fun k => ITreeDefinition.Tau (fold_reader handle sample (k env) env)
             end k
         | inr1 fe => ITree.bind (@handle X fe)
             (fun x => ITreeDefinition.Tau (fold_reader handle sample (k x) env))
         end
     | @ProbF _ _ _ _ X mu k => ITree.bind (@sample X mu)
         (fun x => ITreeDefinition.Tau (fold_reader handle sample (k x) env))
     end).
Proof.
  rewrite fold_reader_as_iter.
  change (Basics.iter (reader_fold_step handle sample env) t)
    with (ITree.iter (reader_fold_step handle sample env) t).
  rewrite unfold_iter. unfold reader_fold_step, fold_step.
  destruct (observe t) as [a|u|X e k|X mu k];
    cbn [reader_effect reader_sample Monad_readerT runReaderT Monad.bind Monad.ret ITreeDefinition.Monad_itree];
    rewrite ?bind_ret_l; try reflexivity.
  - destruct e as [re|fe].
    + destruct re. cbn [reader_effect Monad_readerT runReaderT Monad.bind Monad.ret ITreeDefinition.Monad_itree].
      rewrite !bind_ret_l. reflexivity.
    + cbn [reader_effect Monad_readerT runReaderT Monad.bind Monad.ret ITreeDefinition.Monad_itree].
      rewrite bind_bind. apply eqit_bind; [reflexivity|]. intro x.
      rewrite bind_ret_l. reflexivity.
  - rewrite bind_bind. apply eqit_bind; [reflexivity|]. intro x.
    rewrite bind_ret_l. reflexivity.
Qed.

Theorem itree_fold_run_reader {A} (t : ptree (readerE Env +' E) MN A) env :
  eutt eq (fold_reader handle sample t env)
    (fold handle sample (run_reader t env)).
Proof.
  revert t. einit. ecofix CIH. intro t.
  rewrite itree_reader_fold_observe, itree_fold_observe.
  unfold run_reader at 1. rewrite observe_interp.
  destruct (observe t) as [a|u|X e k|X mu k]; cbn.
  - apply reflexivity.
  - etau.
  - destruct e as [re|fe].
    + destruct re. cbn [reader_handler].
      rewrite itree_fold_bind, itree_fold_observe. cbn [observe _observe].
      rewrite bind_ret_l. etau.
    + cbn [reader_handler]. rewrite tau_euttge, itree_fold_bind, itree_fold_observe.
      cbn [observe _observe]. rewrite bind_bind.
      ebind; econstructor; try reflexivity. intros x y Hxy. subst y.
      rewrite bind_tau, itree_fold_observe. cbn [observe _observe].
      rewrite !bind_ret_l. etau.
  - ebind; econstructor; try reflexivity. intros x y Hxy. subst y.
    etau.
Qed.

Theorem itree_reader_fold_bind {A B} (t : ptree (readerE Env +' E) MN A)
    (k : A -> ptree (readerE Env +' E) MN B) env :
  eq_itree eq (fold_reader handle sample (PTree.bind t k) env)
    (ITree.bind (fold_reader handle sample t env) (fun a => fold_reader handle sample (k a) env)).
Proof.
  revert t. ginit. pcofix CIH. intro t.
  rewrite (itree_reader_fold_observe (PTree.bind t k) env),
    (itree_reader_fold_observe t env), observe_bind.
  destruct (observe t) as [a|u|X e c|X mu c]; cbn.
  - rewrite bind_ret_l, (itree_reader_fold_observe (k a) env). apply reflexivity.
  - rewrite bind_tau. gstep. constructor. eauto with paco.
  - destruct e as [re|fe].
    + destruct re. cbn. rewrite bind_tau. gstep. constructor. eauto with paco.
    + cbn. rewrite bind_bind. guclo eqit_clo_bind. econstructor; [reflexivity|].
      intros x y Hxy. subst y. rewrite bind_tau. gstep. constructor. eauto with paco.
  - rewrite bind_bind. guclo eqit_clo_bind. econstructor; [reflexivity|].
    intros x y Hxy. subst y. rewrite bind_tau. gstep. constructor. eauto with paco.
Qed.
Lemma itree_reader_fold_ret {A} (a : A) (env : Env) :
  eq_itree eq (fold_reader handle sample (Ret a) env) (ITreeDefinition.Ret a).
Proof. rewrite itree_reader_fold_observe. reflexivity. Qed.
End ReaderFoldITree.
