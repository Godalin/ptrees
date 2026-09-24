(** Canonical WriterT agrees with the existing State-based Writer eliminator
    for the actual ITree target. No commutativity or probability law is used. *)
Set Universe Polymorphism.
From Coq Require Import RelationClasses Morphisms.
From Paco Require Import paco.
From ExtLib.Structures Require Import Monoid.
From ITree.Basics Require Import Basics Monad.
From ITree.Core Require Import ITreeDefinition ITreeMonad KTreeFacts.
From ITree.Eq Require Import Eqit UpToTaus Paco2.
From ITree.Events Require Import Writer State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold WriterT.
From PTree.Eq Require Import Shallow.
From PTree.Interp Require Import State Writer WriterFold WriterFoldFacts FoldITree.
Set Implicit Arguments.
Unset Strict Implicit.

Section WriterFoldITree.
Context {W : Type} {E MN F : Type -> Type} (op : Monoid W) (WL : MonoidLaws op).
Variable handle : forall X, E X -> itree F X.
Variable sample : forall X, MN X -> itree F X.

Definition itree_writer_from {A} (t : ptree (writerE W +' E) MN A) log : itree F (W*A) :=
  ITree.iter (writer_fold_step op handle sample) (log,t).

Lemma itree_state_bind_ret {X A} (x : X) (k : X -> ptree (stateE W +' E) MN A) log :
  eq_itree eq (fold handle sample (run_state (PTree.bind (Ret x) k) log))
    (fold handle sample (run_state (k x) log)).
Proof.
  apply itree_fold_observe_eq. rewrite !observe_run_state, observe_bind. reflexivity.
Qed.

Lemma itree_writer_fold_observe {A} (t : ptree (writerE W +' E) MN A) log :
  eq_itree eq (itree_writer_from t log)
    (match observe t with
     | RetF a => ITreeDefinition.Ret (log,a)
     | TauF u => ITreeDefinition.Tau (itree_writer_from u log)
     | @VisF _ _ _ _ X e k => match e with
         | inl1 we => match we in writerE _ X return (X -> _) -> _ with
             | Tell w => fun k => ITreeDefinition.Tau (itree_writer_from (k tt) (monoid_plus op log w))
             end k
         | inr1 fe => ITree.bind (@handle X fe)
             (fun x => ITreeDefinition.Tau (itree_writer_from (k x) log)) end
     | @ProbF _ _ _ _ X mu k => ITree.bind (@sample X mu)
         (fun x => ITreeDefinition.Tau (itree_writer_from (k x) log))
     end).
Proof.
  unfold itree_writer_from at 1. rewrite unfold_iter.
  rewrite (@writer_fold_step_normalize W E MN (itree F) op _
    itree_strong_eq1 itree_strong_equivalence itree_strong_monad_laws WL handle sample A t log).
  unfold writer_next. destruct (observe t) as [a|u|X e k|X mu k];
    cbn [Monad.bind Monad.ret ITreeDefinition.Monad_itree]; rewrite ?bind_ret_l; try reflexivity.
  - destruct e as [we|fe].
    + destruct we. cbn. rewrite bind_ret_l. reflexivity.
    + cbn. rewrite bind_bind. apply eqit_bind; [reflexivity|]. intro x.
      rewrite bind_ret_l. reflexivity.
  - rewrite bind_bind. apply eqit_bind; [reflexivity|]. intro x.
    rewrite bind_ret_l. reflexivity.
Qed.

Theorem itree_fold_run_writer_from {A} (t : ptree (writerE W +' E) MN A) log :
  eutt eq (itree_writer_from t log)
    (fold handle sample (run_state (PTree.interp (writer_handler op) t) log)).
Proof.
  revert t log. einit. ecofix CIH. intros t log.
  rewrite itree_writer_fold_observe, itree_fold_observe.
  rewrite observe_run_state, observe_interp.
  destruct (observe t) as [a|u|X e k|X mu k]; cbn.
  - apply reflexivity.
  - etau.
  - destruct e as [we|fe].
    + destruct we. cbn [writer_handler].
      rewrite itree_fold_observe.
      rewrite observe_run_state, observe_bind. cbn [observe _observe state_response].
      rewrite itree_fold_observe.
      rewrite observe_run_state, observe_bind. cbn [observe _observe state_response].
      rewrite itree_state_bind_ret. etau. rewrite !tau_euttge. ebase.
    + cbn [writer_handler]. rewrite tau_euttge, itree_fold_observe.
      rewrite observe_run_state, observe_bind. cbn [observe _observe].
      ebind; econstructor; try reflexivity. intros x y Hxy. subst y.
      rewrite itree_state_bind_ret. etau.
  - ebind; econstructor; try reflexivity. intros x y Hxy. subst y. etau.
Qed.

Theorem itree_fold_run_writer {A} (t : ptree (writerE W +' E) MN A) :
  eutt eq (fold_writer op handle sample t)
    (fold handle sample (run_writer op t)).
Proof. apply itree_fold_run_writer_from. Qed.

Lemma itree_writer_prefix {A} (t : ptree (writerE W +' E) MN A) prefix log :
  eq_itree eq (itree_writer_from t (monoid_plus op prefix log))
    (ITree.bind (itree_writer_from t log)
      (fun wa => ITreeDefinition.Ret (monoid_plus op prefix (fst wa),snd wa))).
Proof.
  revert t log. ginit. pcofix CIH. intros t log.
  rewrite !itree_writer_fold_observe.
  destruct (observe t) as [a|u|X e k|X mu k]; cbn.
  - rewrite bind_ret_l. apply reflexivity.
  - rewrite bind_tau. gstep. constructor. eauto with paco.
  - destruct e as [we|fe].
    + destruct we. cbn. rewrite bind_tau, (@monoid_assoc W op WL).
      gstep. constructor. eauto with paco.
    + cbn. rewrite bind_bind. guclo eqit_clo_bind. econstructor; [reflexivity|].
      intros x y Hxy. subst y. rewrite bind_tau. gstep. constructor. eauto with paco.
  - rewrite bind_bind. guclo eqit_clo_bind. econstructor; [reflexivity|].
    intros x y Hxy. subst y. rewrite bind_tau. gstep. constructor. eauto with paco.
Qed.

Lemma itree_writer_bind_from {A B} (t : ptree (writerE W +' E) MN A)
    (k : A -> ptree (writerE W +' E) MN B) log :
  eq_itree eq (itree_writer_from (PTree.bind t k) log)
    (ITree.bind (itree_writer_from t log) (fun wa => itree_writer_from (k (snd wa)) (fst wa))).
Proof.
  revert t log. ginit. pcofix CIH. intros t log.
  rewrite (itree_writer_fold_observe (PTree.bind t k) log),
    (itree_writer_fold_observe t log), observe_bind.
  destruct (observe t) as [a|u|X e c|X mu c]; cbn.
  - rewrite bind_ret_l, <- itree_writer_fold_observe. apply reflexivity.
  - rewrite bind_tau. gstep. constructor. eauto with paco.
  - destruct e as [we|fe].
    + destruct we. cbn. rewrite bind_tau. gstep. constructor. eauto with paco.
    + cbn. rewrite bind_bind. guclo eqit_clo_bind. econstructor; [reflexivity|].
      intros x y Hxy. subst y. rewrite bind_tau. gstep. constructor. eauto with paco.
  - rewrite bind_bind. guclo eqit_clo_bind. econstructor; [reflexivity|].
    intros x y Hxy. subst y. rewrite bind_tau. gstep. constructor. eauto with paco.
Qed.

Theorem itree_writer_fold_bind {A B} (t : ptree (writerE W +' E) MN A)
    (k : A -> ptree (writerE W +' E) MN B) :
  eq_itree eq (fold_writer op handle sample (PTree.bind t k))
    (@bind (Monads.writerT W (itree F)) (writerT_monad op) A B
      (fold_writer op handle sample t) (fun a => fold_writer op handle sample (k a))).
Proof.
  change (eq_itree eq (itree_writer_from (PTree.bind t k) (monoid_unit op))
    (ITree.bind (itree_writer_from t (monoid_unit op)) (fun wa =>
      ITree.bind (itree_writer_from (k (snd wa)) (monoid_unit op))
        (fun wb => ITreeDefinition.Ret (monoid_plus op (fst wa) (fst wb),snd wb))))).
  rewrite itree_writer_bind_from. apply eqit_bind; [reflexivity|]. intros [w a]. cbn.
  rewrite <- itree_writer_prefix, (@monoid_runit W op WL). reflexivity.
Qed.
Lemma itree_writer_fold_ret {A} (a : A) :
  eq_itree eq (fold_writer op handle sample (Ret a)) (ITreeDefinition.Ret (monoid_unit op,a)).
Proof.
  change (eq_itree eq (itree_writer_from (Ret a) (monoid_unit op))
    (ITreeDefinition.Ret (monoid_unit op,a))).
  rewrite itree_writer_fold_observe. reflexivity.
Qed.
End WriterFoldITree.
