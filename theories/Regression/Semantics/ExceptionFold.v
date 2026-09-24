(** Actual ITree target, inherited transformer laws, and recursive interaction.
    Nothing here assumes a total sampler or a probability interpretation. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ExtLib.Data.Monads Require Import EitherMonad.
From ITree.Basics Require Import Basics Monad.
From ITree.Core Require Import ITreeDefinition ITreeMonad.
From ITree.Eq Require Import Eqit.
From ITree.Events Require Import Exception.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold IterationLaws ExceptT.
From PTree.Interp Require Import Exception ExceptionFold ExceptionFoldFacts.
From PTree.Execution Require Import ITreeFold.
Fail Check PTree.Eq.PEutt.peutt.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Set Implicit Arguments.
Unset Strict Implicit.

Section ITreeTarget.
Context {Err : Type} {E MN F : Type -> Type}.
Variable handle : forall X, E X -> itree F X.
Variable sample : forall X, MN X -> itree F X.

Example exception_target_monad :
  @MonadLawsE (eitherT Err (itree F)) (@exceptT_eq1 Err (itree F) Eq1_ITree)
    (@Monad_eitherT Err (itree F) _).
Proof. apply exceptT_monad_laws. Qed.

Example exception_target_uniform :
  @iteration_uniform (eitherT Err (itree F)) _ _
    (@exceptT_eq1 Err (itree F) Eq1_ITree).
Proof. apply exceptT_iteration_uniform. apply itree_iteration_uniform. Qed.

Example exception_fold_commutes {A} (t : ptree (exceptE Err +' E) MN A) :
  eutt eq (fold_exception handle sample t)
    (fold handle sample (run_exception t)).
Proof. apply (fold_run_exception (QT := Eq1_ITree)). apply itree_iteration_uniform. Qed.

Example exception_throw_fold {A} (err : Err) :
  eutt eq (fold_exception handle sample
    (Vis (inl1 (Throw err)) (fun v : void => match v return ptree _ _ A with end)))
    (ITreeDefinition.Ret (inl err)).
Proof.
  rewrite exception_fold_commutes, itree_fold_unfold.
  unfold fold_step. rewrite observe_run_exception.
  cbn [PTreeDefinition.observe PTreeDefinition._observe exception_value Monad.ret Monad_itree].
  rewrite bind_ret_l. reflexivity.
Qed.

Example exception_probability_fold {A X} (mu : MN X)
    (k : X -> ptree (exceptE Err +' E) MN A) :
  eutt eq (fold_exception handle sample (Prob mu k))
    (ITree.bind (@sample X mu) (fun x => fold_exception handle sample (k x))).
Proof.
  rewrite exception_fold_commutes, itree_fold_unfold.
  unfold fold_step at 1. rewrite observe_run_exception.
  cbn [PTreeDefinition.observe PTreeDefinition._observe Monad.bind Monad.ret Monad_itree].
  rewrite bind_bind. apply eqit_bind; [reflexivity|]. intro x.
  rewrite bind_ret_l, exception_fold_commutes. reflexivity.
Qed.

(** Sampling before Throw is retained as a bind, not erased. The semantic
    half-mass separation is independently checked in EffectAlgebra. *)
Example sample_then_exception {X A} (mu : MN X) (err : Err) :
  eutt eq (fold_exception handle sample
    (Prob mu (fun _ => Vis (inl1 (Throw err))
      (fun v : void => match v return ptree _ _ A with end))))
    (ITree.bind (@sample X mu) (fun _ => ITreeDefinition.Ret (inl err))).
Proof.
  rewrite exception_probability_fold. apply eqit_bind; [reflexivity|].
  intro x. apply exception_throw_fold.
Qed.
End ITreeTarget.

Variant requestE : Type -> Type := Request : requestE bool.

Section InfiniteInteraction.
Context {MN F : Type -> Type}.
Variable mu : MN bool.
Variable sample : forall X, MN X -> itree F X.
Variable handle : forall X, requestE X -> itree F X.

CoFixpoint retry_or_throw : ptree (exceptE nat +' requestE) MN bool :=
  Vis (inr1 Request) (fun continue : bool =>
    if continue then
      Prob mu (fun done : bool => if done then Ret true else Tau retry_or_throw)
    else Vis (inl1 (Throw 7)) (fun v : void => match v with end)).

Example recursive_exception_square :
  eutt eq (fold_exception handle sample retry_or_throw)
    (fold handle sample (run_exception retry_or_throw)).
Proof. apply exception_fold_commutes. Qed.
End InfiniteInteraction.

Section HighCarrier.
Universe high.
Constraint Set < high.
Context {A : Type@{high}} {MN F : Type -> Type}.
Variable sample : forall X, MN X -> itree F X.
Definition no_event X (e : void1 X) : itree F X := match e with end.
Example high_exception_square (t : ptree (exceptE nat +' void1) MN A) :
  eutt eq (fold_exception (@no_event) sample t)
    (fold (@no_event) sample (run_exception t)).
Proof. apply exception_fold_commutes. Qed.
End HighCarrier.
