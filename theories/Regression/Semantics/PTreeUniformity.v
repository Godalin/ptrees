(** Full-interface clients, including iteration over entire source trees. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Interp Require Import IterationUniform.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.Backend.MathComp.Direct.mathcomp_direct_peutt.

From ExtLib.Structures Require Import Monad Monoid.
From ExtLib.Data.Monads Require Import ReaderMonad EitherMonad.
From ITree.Basics Require Import Basics Monad.
From ITree.Events Require Import State Exception.
From ITree.Indexed Require Import Sum.
From mathcomp Require Import reals.
From PTree.Core Require Import PTreeDefinition IterationLaws Fold ReaderT WriterT ExceptT.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ SubEnumR.
From PTree.Interp.FreeOmega Require Import IterationAlgebra IterationUniform.
From PTree.Interp Require Import State StateFold StateFoldFacts Exception ExceptionFold ExceptionFoldFacts.
Set Implicit Arguments.

Section Rational.
Context {F : Type -> Type}.
Local Notation T := (ptree F SubEnumQ).
Local Instance target_eq1 : Eq1 T := free_omega_ptree_eq1.
Local Instance target_equivalence : @Eq1Equivalence T Monad_ptree target_eq1 :=
  free_omega_ptree_equivalence.
Local Instance target_monad_laws : @MonadLawsE T target_eq1 Monad_ptree :=
  free_omega_ptree_monad_laws.

Example full_uniformity : @iteration_uniform T Monad_ptree MonadIter_ptree target_eq1.
Proof. exact free_omega_ptree_iteration_uniform. Qed.

Context {E SRC : Type -> Type}.
Variable handle : forall X, E X -> T X.
Variable sample : forall X, SRC X -> T X.

Example state_fold_into_ptree {S A} (t : ptree (stateE S +' E) SRC A) s :
  fold_state handle sample t s ≈ₚ fold handle sample (run_state t s).
Proof.
  apply (fold_run_state (QT := target_eq1)).
  exact full_uniformity.
Qed.

Example exception_fold_into_ptree {Err A} (t : ptree (exceptE Err +' E) SRC A) :
  fold_exception handle sample t ≈ₚ fold handle sample (run_exception t).
Proof.
  apply (fold_run_exception (QT := target_eq1)).
  exact full_uniformity.
Qed.

Example reader_inherits_full_uniformity {Env} :
  @iteration_uniform (readerT Env T) _ _ (readerT_eq1 (QT := target_eq1)).
Proof. apply readerT_iteration_uniform. exact full_uniformity. Qed.
Example exception_inherits_full_uniformity {Err} :
  @iteration_uniform (eitherT Err T) _ _ (exceptT_eq1 (QT := target_eq1)).
Proof. apply exceptT_iteration_uniform. exact full_uniformity. Qed.
Example writer_inherits_full_uniformity {W} (op : Monoid W) (WL : MonoidLaws op) :
  @iteration_uniform (Monads.writerT W T) (writerT_monad op) (writerT_iter op)
    (writerT_eq1 (QT := target_eq1)).
Proof. apply (writerT_iteration_uniform WL). exact full_uniformity. Qed.
End Rational.

Section Real.
Variable R : realType.
Context {F : Type -> Type}.
Example real_full_uniformity :
  @iteration_uniform (ptree F (SubEnumR R)) Monad_ptree MonadIter_ptree free_omega_ptree_eq1.
Proof. exact free_omega_ptree_iteration_uniform. Qed.
End Real.

(** A loop state can contain a complete PTree, not just a small event reply. *)
Section LargeStates.
Context {E : Type -> Type} {A : Type}.
Local Notation S := (ptree E SubEnumQ A).
Example tree_state_uniformity (f : S -> ptree E SubEnumQ (S+A))
    (g : unit -> ptree E SubEnumQ (unit+A)) :
  (forall t, PTree.bind (f t) (fun v => Ret (iteration_map (fun _ : S => tt) v)) ≈ₚ g tt) ->
  forall t, PTree.iter f t ≈ₚ PTree.iter g tt.
Proof. apply (free_omega_ptree_iteration_uniform (f := f) (g := g) (h := fun _ : S => tt)). Qed.
End LargeStates.

Section HighUniverse.
Universe high.
Constraint Set < high.
Context {E : Type -> Type}.
Example high_full_uniformity (I J A : Type@{high})
    (f : I -> ptree E SubEnumQ (I+A)) (g : J -> ptree E SubEnumQ (J+A)) (h : I -> J) :
  (forall i, PTree.bind (f i) (fun v => Ret (iteration_map h v)) ≈ₚ g (h i)) ->
  forall i, PTree.iter f i ≈ₚ PTree.iter g (h i).
Proof. apply free_omega_ptree_iteration_uniform. Qed.
End HighUniverse.
