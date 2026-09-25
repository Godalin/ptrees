(** Real generic law consumers, pure-map iteration, and an explicit boundary
    for the stronger universe-polymorphic iteration_uniform package. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Interp Require Import IterationAlgebra.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.Backend.MathComp.Direct.mathcomp_direct_peutt.

From Coq Require Import Morphisms List.
From ExtLib.Structures Require Import Monad Monoid.
From ExtLib.Data.Monads Require Import ReaderMonad EitherMonad.
From ITree.Basics Require Import Basics Monad.
From ITree.Events Require Import State Reader Writer Exception.
From ITree.Indexed Require Import Sum.
From mathcomp Require Import reals.
From PTree.Core Require Import PTreeDefinition Fold IterationLaws ReaderT WriterT ExceptT.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ SubEnumR.
From PTree.Prob.FreeOmega Require Import RelationalLimit.
From PTree.Prob.Interface Require Import RelationalClosure.
From PTree.Interp.FreeOmega Require Import IterationAlgebra.
From PTree.Interp Require Import StateFold StateFoldFacts ExceptionFold ExceptionFoldFacts.
Set Implicit Arguments.

Variant questionE : Type -> Type := Question : questionE bool.
Fail Definition no_global_behavioral_eq1 : Eq1 (ptree questionE SubEnumQ) := _.

Section RationalTarget.
Context {F : Type -> Type}.
Local Notation T := (ptree F SubEnumQ).
Local Instance target_eq1 : Eq1 T := free_omega_ptree_eq1.
Local Instance target_equivalence : @Eq1Equivalence T Monad_ptree target_eq1 :=
  free_omega_ptree_equivalence.
Local Instance target_monad_laws : @MonadLawsE T target_eq1 Monad_ptree :=
  free_omega_ptree_monad_laws.

Example eq1_is_canonical {A} (t u : T A) : eq1 t u <-> t ≈ₚ u.
Proof. reflexivity. Qed.

Example actual_monad_rewriting {A B} (t : T A) (k : A -> T B) :
  eq1 (@Monad.bind T Monad_ptree A B
    (@Monad.bind T Monad_ptree A A t (@Monad.ret T Monad_ptree A)) k)
    (@Monad.bind T Monad_ptree A B t k).
Proof. rewrite (@bind_ret_r T target_eq1 Monad_ptree target_monad_laws). reflexivity. Qed.

Example actual_uniformity {I J A} (f : I -> T (I+A))
    (g : J -> T (J+A)) (h : I -> J) :
  (forall i, PTree.bind (f i) (fun v => Ret (iteration_map h v)) ≈ₚ g (h i)) ->
  forall i, PTree.iter f i ≈ₚ PTree.iter g (h i).
Proof. apply free_omega_peutt_iter_uniform. Qed.

(** Do not mistake a small-state theorem for the single Eq1-wide package
    needed by fold_run_state/fold_run_exception. The protocol proof places
    I+A in the event-response universe; Eq1's full domain is larger here. *)
Fail Definition protocol_uniformity_package :
  @iteration_uniform T Monad_ptree MonadIter_ptree target_eq1 :=
  fun I J A f g h => @free_omega_peutt_iter_uniform
    SubEnumQ _ _ _ _ _ _ F I J A f g h.

Example weak_fixed_point {I A} (step : I -> T (I+A)) i :
  PTree.iter step i ≈ₚ PTree.bind (step i)
    (fun v => match v with inl j => PTree.iter step j | inr a => Ret a end).
Proof.
  apply (ptree_peutt_iter_unfold free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Example state_dependent_finite_stuttering {I A} (step : I -> T (I+A))
    (delay : I -> nat) i :
  PTree.iter (fun j => Nat.iter (delay j) (fun t => Tau t) (step j)) i ≈ₚ
  PTree.iter step i.
Proof.
  apply (ptree_peutt_iter_finite_stutter free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Example reader_inherits_monad {Env} :
  @MonadLawsE (readerT Env T) (readerT_eq1 (QT := target_eq1)) _.
Proof. apply readerT_monad_laws. Qed.

Example exception_inherits_monad {Err} :
  @MonadLawsE (eitherT Err T) (exceptT_eq1 (QT := target_eq1)) _.
Proof. apply exceptT_monad_laws. Qed.

Example writer_inherits_monad {W} (op : Monoid W) (WL : MonoidLaws op) :
  @MonadLawsE (Monads.writerT W T) (writerT_eq1 (QT := target_eq1)) (writerT_monad op).
Proof. apply (writerT_monad_laws WL). Qed.
End RationalTarget.

(** Noninjective state map: no inverse or choice of representative is used. *)
Definition counted_step (n : nat) : ptree questionE SubEnumQ (nat+bool) :=
  Vis Question (fun b : bool => Ret (if b then inr true else inl (S n))).
Definition collapsed_step (_ : unit) : ptree questionE SubEnumQ (unit+bool) :=
  Vis Question (fun b : bool => Ret (if b then inr true else inl tt)).

Example collapse_unbounded_counter n :
  PTree.iter counted_step n ≈ₚ PTree.iter collapsed_step tt.
Proof.
  apply (free_omega_peutt_iter_uniform (f := counted_step) (g := collapsed_step)
    (h := fun _ => tt)).
  intro i. unfold counted_step, collapsed_step.
  change (
    ((Vis Question (fun b : bool => PTree.bind
      (Ret (if b then inr true else inl (S i)))
      (fun v => Ret (iteration_map (fun _ : nat => tt) v)))) : ptree questionE SubEnumQ (unit+bool))
    ≈ₚ (Vis Question (fun b : bool => Ret (if b then inr true else inl tt)))).
  apply peutt_vis. intros [].
  all: exact (PTree.Eq.Algebra.peutt_bind_ret_l (relational_bind_of_laws _)
    free_omega_relational_mixed_bind free_omega_relational_zero free_omega_relational_lub
    _ (fun v : nat+bool => Ret (iteration_map (fun _ : nat => tt) v))).
Qed.

Section RealTarget.
Variable R : realType.
Context {F : Type -> Type}.
Example real_lawful_iteration {I J A}
    (f : I -> ptree F (SubEnumR R) (I+A))
    (g : J -> ptree F (SubEnumR R) (J+A)) (h : I -> J) :
  (forall i, PTree.bind (f i) (fun v => Ret (iteration_map h v)) ≈ₚ g (h i)) ->
  forall i, PTree.iter f i ≈ₚ PTree.iter g (h i).
Proof. apply free_omega_peutt_iter_uniform. Qed.
Example real_lawful_monad :
  @MonadLawsE (ptree F (SubEnumR R)) free_omega_ptree_eq1 Monad_ptree.
Proof. exact free_omega_ptree_monad_laws. Qed.
End RealTarget.

Section LargeCarrier.
Universe high.
Constraint Set < high.
Example high_uniformity (I J A : Type@{high})
    (f : I -> ptree questionE SubEnumQ (I+A))
    (g : J -> ptree questionE SubEnumQ (J+A)) (h : I -> J) :
  (forall i, PTree.bind (f i) (fun v => Ret (iteration_map h v)) ≈ₚ g (h i)) ->
  forall i, PTree.iter f i ≈ₚ PTree.iter g (h i).
Proof. apply free_omega_peutt_iter_uniform. Qed.
End LargeCarrier.
