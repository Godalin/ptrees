(** Explicit transformer laws and actual ITree commuting clients. Logs are
    deliberately noncommutative; both services may run without a bound. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From ExtLib.Structures Require Import Monad Monoid BinOps.
From ExtLib.Data.Monads Require Import ReaderMonad.
From ITree.Basics Require Import Basics Monad.
From ITree.Core Require Import ITreeDefinition ITreeMonad.
From ITree.Eq Require Import Eqit.
From ITree.Events Require Import Reader Writer.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold IterationLaws ReaderT WriterT.
From PTree.Interp Require Import Reader Writer ReaderFold WriterFold ReaderFoldITree WriterFoldITree.
From PTree.Execution Require Import ITreeFold.
Fail Check PTree.Eq.PEutt.peutt.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

Definition logs : Monoid (list nat) := {| monoid_plus := @app nat; monoid_unit := [] |}.
Definition logs_laws : MonoidLaws logs.
Proof.
  constructor; unfold Associative, LeftUnit, RightUnit; cbn.
  - intros. symmetry. apply app_assoc.
  - reflexivity.
  - apply app_nil_r.
Defined.

Section Laws.
Context {F : Type -> Type}.
Example reader_target_monad :
  @MonadLawsE (readerT bool (itree F)) (@readerT_eq1 bool (itree F) Eq1_ITree)
    (@Monad_readerT bool (itree F) _).
Proof. apply readerT_monad_laws. Qed.
Example reader_target_uniform :
  @iteration_uniform (readerT bool (itree F)) _ _ (@readerT_eq1 bool (itree F) Eq1_ITree).
Proof. apply readerT_iteration_uniform. apply itree_iteration_uniform. Qed.
Example writer_target_monad :
  @MonadLawsE (Monads.writerT (list nat) (itree F)) (@writerT_eq1 (list nat) (itree F) Eq1_ITree)
    (writerT_monad logs).
Proof.
  exact (@writerT_monad_laws _ (itree F) logs _ Eq1_ITree
    Eq1Equivalence_ITree MonadLawsE_ITree logs_laws).
Qed.
Example writer_target_uniform :
  @iteration_uniform (Monads.writerT (list nat) (itree F))
    (writerT_monad logs) (writerT_iter logs) (@writerT_eq1 (list nat) (itree F) Eq1_ITree).
Proof.
  exact (@writerT_iteration_uniform _ (itree F) logs _ Eq1_ITree
    Eq1Equivalence_ITree MonadLawsE_ITree logs_laws _ itree_iteration_uniform).
Qed.

Example writer_bind_keeps_order :
  eq_itree eq
    (@bind (Monads.writerT (list nat) (itree F)) (writerT_monad logs) unit unit
      (ITreeDefinition.Ret ([1],tt)) (fun _ => ITreeDefinition.Ret ([2],tt)))
    (ITreeDefinition.Ret ([1;2],tt)).
Proof.
  cbn [Monad.bind writerT_monad ITreeDefinition.Monad_itree]. rewrite !bind_ret_l. reflexivity.
Qed.
Example logs_not_commutative : monoid_plus logs [1] [2] <> monoid_plus logs [2] [1].
Proof. discriminate. Qed.
End Laws.

Variant tickE : Type -> Type := Tick : tickE unit.
Section Services.
Context {MN F : Type -> Type}.
Variable mu : MN bool.
Variable sample : forall X, MN X -> itree F X.
Variable handle : forall X, tickE X -> itree F X.

CoFixpoint reader_service : ptree (readerE bool +' tickE) MN bool :=
  Vis (inl1 Ask) (fun enabled : bool =>
    if enabled then Vis (inr1 Tick) (fun _ =>
      Prob mu (fun b : bool => if b then Ret b else Tau reader_service))
    else Ret false).

CoFixpoint writer_service : ptree (writerE (list nat) +' tickE) MN bool :=
  Vis (inr1 Tick) (fun _ => Vis (inl1 (Tell [1])) (fun _ =>
    Prob mu (fun b : bool => if b then Vis (inl1 (Tell [2])) (fun _ => Ret b)
      else Tau writer_service))).

Example reader_recursive_square env :
  eutt eq (fold_reader handle sample reader_service env)
    (fold handle sample (run_reader reader_service env)).
Proof. apply itree_fold_run_reader. Qed.
Example writer_recursive_square :
  eutt eq (fold_writer logs handle sample writer_service)
    (fold handle sample (run_writer logs writer_service)).
Proof. apply itree_fold_run_writer. exact logs_laws. Qed.

Example reader_bind_square {A B} (t : ptree (readerE bool +' tickE) MN A)
    (k : A -> ptree (readerE bool +' tickE) MN B) env :
  eq_itree eq (fold_reader handle sample (PTree.bind t k) env)
    (ITree.bind (fold_reader handle sample t env) (fun a => fold_reader handle sample (k a) env)).
Proof. apply itree_reader_fold_bind. Qed.
Example writer_bind_square {A B} (t : ptree (writerE (list nat) +' tickE) MN A)
    (k : A -> ptree (writerE (list nat) +' tickE) MN B) :
  eq_itree eq (fold_writer logs handle sample (PTree.bind t k))
    (@bind (Monads.writerT (list nat) (itree F)) (writerT_monad logs) A B
      (fold_writer logs handle sample t) (fun a => fold_writer logs handle sample (k a))).
Proof. apply itree_writer_fold_bind. exact logs_laws. Qed.

Example writer_sampling_does_not_log {X} (m : MN X) :
  @writer_sample (list nat) MN (itree F) logs _ sample X m =
    ITree.bind (@sample X m) (fun x => ITreeDefinition.Ret ([],x)).
Proof. reflexivity. Qed.
End Services.

Section HigherCarrier.
Universe high.
Constraint Set < high.
Context {A : Type@{high}} {MN F : Type -> Type}.
Variable handle : forall X, tickE X -> itree F X.
Variable sample : forall X, MN X -> itree F X.
Example writer_high_square (t : ptree (writerE (list nat) +' tickE) MN A) :
  eutt eq (fold_writer logs handle sample t) (fold handle sample (run_writer logs t)).
Proof. apply itree_fold_run_writer. exact logs_laws. Qed.
Example reader_high_square (t : ptree (readerE bool +' tickE) MN A) env :
  eutt eq (fold_reader handle sample t env) (fold handle sample (run_reader t env)).
Proof. apply itree_fold_run_reader. Qed.
End HigherCarrier.
