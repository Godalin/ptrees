(** Standard effect clients preserve probability and observable error/output
    behavior. Concrete execution is checked in addition to theorem signatures. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From ExtLib.Structures Require Import Monoid.
From ITree.Basics Require Import Basics.
From ITree.Events Require Import Reader Writer Exception.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Interp Require Import Reader Writer Exception StandardFacts ExceptionFacts State.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.
From PTree.Eq Require Import PEutt.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure RelationalLimit BindOrder.
From PTree.Execution Require Import Runner.
From PTree.Execution.Backend Require Import SubEnumQ.
From PTree.Examples Require Import StateCounter.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation W E A B RR := (@peutt E SubEnumQ MF FI FC FreeOmegaMixedMeasure FO A B RR).

Example reader_heterogeneous {Env E A B} (RR : A -> B -> Prop) env
    (t : ptree (readerE Env +' E) SubEnumQ A) (u : ptree (readerE Env +' E) SubEnumQ B) :
  W _ _ _ RR t u -> W _ _ _ RR (run_reader t env) (run_reader u env).
Proof. apply (run_reader_peutt free_omega_relational_zero free_omega_relational_lub). Qed.

Example writer_heterogeneous {Log E A B} (op : Monoid Log) (RR : A -> B -> Prop)
    (t : ptree (writerE Log +' E) SubEnumQ A) (u : ptree (writerE Log +' E) SubEnumQ B) :
  W _ _ _ RR t u -> W _ _ _ (state_result_rel RR) (run_writer op t) (run_writer op u).
Proof. apply (run_writer_peutt free_omega_relational_zero free_omega_relational_lub). Qed.

Example exception_heterogeneous {Err E A B} (RR : A -> B -> Prop)
    (t : ptree (exceptE Err +' E) SubEnumQ A) (u : ptree (exceptE Err +' E) SubEnumQ B) :
  W _ _ _ RR t u -> W _ _ _ (exception_result_rel RR) (run_exception t) (run_exception u).
Proof. apply (run_exception_peutt free_omega_relational_bind). Qed.

Definition read_and_sample : ptree (readerE nat +' void1) SubEnumQ nat :=
  Vis (inl1 Ask) (fun env => Prob coin (fun b : bool => Ret (if b then env else 0))).
Example reader_native_probability :
  run (@replay_sample) 2 (run_reader read_and_sample 7) [high_quantile] = (Returned 7, []).
Proof. native_compute. reflexivity. Qed.

Definition list_log : Monoid (list nat) := {| monoid_plus := @List.app nat; monoid_unit := [] |}.
Definition log_and_sample : ptree (writerE (list nat) +' void1) SubEnumQ bool :=
  Vis (inl1 (Tell [1])) (fun _ => Prob coin (fun b : bool =>
    Vis (inl1 (Tell [if b then 2 else 3])) (fun _ => Ret b))).
Example writer_chronological_order :
  run (@replay_sample) 7 (run_writer list_log log_and_sample) [high_quantile] =
    (Returned ([1;2],true), []).
Proof. native_compute. reflexivity. Qed.
Example writer_probabilistic_other_branch :
  run (@replay_sample) 7 (run_writer list_log log_and_sample) [low_quantile] =
    (Returned ([1;3],false), []).
Proof. native_compute. reflexivity. Qed.

Definition sample_or_throw : ptree (exceptE nat +' void1) SubEnumQ nat :=
  Prob coin (fun b : bool => if b then
    Vis (inl1 (Throw 42)) (fun v : void => match v with end) else Ret 7).
Example exception_is_a_returned_error :
  run (@replay_sample) 1 (run_exception sample_or_throw) [high_quantile] = (Returned (inl 42), []).
Proof. native_compute. reflexivity. Qed.
Example exception_success_branch :
  run (@replay_sample) 1 (run_exception sample_or_throw) [low_quantile] = (Returned (inr 7), []).
Proof. native_compute. reflexivity. Qed.
Example missing_mass_is_not_an_exception :
  run (@replay_sample) 1
    (run_exception (Prob (@subenumQ_zero bool)
      (fun _ => (Ret 7 : ptree (exceptE nat +' void1) SubEnumQ nat))))
    [low_quantile] = (Lost, []).
Proof. native_compute. reflexivity. Qed.

Variant emitE : Type -> Type := Emit : nat -> emitE unit.
Example reader_forwards_event :
  @reader_handler nat emitE SubEnumQ 7 unit (inr1 (Emit 3)) = Vis (Emit 3) (fun x => Ret x).
Proof. reflexivity. Qed.
Example writer_forwards_event :
  @writer_handler (list nat) emitE SubEnumQ list_log unit (inr1 (Emit 3)) =
    Vis (inr1 (Emit 3)) (fun x => Ret x).
Proof. reflexivity. Qed.

CoFixpoint throw_after_retries : ptree (exceptE nat +' emitE) SubEnumQ nat :=
  Prob coin (fun b => if b then Vis (inl1 (Throw 42)) (fun v : void => match v with end)
    else Vis (inr1 (Emit 0)) (fun _ => Tau throw_after_retries)).
Example infinite_exception_weak_rewrite :
  W _ _ _ (exception_result_rel eq) (run_exception (Tau throw_after_retries))
    (run_exception throw_after_retries).
Proof. apply exception_heterogeneous. apply peutt_tau_l. Qed.
