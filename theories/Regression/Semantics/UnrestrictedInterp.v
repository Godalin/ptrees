(** Arbitrary handlers, including internally returning and mixed handlers.
    Source evidence is peutt, not a handler-specific target equivalence. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms.
From ITree.Events Require Import Reader.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Interp Require Import HandlerMachine HandlerMachineScheduling HandlerMachineAcceleration Unrestricted.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.
From PTree.Eq Require Import PEutt UnifiedFrontier PrimitiveStableHitting.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure RelationalLimit.
Require PTree.Interp.FreeOmega.Unrestricted.
From PTree.Examples Require Import StateCounter.
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

Section ReaderClient.
Context {E : Type -> Type}.
Definition reader_handler (env : bool) X (e : (readerE bool +' E) X) : ptree E SubEnumQ X :=
  match e with
  | inl1 se => match se in readerE _ X return ptree E SubEnumQ X with
      | Ask => Ret env end
  | inr1 e => Vis e (fun x => Ret x)
  end.

Example internally_returning_reader env :
  reader_handler env (inl1 Ask) = Ret env.
Proof. reflexivity. Qed.

Example handler_return_is_internal {A} (k : bool -> ptree (readerE bool +' E) SubEnumQ A) b :
  handler_front_result (reader_handler b) k (FHRet b) = SHInternal (SourceConfig (k b)).
Proof. reflexivity. Qed.

Example reader_source_enters_handler {A} env (k : bool -> ptree (readerE bool +' E) SubEnumQ A) :
  source_front_result (reader_handler env) (FHVis (inl1 Ask) k) =
    SHInternal (HandlerConfig (Ret env) k).
Proof. reflexivity. Qed.

Example heterogeneous_elimination {A B} (RR : A -> B -> Prop) env
    (t : ptree (readerE bool +' E) SubEnumQ A) (u : ptree (readerE bool +' E) SubEnumQ B) :
  W _ _ _ RR t u ->
  W _ _ _ RR (PTree.interp (reader_handler env) t) (PTree.interp (reader_handler env) u).
Proof. apply PTree.Interp.FreeOmega.Unrestricted.peutt_interp. Qed.

CoFixpoint forever_ask : ptree (readerE bool +' E) SubEnumQ unit :=
  Vis (inl1 Ask) (fun _ => forever_ask).

Example infinitely_many_eliminated_events env :
  W _ _ _ eq (PTree.interp (reader_handler env) (Tau forever_ask))
    (PTree.interp (reader_handler env) forever_ask).
Proof. apply heterogeneous_elimination. apply peutt_tau_l. Qed.

#[local] Instance reader_interp_Proper env A :
  Proper (W (readerE bool +' E) A A eq ==> W E A A eq)
    (@PTree.interp _ _ _ (reader_handler env) A).
Proof.
  apply (Unrestricted.peutt_interp_Proper free_omega_relational_zero free_omega_relational_lub).
Qed.

Example eliminating_setoid_rewrite env (t u : ptree (readerE bool +' E) SubEnumQ nat)
    (H : W _ _ _ eq t u) :
  W _ _ _ eq (PTree.interp (reader_handler env) t) (PTree.interp (reader_handler env) u).
Proof. setoid_rewrite H. apply peutt_refl. Qed.
End ReaderClient.

CoFixpoint diverge {E MN A} : ptree E MN A := Tau diverge.

Definition mixed_handler {E} X (e : (readerE bool +' E) X) : ptree E SubEnumQ X :=
  match e with
  | inl1 se => match se in readerE _ X return ptree E SubEnumQ X with
      | Ask => Prob coin (fun b => if b then Ret true else diverge) end
  | inr1 e => Vis e (fun x => Ret x)
  end.

(** This has positive returning mass, missing mass, and residual effects;
    it is not the old AE-visible guarded profile. *)
Example partial_mixed_handler {E A B} (RR : A -> B -> Prop)
    (t : ptree (readerE bool +' E) SubEnumQ A) (u : ptree (readerE bool +' E) SubEnumQ B) :
  W _ _ _ RR t u -> W _ _ _ RR (PTree.interp (@mixed_handler E) t) (PTree.interp (@mixed_handler E) u).
Proof. apply PTree.Interp.FreeOmega.Unrestricted.peutt_interp. Qed.

(** An independent real-weight native client uses the SAME completion
    specialization, not another proof of interpreter congruence. *)
From mathcomp Require Import reals.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.

Example real_arbitrary_handler (R : realType) {E F A B} (RR : A -> B -> Prop)
    (h : forall X, E X -> ptree F (SubEnumR R) X)
    (t : ptree E (SubEnumR R) A) (u : ptree E (SubEnumR R) B) :
  peutt (MF := FreeOmega (SubEnumR R)) RR t u ->
  peutt (MF := FreeOmega (SubEnumR R)) RR (PTree.interp h t) (PTree.interp h u).
Proof. apply PTree.Interp.FreeOmega.Unrestricted.peutt_interp. Qed.
