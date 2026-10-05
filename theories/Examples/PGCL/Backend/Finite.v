(** Two concrete instances of the SAME pGCL theorem. Probability parameters
    and native finite coins come from the executable [Probability] module.
    The semantic result remains FreeOmega, not a finite distribution. *)
From Coq Require Import Utf8 List.
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat reals.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.
From PTree.Prob.Backend.SubEnumQ Require Import Representation Measure.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure Measure.
From PTree.Eq Require Import PTreeKernel.
From PTree.Interp Require Import ReturnIteration.
From PTree.Examples.PGCL Require Import Syntax Forward Interpretation FreeOmega.
From PTree.Examples.PGCL.Backend Require Export Probability.
Import ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Section Rational.
Context {S : Type} {E : Type → Type}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

Theorem rational_pgcl_hitting (c : command S rational_probability) s :
  ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (run (E := E) rational_coin c s))
    (iteration_return_map (E := E) (MN := SubEnumQ)
      (denote (FI := FI) (FO := FO) rational_coin c s)).
Proof. apply pgcl_run_hitting. Qed.
End Rational.

Section Real.
Variable R : realType.
Context {S : Type} {E : Type → Type}.
Definition real_coin : probability R → SubEnumR R bool := @bernoulli R.
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).

Theorem real_pgcl_hitting (c : command S (probability R)) s :
  ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (run (E := E) real_coin c s))
    (iteration_return_map (E := E) (MN := SubEnumR R)
      (denote (FI := FI) (FO := FO) real_coin c s)).
Proof. apply pgcl_run_hitting. Qed.
End Real.
