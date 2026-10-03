(** Two concrete instances of the SAME pGCL theorem. Probability parameters
    are bounded scalars; native list representation is confined to this file.
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
Import ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Record probability (W : numDomainType) := Probability {
  bias : W;
  bias_nonnegative : 0 <= bias;
  bias_bounded : bias <= 1
}.

Definition bernoulli {W : numDomainType} (p : probability W) : FiniteSubdist W bool.
Proof.
  refine (finite_subdist_of_list
    (mu := [(bias p,true); (1-bias p,false)]) _ _).
  - intros q b [H|[H|[]]]; inversion H; subst.
    + exact (bias_nonnegative p).
    + by rewrite subr_ge0; apply bias_bounded.
  - cbn. by rewrite !mulr1 addr0 addrC subrK.
Defined.

Lemma bernoulli_expect {W : numDomainType} (p : probability W) (f : bool → W) :
  finite_subdist_expect (bernoulli p) f = bias p * f true + (1-bias p) * f false.
Proof. by rewrite /finite_subdist_expect /finite_enum_expect /= addr0. Qed.

Definition rational_probability := probability rat_rat__canonical__Num_NumDomain.
Definition rational_coin : rational_probability → SubEnumQ bool := @bernoulli _.

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
