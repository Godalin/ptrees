(** Operation inference and actual completion clients. No local sampling
    instance is needed for PTree or StateT over PTree. *)
From Coq Require Import Utf8.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import Fold.
Fail Check PTree.Eq.PEutt.peutt.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Eq.Backend.MathComp.mathcomp_peutt.

From mathcomp Require Import reals.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ SubEnumR.
From PTree.Prob.FreeOmega Require Import RelationalLimit.
From PTree.Interp Require Import FoldPTree State StateFold StateFoldFacts.
From PTree.Interp.FreeOmega Require Import IterationAlgebra IterationUniform.
Set Implicit Arguments.
Unset Strict Implicit.

Section Rational.
Context {E F : Type → Type}.
Variable h : ∀ X, E X → ptree F SubEnumQ X.

Example rational_agreement {A} (t : ptree E SubEnumQ A) :
  interp h t ≈ₚ PTree.interp_tree h t.
Proof.
  exact (interp_ptree_agrees free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub h t).
Qed.

Example rational_bind {A B} (t : ptree E SubEnumQ A)
    (k : A → ptree E SubEnumQ B) :
  interp h (PTree.bind t k) ≈ₚ PTree.bind (interp h t) (λ x, interp h (k x)).
Proof.
  exact (interp_ptree_bind free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub h t k).
Qed.

Example state_sampling {S X} (mu : SubEnumQ X) (s : S) :
  @msample _ _ (@MonadSample_stateT S SubEnumQ (ptree F SubEnumQ) _ _) X mu s =
    PTree.bind (PTree.sample mu) (λ x, Ret (s,x)).
Proof. reflexivity. Qed.

Example state_interpretation {S A} (t : ptree (stateE S +' E) SubEnumQ A) s :
  interp_state h t s ≈ₚ PTree.interp_tree h (run_state t s).
Proof.
  transitivity (interp h (run_state t s)); [|apply rational_agreement].
  apply (interp_state_run_state (QT := free_omega_ptree_eq1)
    (QE := free_omega_ptree_equivalence) (ML := free_omega_ptree_monad_laws)).
  exact free_omega_ptree_iteration_uniform.
Qed.
End Rational.

Section Real.
Variable R : realType.
Context {E F : Type → Type}.
Example real_agreement {A} (h : ∀ X, E X → ptree F (SubEnumR R) X)
    (t : ptree E (SubEnumR R) A) :
  interp h t ≈ₚ PTree.interp_tree h t.
Proof.
  exact (interp_ptree_agrees free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub h t).
Qed.
End Real.

Section HighUniverse.
Universe high.
Constraint Set < high.
Context {E F : Type → Type}.
Example high_agreement (A : Type@{high})
    (h : ∀ X, E X → ptree F SubEnumQ X) (t : ptree E SubEnumQ A) :
  interp h t ≈ₚ PTree.interp_tree h t.
Proof. apply rational_agreement. Qed.
End HighUniverse.

(** Both source and handler may fail to return. Agreement must not obtain
    either termination certificate through inference. *)
Section Divergence.
Context {E : Type → Type}.
CoFixpoint forever {A} : ptree E SubEnumQ A := Tau forever.
Example nonreturning_handler {A} (t : ptree E SubEnumQ A) :
  interp (λ X (_ : E X), @forever X) t ≈ₚ
    PTree.interp_tree (λ X (_ : E X), @forever X) t.
Proof. apply rational_agreement. Qed.
Example silent_source :
  interp (λ X (_ : E X), @forever X) (@forever bool) ≈ₚ
    PTree.interp_tree (λ X (_ : E X), @forever X) (@forever bool).
Proof. apply rational_agreement. Qed.
End Divergence.
