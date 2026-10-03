(** Classical source-language form of the maintained random walk. The proof
    reuses its control flow and infinite-support analysis; no second harmonic
    or convergence development is introduced here. *)
From Coq Require Import Utf8 Arith.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ.
From PTree.Eq Require Import PTreeKernel.
From PTree.Eq.FreeOmega Require Import Relation Hitting.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Measure StructuralMeasure RelationalLimit.
From PTree.Interp Require Import ReturnIteration.
From PTree.Examples Require Import RandomWalk.
From PTree.Examples.PGCL Require Import Syntax Forward Interpretation StateInterpretation FreeOmega.
Import PGCLNotations.
Local Open Scope pgcl_scope.
Set Implicit Arguments.

Definition walk {P} (downward : P) : command rw_state P :=
  WHILE (λ s, negb (Nat.eqb (fst s) 0)) DO
    (UPDATE (λ s, (Nat.pred (fst s), S (snd s))))
      ⊕[ downward ]
    (UPDATE (λ s, (S (fst s), 0)))
  OD.

(** Compilation is structural and works for ANY native coin; distribution
    laws enter only after this ordinary control-flow correspondence. *)
Theorem walk_execute {P : Type} {E MN : Type → Type} (coin : P → MN bool) p :
  pstruct eq (execute (E := E) coin (walk p) (1,0))
    (random_walk_prog (coin p)).
Proof.
  unfold walk, random_walk_prog. cbn [execute].
  apply pstruct_iter. intros [x y]. destruct x as [|x].
  - apply observe_eq_pstruct. reflexivity.
  - apply pstruct_fold. cbn. constructor. intros [].
    + apply observe_eq_pstruct. reflexivity.
    + apply observe_eq_pstruct. reflexivity.
Qed.

(** This parameter label selects the existing verified 2/3 native coin.
    No rational representation or conversion appears in the program proof. *)
Definition walk_coin (_ : unit) := rw_coin.
Definition walk_source := walk tt.

Theorem walk_run :
  run (E := rwE) walk_coin walk_source (1,0) ≈ₚ random_walk.
Proof.
  rewrite (run_execute free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
  apply peutt_of_pstruct. apply walk_execute.
Qed.

Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

(** The forward denotation is the whole final subdistribution, not a finite
    native representation and not a weakest-precondition observation. *)
Theorem walk_forward :
  ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (run (E := rwE) walk_coin walk_source (1,0)))
    (iteration_return_map (E := rwE) (MN := SubEnumQ)
      (denote (FI := FI) (FO := FO) walk_coin walk_source (1,0))).
Proof. apply pgcl_run_hitting. Qed.

(** The already analysed PTree itself has this classical forward frontier.
    Its established infinite-support observations thus refer to the same
    whole-distribution semantics, rather than to a new walk implementation. *)
Theorem walk_classical_frontier :
  ptree_stable_hitting (FI := FI) (FO := FO) (observe random_walk)
    (iteration_return_map (E := rwE) (MN := SubEnumQ)
      (denote (FI := FI) (FO := FO) walk_coin walk_source (1,0))).
Proof.
  eapply peutt_hitting_ret_only.
  - apply peutt_sym. exact walk_run.
  - exact walk_forward.
  - unfold iteration_return_map. eapply free_omega_ae_bind.
    + apply (sem_ae_true (SI := FI)).
    + intros s _. constructor. exists s. reflexivity.
Qed.
