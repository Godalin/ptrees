(** Reading entry: a coin assignment, an unbounded retry, a nested loop,
    partial termination, and a divergent loop. The notation describes source
    programs; the same generic theorem gives their whole forward frontier.
    No termination assumption or finite-support limit is hidden in these rules. *)
From Coq Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Eq Require Import PTreeKernel.
From PTree.Eq.FreeOmega Require Import Hitting.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure Measure Quotient.
From PTree.Interp Require Import ReturnIteration.
From PTree.Examples.PGCL Require Import Syntax Forward Algebra Interpretation FreeOmega Finite.
Import GRing.Theory Num.Theory Order.Theory.
Import PGCLNotations PGCLDenotationNotations SemanticMeasureNotations HittingNotations.
Local Open Scope ring_scope.
Local Open Scope semantic_measure_scope.
Local Open Scope freeomega_scope.
Local Open Scope pgcl_scope.
Local Open Scope pgcl_denotation_scope.
Local Open Scope hitting_scope.
Set Implicit Arguments.

Module CoinLoops.
Definition half : rational_probability.
Proof. refine (@Probability _ (1/2) _ _); by vm_compute. Defined.

Definition toss : command bool rational_probability :=
  (UPDATE (λ _, true)) ⊕[ half ] (UPDATE (λ _, false)).

Definition retry : command bool rational_probability :=
  WHILE (λ b, b) DO toss OD.

Definition nested : command bool rational_probability :=
  WHILE (λ b, b) DO
    retry ;; toss
  OD.

Definition partial : command bool rational_probability :=
  (UPDATE (λ _, true)) ⊕[ half ] DIVERGE.

Definition endless : command bool rational_probability :=
  WHILE (λ _, true) DO SKIP OD.

Section Meaning.
(** An inhabited signature is allowed: these programs happen not to use it. *)
Context {E : Type → Type}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation D := (denote (FI := FI) (FO := FO) rational_coin).
Local Notation run := (Interpretation.run (E := E) rational_coin).
Local Notation "c '≈g' d" :=
  (cequiv (FI := FI) (FO := FO) rational_coin c d) (at level 70).

(** Source algebra, including rewriting underneath both a choice and an
    unbounded while. No program semantics is unfolded in this proof. *)
Theorem source_rewrite (b : bool → bool) (f g : bool → bool) :
  (WHILE b DO
     (SKIP ;; UPDATE f) ⊕[ half ] ((UPDATE (λ s, s) ;; UPDATE g) ;; SKIP)
   OD) ≈g
  (WHILE b DO (UPDATE f) ⊕[ half ] (UPDATE g) OD).
Proof.
  rewrite (assign_id (FI := FI) (FO := FO) rational_coin)
    !(seq_skip_l (FI := FI) (FO := FO) rational_coin)
    (pgcl_seq_skip_r rational_coin). reflexivity.
Qed.

(** The same source rewrite can be consumed under the State interpreter. *)
Theorem source_rewrite_run (b : bool → bool) (f g : bool → bool) s :
  run (WHILE b DO
    (SKIP ;; UPDATE f) ⊕[ half ] ((UPDATE (λ s, s) ;; UPDATE g) ;; SKIP)
  OD) s ≈ₚ run (WHILE b DO (UPDATE f) ⊕[ half ] (UPDATE g) OD) s.
Proof. setoid_rewrite (source_rewrite b f g). reflexivity. Qed.

(** The denotation brackets and the relational notation agree. *)
Example toss_denotes : toss ⇓[ rational_coin ] ⟦ toss ⟧[ rational_coin ].
Proof. apply denote_spec. Qed.

Theorem retry_frontier s :
  run retry s ⇓ₕ iteration_return_map (D retry s).
Proof. apply rational_pgcl_hitting. Qed.

Theorem nested_frontier s :
  run nested s ⇓ₕ iteration_return_map (D nested s).
Proof. apply rational_pgcl_hitting. Qed.

(** This is the familiar loop equation; the bottom-started approximants,
    not this equation alone, select the intended solution. *)
Theorem retry_equation s :
  D retry s ≈ₘ (if s then D toss s >>=ₘ D retry else ηₘ s).
Proof. exact (denote_while_unfold rational_coin (λ b, b) toss s). Qed.

Theorem partial_frontier s :
  run partial s ⇓ₕ
    (b ←ω rational_coin half ;; if b then ηω (FHRet true) else ⊥ω).
Proof.
  eapply stable_hitting_output_transport; [apply rational_pgcl_hitting|].
  apply FOQLSample with (T := eq).
  - apply sem_lift_refl. intro b. reflexivity.
  - intros b b' ->. destruct b'; apply free_omega_qlift_refl; intro h; reflexivity.
Qed.

(** Divergence is zero stable mass, never a distinguished terminal state. *)
Theorem divergent_frontier s :
  run DIVERGE s ⇓ₕ (⊥ω : FreeOmega SubEnumQ (stable_head E SubEnumQ bool)).
Proof. exact (rational_pgcl_hitting (E := E) CDiverge s). Qed.

Theorem endless_frontier s :
  run endless s ⇓ₕ (⊥ω : FreeOmega SubEnumQ (stable_head E SubEnumQ bool)).
Proof.
  eapply stable_hitting_output_transport; [apply rational_pgcl_hitting|].
  change (@sem_eq _ FI _ (iteration_return_map (E := E) (MN := SubEnumQ) (D endless s))
    (iteration_return_map (E := E) (MN := SubEnumQ) (@sem_zero _ FI FO bool))).
  unfold iteration_return_map. apply sem_bind_eq_l.
  exact (denote_endless_skip rational_coin s).
Qed.

Theorem skip_retry s : run (SKIP ;; retry) s ≈ₚ run retry s.
Proof.
  apply pgcl_denotation_peutt. intro t.
  apply sem_bind_ret_l.
Qed.
End Meaning.
End CoinLoops.
