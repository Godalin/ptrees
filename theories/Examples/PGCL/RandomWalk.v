(** Principal quantitative case: pGCL source -> forward lfp -> PTree -> law.

    Read [walk_source], [walk_denote_least_fixed_point], [walk_forward] and
    [walk_denote_closed_form], in that order. [walk_run] and
    [walk_classical_frontier] identify the already analysed PTree program.

    The source semantics is backend-parametric; this case selects SubEnumQ
    and observable FreeOmega. Leastness uses the internal preorder [⊑ω],
    not an external validating model or the structural approximation order.
    Passage, harmonic and convergence proofs stay in RandomWalkAnalysis.v.
    The output has infinite support; no finite native limit is asserted. *)
From Coq Require Import Utf8 Arith.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum rat.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ.
From PTree.Eq Require Import PTreeKernel.
From PTree.Eq.FreeOmega Require Import Relation Hitting.
From PTree.Prob.Interface Require Import Measure Omega KleisliIteration.
From PTree.Prob.Backend.Common Require Import FiniteSubdist.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Measure StructuralMeasure RelationalLimit Observation Quotient IterationOrder.
From PTree.Interp Require Import ReturnIteration.
From PTree.Examples.PGCL Require Import RandomWalkAnalysis.
From PTree.Examples.PGCL Require Import Syntax Forward Algebra Interpretation StateInterpretation FreeOmega.
Import PGCLNotations PGCLDenotationNotations PGCLAlgebraNotations SemanticMeasureNotations.
Import FreeOmegaOrderNotations.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope semantic_measure_scope.
Local Open Scope freeomega_scope.
Local Open Scope pgcl_scope.
Local Open Scope pgcl_denotation_scope.
Set Implicit Arguments.

(** 1. Source program. A probability label selects the native coin. *)
Definition walk {P} (downward : P) : command rw_state P :=
  WHILE (λ s, negb (Nat.eqb (fst s) 0)) DO
    (UPDATE (λ s, (Nat.pred (fst s), S (snd s))))
      ⊕[ downward ]
    (UPDATE (λ s, (S (fst s), 0)))
  OD.

(** The label tt selects the verified 2/3 coin. Scalar list details remain
    in the analysis file, not in the source program. *)
Definition walk_coin (_ : unit) := rw_coin.
Definition walk_source := walk tt.

Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

(** Compilation is structural and works for ANY native coin; distribution
    laws enter only after this ordinary control-flow correspondence. *)
Theorem walk_execute {P : Type} {E MN : Type → Type} (coin : P → MN bool) p :
  pstruct eq (execute (E := E) coin (walk p) (1%nat,0%nat))
    (random_walk_prog (coin p)).
Proof.
  unfold walk, random_walk_prog. cbn [execute].
  apply pstruct_iter. intros [x y]. destruct x as [|x].
  - apply observe_eq_pstruct. reflexivity.
  - apply pstruct_fold. cbn. constructor. intros [].
    + apply observe_eq_pstruct. reflexivity.
    + apply observe_eq_pstruct. reflexivity.
Qed.

(** 2. Forward semantics and leastness. Instantiate the language's while
    theorem; the local equation only exposes this program's two updates. *)
Local Notation D := (denote (FI := FI) (FO := FO) walk_coin).

(** The classical forward functional: absorb at height zero, otherwise
    move down/up and continue. The result remains in MF, not a finite list. *)
Definition walk_functional (Y : rw_state → FreeOmega SubEnumQ rw_state) s :=
  if Nat.eqb (fst s) 0 then ηω s else
    b ←ω walk_coin tt ;;
    Y (if b then (Nat.pred (fst s), S (snd s)) else (S (fst s), 0%nat)).

Theorem walk_denote_least_fixed_point :
  (∀ s, D walk_source s ≈ₘ walk_functional (D walk_source) s) ∧
  (∀ Y, (∀ s, walk_functional Y s ⊑ω Y s) → ∀ s, D walk_source s ⊑ω Y s).
Proof.
  assert (Hstep : ∀ (Y : rw_state → FreeOmega SubEnumQ rw_state) s,
    (if negb (Nat.eqb (fst s) 0) then
      D ((UPDATE (λ s, (Nat.pred (fst s), S (snd s))))
        ⊕[ tt ] (UPDATE (λ s, (S (fst s), 0)))) s >>=ₘ Y
     else ηₘ s) ≈ₘ walk_functional Y s).
  { intros Y s. unfold walk_functional. destruct (Nat.eqb (fst s) 0).
    - apply sem_eq_refl.
    - apply FOQLSample with (T := eq).
      + apply sem_lift_refl. intro b; reflexivity.
      + intros x y ->. destruct y; apply free_omega_qlift_refl; intro a; reflexivity. }
  destruct (pgcl_while_least_fixed_point (S := rw_state)
    (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)
    walk_coin (λ s, negb (Nat.eqb (fst s) 0))
    ((UPDATE (λ s, (Nat.pred (fst s), S (snd s))))
      ⊕[ tt ] (UPDATE (λ s, (S (fst s), 0))))) as [Hfix Hleast].
  split.
  - intro s. eapply sem_eq_trans; [apply Hfix|apply Hstep].
  - intros Y HY. apply Hleast. intro s.
    eapply free_omega_sem_le_trans; [apply free_omega_sem_eq_le, Hstep|apply HY].
Qed.

(** 3. State-interpreted PTree. Generic adequacy gives the whole frontier;
    the structural compilation equation connects the existing walk analysis. *)

Theorem walk_run :
  run (E := rwE) walk_coin walk_source (1%nat,0%nat) ≈ₚ random_walk.
Proof.
  rewrite (run_execute free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
  apply peutt_of_pstruct. apply walk_execute.
Qed.

(** The forward denotation is the whole final subdistribution, not a finite
    native representation and not a weakest-precondition observation. *)
Theorem walk_forward :
  ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (run (E := rwE) walk_coin walk_source (1%nat,0%nat)))
    (iteration_return_map (E := rwE) (MN := SubEnumQ)
      (denote (FI := FI) (FO := FO) walk_coin walk_source (1%nat,0%nat))).
Proof. apply pgcl_run_hitting. Qed.

(** The already analysed PTree itself has this classical forward frontier.
    Its established infinite-support observations thus refer to the same
    whole-distribution semantics, rather than to a new walk implementation. *)
Theorem walk_classical_frontier :
  ptree_stable_hitting (FI := FI) (FO := FO) (observe random_walk)
    (iteration_return_map (E := rwE) (MN := SubEnumQ)
      (denote (FI := FI) (FO := FO) walk_coin walk_source (1%nat,0%nat))).
Proof.
  eapply peutt_hitting_ret_only.
  - apply peutt_sym. exact walk_run.
  - exact walk_forward.
  - unfold iteration_return_map. eapply free_omega_ae_bind.
    + apply (sem_ae_true (SI := FI)).
    + intros s _. constructor. exists s. reflexivity.
Qed.

(** 4. Quantitative law. Reuse the analysis through finite observations.
    Round zero already observes an absorbing state, hence the S n shift
    relative to the classical bottom-started Kleisli approximants. *)

Definition walk_round n s :=
  sem_iter_approx (MI := FI)
    (while_kernel (λ s : rw_state, negb (Nat.eqb (fst s) 0))
      (D ((UPDATE (λ s, (Nat.pred (fst s), S (snd s))))
           ⊕[ tt ] (UPDATE (λ s, (S (fst s), 0)))))) (S n) s.

Theorem walk_denote_rounds s :
  D walk_source s ≈ₘ (supω n, walk_round n s).
Proof.
  change (@sem_lub _ FI FO _ (λ n, walk_round n s) (D walk_source s)).
  apply (proj1 (sem_iter_lub_shift (MI := FI) (MO := FO) _ _ _)).
  apply iterate_spec.
Qed.

Theorem walk_round_increasing s :
  @sem_increasing _ FI FO _ (λ n, walk_round n s).
Proof.
  intro n. exact (sem_iter_approx_increasing (MI := FI) (MO := FO) _ s (S n)).
Qed.

Lemma walk_round_observes n x y :
  free_omega_observes (λ s : rw_state, s) (walk_round n (x,y))
    (walk_observation (λ y, (0%nat,y)) n x y).
Proof.
  revert x y. induction n as [|n IH]; intros [|x] y.
  - constructor.
  - apply FOOObserveSample. intros []; constructor.
  - constructor.
  - apply FOOObserveSample. intros []; apply IH.
Qed.

(** Infinite-support meaning: a whole forward denotation, represented by
    its finite source rounds, whose atom probabilities have a normalized
    closed form. The finite lists are approximations, not the final measure. *)
Theorem walk_denote_closed_form :
  D walk_source (1%nat,0%nat) ≈ₘ (supω n, walk_round n (1%nat,0%nat)) ∧
  (∀ n, free_omega_observes (λ s : rw_state, s)
    (walk_round n (1%nat,0%nat)) (random_walk_outputs n)) ∧
  (∀ s, rational_limit (λ n, finite_subdist_expect
    (random_walk_outputs n) (state_indicator s)) (joint_pmf s)) ∧
  rational_limit geometric_partial_mass 1.
Proof.
  split; first apply walk_denote_rounds.
  split; first (intro n; apply walk_round_observes).
  split; [apply random_walk_output_dist|apply joint_pmf_normalized].
Qed.
