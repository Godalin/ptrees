(** Role: supporting program/semantic example, not a flagship claim. *)
(** Actual behavioral-step clients, not supplied generator-closure proofs. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Interp Require Import Iteration.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.Backend.MathComp.mathcomp_peutt.

From mathcomp Require Import reals.
From PTree.Prob.Interface Require Import Measure Mixed.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ SubEnumR.
From PTree.Interp.FreeOmega Require Import Iteration.
Set Implicit Arguments.

Variant questionE : Type → Type := Question : questionE bool.

(** Distinct state AND return carriers. Repeated false responses cause
    indefinitely many interactions; there is no termination assumption. *)
Definition left_step (_ : unit) : ptree questionE SubEnumQ (unit+bool) :=
  Vis Question (λ b : bool, Ret (if b then inr true else inl tt)).
Definition right_step (_ : nat) : ptree questionE SubEnumQ (nat+nat) :=
  Vis Question (λ b : bool, Ret (if b then inr 1 else inl 0)).
Definition state_rel (_ : unit) (n : nat) := n = 0.
Definition return_rel (b : bool) (n : nat) := n = if b then 1 else 0.

Lemma heterogeneous_steps i j : state_rel i j →
  left_step i ≈ₚ[pstruct_iter_sum_rel state_rel return_rel] right_step j.
Proof.
  intro H. apply peutt_vis. intros []; apply peutt_ret; constructor; reflexivity.
Qed.

Example heterogeneous_eventful_iteration :
  PTree.iter left_step tt ≈ₚ[return_rel] PTree.iter right_step 0.
Proof.
  eapply free_omega_peutt_iter_eventful_rel with (SI := state_rel).
  - exact heterogeneous_steps.
  - reflexivity.
Qed.

(** Sampling and interaction can both occur inside a single step. The
    right step inserts a Tau: the premise is weak, not lockstep structural. *)
Definition sampling_step {MN : Type → Type} (mu : MN bool) (_ : unit) :
    ptree questionE MN (unit+bool) :=
  Vis Question (λ _, Prob mu
    (λ b : bool, Ret (if b then inr true else inl tt))).

Example sampled_eventful_iteration (mu : SubEnumQ bool) :
  PTree.iter (sampling_step mu) tt ≈ₚ
  PTree.iter (λ i, Tau (sampling_step mu i)) tt.
Proof. apply free_omega_peutt_iter_eventful. intro i. apply peutt_tau_r. Qed.

Example partial_eventful_iteration :
  PTree.iter (sampling_step (@subenumQ_zero bool)) tt ≈ₚ
  PTree.iter (λ i, Tau (sampling_step (@subenumQ_zero bool) i)) tt.
Proof. apply sampled_eventful_iteration. Qed.

(** A probability-algebra change, not just a Tau-prefix test. Each round
    erases a native Dirac draw after a visible response. *)
Definition redundant_sample_step (_ : unit) : ptree questionE SubEnumQ (unit+bool) :=
  Vis Question (λ b : bool, Prob (subenumQ_ret b)
    (λ c : bool, Ret (if c then inr true else inl tt))).

Example probability_algebra_inside_iteration :
  PTree.iter redundant_sample_step tt ≈ₚ PTree.iter left_step tt.
Proof.
  apply free_omega_peutt_iter_eventful. intro i.
  apply peutt_vis. intro b.
  (* Both continuations return immediately. Keeping these explicit witnesses
     avoids the choice of arbitrary continuation frontiers used by the
     general [peutt_prob_ret] law. *)
  eapply peutt_of_hitting_lift.
  - eapply stable_hitting_prob with (Good := λ _, True)
      (front := λ c : bool, sem_ret (FHRet (if c then inr true else inl tt))).
    + apply sem_ae_true.
    + intros c _. apply stable_hitting_ret.
  - apply stable_hitting_ret.
  - eapply sem_lift_mono.
    + intros h1 h2 ->. destruct h2; constructor.
      * reflexivity.
      * intro x. apply peutt_refl.
    + exact (mixed_bind_ret_l
        (NI := PTree.Prob.Backend.SubEnumQ.Measure.SubEnumQ_SemanticMeasure)
        b (λ c : bool, sem_ret (FHRet (if c then inr true else inl tt)))).
Qed.

(** Silent endless retry is permitted, as well as eventful recursion. *)
Example silent_endless_iteration :
  PTree.iter (λ _ : unit, (Ret (inl tt) : ptree questionE SubEnumQ (unit+bool))) tt ≈ₚ
  PTree.iter (λ _ : unit, Tau (Ret (inl tt) : ptree questionE SubEnumQ (unit+bool))) tt.
Proof. apply free_omega_peutt_iter_eventful. intro i. apply peutt_tau_r. Qed.

(** An infinite coinductive step need not even return to the loop entry. *)
CoFixpoint never_returning_step : ptree questionE SubEnumQ (unit+bool) :=
  Vis Question (λ _, Tau never_returning_step).

Example infinite_active_step :
  PTree.iter (λ _ : unit, never_returning_step) tt ≈ₚ
  PTree.iter (λ _ : unit, Tau never_returning_step) tt.
Proof. apply free_omega_peutt_iter_eventful. intro i. apply peutt_tau_r. Qed.

(** The old loop-entry-only candidate cannot contain even this residual
    return. This is a candidate-exclusion test, not a new negative theorem
    about all conceivable iteration proof methods. *)
Definition exiting_step (_ : unit) : ptree questionE SubEnumQ (unit+bool) :=
  Vis Question (λ b, Ret (inr b)).
Example entry_candidate_excludes_residual b :
  ¬ iter_eventful_bisim_candidate exiting_step exiting_step eq
      (observe (Ret b)) (observe (Ret b)).
Proof. intros [i [j [_ [H _]]]]. discriminate H. Qed.

Section RealBackend.
Variable R : realType.
Example real_sampled_eventful_iteration (mu : SubEnumR R bool) :
  PTree.iter (sampling_step mu) tt ≈ₚ
  PTree.iter (λ i, Tau (sampling_step mu i)) tt.
Proof. apply free_omega_peutt_iter_eventful. intro i. apply peutt_tau_r. Qed.

Example real_heterogeneous_iteration {I J A B}
    (step1 : I → ptree questionE (SubEnumR R) (I+A))
    (step2 : J → ptree questionE (SubEnumR R) (J+B))
    (SI : I → J → Prop) (RR : A → B → Prop) :
  (∀ i j, SI i j → step1 i ≈ₚ[pstruct_iter_sum_rel SI RR] step2 j) →
  ∀ i j, SI i j → PTree.iter step1 i ≈ₚ[RR] PTree.iter step2 j.
Proof. apply free_omega_peutt_iter_eventful_rel. Qed.
End RealBackend.

Section LargeCarrier.
Universe high.
Constraint Set < high.
Example high_eventful_iteration (I J A B : Type@{high})
    (step1 : I → ptree questionE SubEnumQ (I+A))
    (step2 : J → ptree questionE SubEnumQ (J+B))
    (SI : I → J → Prop) (RR : A → B → Prop) :
  (∀ i j, SI i j → step1 i ≈ₚ[pstruct_iter_sum_rel SI RR] step2 j) →
  ∀ i j, SI i j → PTree.iter step1 i ≈ₚ[RR] PTree.iter step2 j.
Proof. apply free_omega_peutt_iter_eventful_rel. Qed.
End LargeCarrier.
