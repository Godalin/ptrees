(** Exact forward semantics of the State-effect frontend, for any native
    backend with the maintained FreeOmega profile. This is an instance of
    the generic proofs, not a second language semantics. No validation
    model participates in this development. *)
From Coq Require Import Utf8 Morphisms.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed KleisliIteration.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure Measure
  BindOrder RelationalLimit Coupling Quotient IterationOrder.
From PTree.Eq Require Import PTreeKernel PEutt.
From PTree.Eq.FreeOmega Require Import Hitting.
From PTree.Interp Require Import HandlerMachine ReturnIteration.
From PTree.Examples.PGCL Require Import Syntax Forward Algebra Interpretation Adequacy StateInterpretation.
Set Implicit Arguments.
Unset Strict Implicit.
Import FreeOmegaOrderNotations.
Local Open Scope freeomega_scope.

Section Completion.
Context {S P : Type} {MN E : Type → Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Variable coin : P → MN bool.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation D := (denote (S := S) (FI := FI) (FO := FO) coin).
Local Notation lift_return := (@iteration_return_map E MN MF FI).
Local Notation hits t out := (ptree_stable_hitting (FI := FI) (FO := FO) (observe t) out).

(** The same forward kernel is an actual complete frontier of the publicly
    interpreted State program. In particular it has no visible heads, even
    when the surrounding signature E is inhabited. *)
Theorem pgcl_run_hitting (c : command S P) s :
  hits (run (E := E) coin c s) (lift_return (D c s)).
Proof.
  eapply peutt_hitting_ret_only.
  - exact (run_execute free_omega_relational_mixed_bind
      free_omega_relational_zero free_omega_relational_lub coin c s).
  - eapply stable_hitting_output_transport.
    + apply handler_complete_front_hitting.
    + exact (execute_denote (E := E) (FI := FI) (FO := FO) coin c s).
  - unfold iteration_return_map. eapply free_omega_ae_bind.
    + apply (sem_ae_true (SI := FI)).
    + intros a _. constructor. exists a. reflexivity.
Qed.

Theorem pgcl_run_denotes_iff (c : command S P) (K : S → MF S) :
  denotes (FI := FI) (FO := FO) coin c K ↔
  ∀ s, hits (run (E := E) coin c s) (lift_return (K s)).
Proof.
  split.
  - intros HD s. eapply stable_hitting_output_transport; [apply pgcl_run_hitting|].
    change (@sem_eq MF FI _ (lift_return (D c s)) (lift_return (K s))).
    unfold iteration_return_map.
    apply sem_bind_eq_l. apply sem_eq_sym. exact (denotes_canonical HD s).
  - intro HK. eapply DenEquiv; [apply denote_spec|].
    intro s.
    pose proof (ptree_stable_hitting_unique (pgcl_run_hitting c s) (HK s)) as H.
    change (@sem_lift MF FI _ _ eq (lift_return (D c s)) (lift_return (K s))) in H.
    assert (Hret : ∀ A (mu : MF A), @sem_eq MF FI _ (sem_bind mu sem_ret) mu).
    { intros A mu. apply FOQLStructural. apply free_omega_bind_return_lift. }
    pose proof (sem_lift_map_reflect Hret H) as Hlift.
    change (@sem_lift MF FI _ _ eq (D c s) (K s)).
    eapply sem_lift_mono; [|exact Hlift].
    intros a b Hab. inversion Hab. reflexivity.
Qed.

Corollary pgcl_run_forward_correspondence (c : command S P) K s out :
  denotes (FI := FI) (FO := FO) coin c K →
  hits (run (E := E) coin c s) out →
  @sem_eq MF FI _ out (lift_return (K s)).
Proof.
  intros HD Hout. eapply ptree_stable_hitting_unique;
    [exact Hout|apply (proj1 (pgcl_run_denotes_iff c K) HD)].
Qed.

(** Source-level forward algebra can be used under PTree program contexts.
    This is a derived proof rule, not a new backend capability. *)
Theorem pgcl_denotation_peutt (c d : command S P) :
  kernel_eq (D c) (D d) → ∀ s,
  peutt (FI := FI) (FO := FO) eq
    (run (E := E) coin c s) (run coin d s).
Proof.
  intros Heq s. eapply peutt_of_hitting_lift;
    [apply pgcl_run_hitting|apply pgcl_run_hitting|].
  unfold iteration_return_map. eapply sem_lift_bind.
  - exact (Heq s).
  - intros a b ->. apply sem_lift_ret. constructor. reflexivity.
Qed.

(** Source rewrites also work below the public State interpretation. *)
#[global] Instance pgcl_run_Proper :
  Proper (cequiv (FI := FI) (FO := FO) coin ==> eq ==>
    peutt (FI := FI) (FO := FO) (@eq S)) (run (E := E) coin).
Proof. intros c d H s s' ->. apply pgcl_denotation_peutt, H. Qed.

(** Discharge the ordinary monad right unit once for the completion. *)
Theorem pgcl_seq_skip_r (c : command S P) :
  cequiv (FI := FI) (FO := FO) coin (CSeq c CSkip) c.
Proof.
  apply seq_skip_r. intro mu. apply FOQLStructural.
  apply free_omega_bind_return_lift.
Qed.
End Completion.

(** Leastness uses the public completion preorder, NOT the structural
    SemanticOmega order. This part needs only the native core laws;
    the fixed-point equation additionally uses the existing diagonal laws. *)
Section WhileOrder.
Context {S P : Type} {MN : Type → Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Variable coin : P → MN bool.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation D := (denote (S := S) (FI := FI) (FO := FO) coin).

Theorem pgcl_while_least_prefixed (b : S → bool) c (Y : S → FreeOmega MN S) :
  (∀ s, (if b s then sem_bind (D c s) Y else sem_ret s) ⊑ω Y s) →
  ∀ s, D (CWhile b c) s ⊑ω Y s.
Proof.
  intro HY. apply (free_omega_sem_iter_least_prefixed
    (K := while_kernel b (D c))).
  - intro s. apply iterate_spec.
  - intro s. eapply free_omega_sem_le_trans; [apply free_omega_sem_eq_le|apply HY].
    change (@sem_eq (FreeOmega MN) FI _
      (sem_iter_step (MI := FI) (while_kernel b (D c)) Y s)
      (if b s then sem_bind (D c s) Y else sem_ret s)).
    unfold sem_iter_step, while_kernel. destruct (b s).
    + change (free_omega_qlift eq
        (free_omega_bind (free_omega_bind (D c s) (λ t, FORet (inl t)))
          (λ v : S+S, match v with inl j => Y j | inr a => FORet a end))
        (free_omega_bind (D c s) Y)).
      rewrite free_omega_bind_assoc. apply free_omega_qlift_refl. intro x; reflexivity.
    + apply free_omega_qlift_refl. intro x; reflexivity.
Qed.

Context `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.

Theorem pgcl_while_least_fixed_point b c :
  (∀ s, @sem_eq (FreeOmega MN) FI _ (D (CWhile b c) s)
    (if b s then sem_bind (D c s) (D (CWhile b c)) else sem_ret s)) ∧
  (∀ Y : S → FreeOmega MN S,
    (∀ s, (if b s then sem_bind (D c s) Y else sem_ret s) ⊑ω Y s) →
    ∀ s, D (CWhile b c) s ⊑ω Y s).
Proof.
  split; [|apply pgcl_while_least_prefixed].
  pose proof (coupling_ae_implies_ae_lift (S := MN)) as NAE.
  exact (denote_while_unfold (FI := FI) (FO := FO) coin b c).
Qed.
End WhileOrder.
