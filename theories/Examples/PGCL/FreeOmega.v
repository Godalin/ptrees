(** Exact forward semantics of the State-effect frontend, for any native
    backend with the maintained FreeOmega profile. This is an instance of
    the generic proofs, not a second language semantics. No validation
    model participates in this development. *)
From Coq Require Import Utf8.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure Measure
  BindOrder RelationalLimit Coupling Quotient.
From PTree.Eq Require Import PTreeKernel PEutt.
From PTree.Eq.FreeOmega Require Import Hitting.
From PTree.Interp Require Import HandlerMachine ReturnIteration.
From PTree.Examples.PGCL Require Import Syntax Forward Interpretation Adequacy StateInterpretation.
Set Implicit Arguments.
Unset Strict Implicit.

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
End Completion.
