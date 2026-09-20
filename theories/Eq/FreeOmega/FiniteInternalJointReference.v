Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From Coq Require Import Program.Equality Logic.ClassicalChoice.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure SemanticCoupling FreeOmegaMeasure
  FreeOmegaCoupling.
From PTree.Eq Require Import FiniteInternal PStrong PrimitiveStableHitting
  UnifiedFrontier PTreeKernel PEutt.
From PTree.Eq.FreeOmega Require Import FiniteInternalJoint FiniteInternalJointAcceleration.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Two sides may present the SAME correlated execution kernel differently.
    Each presentation has a structural graph for its own valid cut.  The
    two cut distributions need not themselves have a structural lifting.
    Reference kernels and their quotient equalities are proved premises,
    not a claim that every quotient residual coupling admits them. *)
Section ReferenceCoinduction.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI} {A B : Type}.
Variable RR : A -> B -> Prop.
Variable sim : ptree E MN A -> ptree E MN B -> Prop.
Local Notation Pair := (ptree E MN A * ptree E MN B)%type.
Local Notation Heads := (stable_head E MN A * stable_head E MN B)%type.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Variable cut1 : Pair -> MF (ptree E MN A).
Variable cut2 : Pair -> MF (ptree E MN B).
Hypothesis cut1_valid : forall t u, sim t u ->
  @finite_internal E MN MF FI FreeOmegaMixedMeasure A t (cut1 (t,u)).
Hypothesis cut2_valid : forall t u, sim t u ->
  @finite_internal E MN MF FI FreeOmegaMixedMeasure B u (cut2 (t,u)).
Hypothesis node_realizes : forall {X Y} (R : X -> Y -> Prop)
    (mu : MN X) (nu : MN Y), sem_lift R mu nu ->
    exists joint, semantic_coupling R mu nu joint.

Variables kernel left_reference right_reference : Pair -> MF (stable_target Pair Heads).
Hypothesis kernel_closed : forall t u, sim t u ->
  free_omega_ae (finite_internal_pair_invariant RR sim) (kernel (t,u)).
Hypothesis left_equal : forall t u, sim t u ->
  free_omega_qlift eq (left_reference (t,u)) (kernel (t,u)).
Hypothesis right_equal : forall t u, sim t u ->
  free_omega_qlift eq (right_reference (t,u)) (kernel (t,u)).
Hypothesis left_marginal : forall t u, sim t u ->
  free_omega_lift (fun z target => finite_internal_pair_left z = target)
    (left_reference (t,u))
    (free_omega_bind (cut1 (t,u)) finite_internal_guard_transition).
Hypothesis right_marginal : forall t u, sim t u ->
  free_omega_lift (fun z target => finite_internal_pair_right z = target)
    (right_reference (t,u))
    (free_omega_bind (cut2 (t,u)) finite_internal_guard_transition).

Lemma finite_internal_reference_closed reference
    (Heq : forall t u, sim t u -> free_omega_qlift eq (reference (t,u)) (kernel (t,u))) :
  forall p : Pair, sim (fst p) (snd p) ->
  free_omega_ae
    (KernelCompletion.kernel_completion_invariant (fun q => sim (fst q) (snd q)))
    (reference p).
Proof.
  intros [t u] Hsim.
  pose proof (proj2 (free_omega_qlift_support (Heq t u Hsim)) _
    (kernel_closed Hsim)) as Hsupport.
  eapply free_omega_ae_mono; [|exact Hsupport].
  intros z [w [-> Hw]]. destruct w; cbn; [exact I|exact Hw].
Qed.

Theorem finite_internal_reference_pair_hitting t u out1 out2 :
  sim t u ->
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A (observe t) out1 ->
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega B (observe u) out2 ->
  free_omega_qlift (stable_head_rel RR sim) out1 out2.
Proof.
  intros Hsim Hhit1 Hhit2.
  pose (joint_out := FOLub (fun n => @stable_hitting_approx MF FI
    FreeOmegaObservableSemanticOmega Pair Heads kernel n (t,u))).
  assert (Hjoint : @stable_hitting MF FI FreeOmegaObservableSemanticOmega
    Pair Heads kernel (t,u) joint_out).
  { apply free_omega_qlift_refl. intro h. reflexivity. }
  assert (Hleft : free_omega_qlift eq
    (free_omega_bind joint_out (fun h => FORet (fst h))) out1).
  { eapply finite_internal_structural_execution_adequate_modulo_eq with
      (project_state := @fst (ptree E MN A) (ptree E MN B))
      (D := fun p => sim (fst p) (snd p)) (cut := cut1)
      (kernel := left_reference) (represented := kernel) (s := (t,u)).
    - apply finite_internal_reference_closed. exact left_equal.
    - intros [x y] Hxy. exact (cut1_valid Hxy).
    - intros [x y] Hxy. exact (left_marginal Hxy).
    - exact (@node_realizes).
    - intros [x y] Hxy. exact (left_equal Hxy).
    - exact Hsim.
    - exact Hjoint.
    - exact Hhit1. }
  assert (Hright : free_omega_qlift eq
    (free_omega_bind joint_out (fun h => FORet (snd h))) out2).
  { eapply finite_internal_structural_execution_adequate_modulo_eq with
      (project_state := @snd (ptree E MN A) (ptree E MN B))
      (D := fun p => sim (fst p) (snd p)) (cut := cut2)
      (kernel := right_reference) (represented := kernel) (s := (t,u)).
    - apply finite_internal_reference_closed. exact right_equal.
    - intros [x y] Hxy. exact (cut2_valid Hxy).
    - intros [x y] Hxy. exact (right_marginal Hxy).
    - exact (@node_realizes).
    - intros [x y] Hxy. exact (right_equal Hxy).
    - exact Hsim.
    - exact Hjoint.
    - exact Hhit2. }
  pose proof (proj2 (finite_internal_paired_hitting_coupled
    kernel_closed Hsim Hjoint)) as Hcoupled.
  eapply FOQLComp with (T := eq) (U := stable_head_rel RR sim).
  - apply FOQLMono with (T := fun x y => y = x).
    + apply FOQLSym. exact Hleft.
    + intros x y Hxy. symmetry. exact Hxy.
  - eapply FOQLComp with (T := stable_head_rel RR sim) (U := eq).
    + exact Hcoupled.
    + exact Hright.
    + intros x z [y [Hxy ->]]. exact Hxy.
  - intros x z [y [-> Hyz]]. exact Hyz.
Qed.

Theorem peutt_coinduction_finite_internal_references t u :
  sim t u ->
  @peutt E MN MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A B RR t u.
Proof.
  intro Hsim. eapply peutt_coinduction with
    (sim := fun s1 s2 => exists x y,
      s1 = observe x /\ s2 = observe y /\ sim x y).
  - intros s1 s2 [x [y [-> [-> Hxy]]]].
    eapply stable_hitting_match_of_hitting_lift with
      (out1 := FOLub (fun n => @ptree_hitting_approx E MN MF FI
        FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A n (observe x)))
      (out2 := FOLub (fun n => @ptree_hitting_approx E MN MF FI
        FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega B n (observe y))).
    + apply free_omega_qlift_refl. intro h. reflexivity.
    + apply free_omega_qlift_refl. intro h. reflexivity.
    + eapply FOQLMono with (T := stable_head_rel RR sim).
      * eapply finite_internal_reference_pair_hitting with (t := x) (u := y);
          [exact Hxy| |].
        -- apply free_omega_qlift_refl. intro h. reflexivity.
        -- apply free_omega_qlift_refl. intro h. reflexivity.
      * intros h1 h2 Hhead. dependent destruction Hhead.
        -- constructor. exact H.
        -- constructor. intro z. exists (k1 z), (k2 z).
           repeat split; try reflexivity. exact (H z).
  - exists t, u. repeat split; try reflexivity. exact Hsim.
Qed.

End ReferenceCoinduction.

(** The client supplies references only for residual distributions.  The
    library constructs the paired guard and both execution kernels; it
    never asks for a pre-existing equivalence of the continuations. *)
Section ResidualReferences.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI} {A B : Type}.
Variable RR : A -> B -> Prop.
Variable sim : ptree E MN A -> ptree E MN B -> Prop.
Local Notation Pair := (ptree E MN A * ptree E MN B)%type.
Local Notation Heads := (stable_head E MN A * stable_head E MN B)%type.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Variable cut1 : Pair -> MF (ptree E MN A).
Variable cut2 : Pair -> MF (ptree E MN B).
Variables left_joint right_joint : Pair -> MF Pair.
Hypothesis cuts_references : forall t u, sim t u ->
  free_omega_coupling_references (fun t u => pstrongF RR sim (observe t) (observe u))
    (cut1 (t,u)) (cut2 (t,u)) (left_joint (t,u)) (right_joint (t,u)).
Hypothesis node_realizes : forall {X Y} (R : X -> Y -> Prop)
    (mu : MN X) (nu : MN Y), sem_lift R mu nu ->
    exists joint, semantic_coupling R mu nu joint.

Theorem finite_internal_reference_kernels_exists :
  exists left right : Pair -> MF (stable_target Pair Heads),
    forall t u, sim t u ->
      free_omega_qlift eq (left (t,u)) (right (t,u)) /\
      free_omega_lift (fun z target => finite_internal_pair_left z = target)
        (left (t,u))
        (free_omega_bind (cut1 (t,u)) finite_internal_guard_transition) /\
      free_omega_lift (fun z target => finite_internal_pair_right z = target)
        (right (t,u))
        (free_omega_bind (cut2 (t,u)) finite_internal_guard_transition) /\
      free_omega_ae (finite_internal_pair_invariant RR sim) (left (t,u)).
Proof.
  assert (Hex : forall p : Pair, exists step : MF (stable_target Pair Heads),
    (fun t u => pstrongF RR sim (observe t) (observe u)) (fst p) (snd p) ->
      free_omega_lift (fun z x => finite_internal_pair_left z = x)
        step (finite_internal_guard_transition (fst p)) /\
      free_omega_lift (fun z y => finite_internal_pair_right z = y)
        step (finite_internal_guard_transition (snd p)) /\
      free_omega_ae (finite_internal_pair_invariant RR sim) step).
  { intros [t u]. destruct (classic ((fun t u => pstrongF RR sim (observe t) (observe u)) t u)) as [Hguard|Hnot].
    - destruct (finite_internal_guard_structural_joint_exists (@node_realizes) Hguard)
        as [step Hstep]. exists step. intros _. exact Hstep.
    - exists FOZero. intro Hguard. contradiction. }
  destruct (choice _ Hex) as [step Hstep].
  exists (fun p => free_omega_bind (left_joint p) step),
    (fun p => free_omega_bind (right_joint p) step).
  intros t u Hsim. pose proof (cuts_references Hsim) as Hcut. split.
  - eapply FOQLBind; [exact (proj1 Hcut)|].
    intros p q ->. apply free_omega_qlift_refl. intro z. reflexivity.
  - split.
    + eapply free_omega_lift_bind;
        [exact (free_omega_coupling_references_left_supported Hcut)|].
      intros [x y] z [<- Hxy]. exact (proj1 (Hstep (x,y) Hxy)).
    + split.
      * eapply free_omega_lift_bind;
          [exact (free_omega_coupling_references_right_supported Hcut)|].
        intros [x y] z [<- Hxy]. exact (proj1 (proj2 (Hstep (x,y) Hxy))).
      * eapply free_omega_ae_bind; [exact (proj2 (proj2 (proj2 Hcut)))|].
        intros [x y] Hxy. exact (proj2 (proj2 (Hstep (x,y) Hxy))).
Qed.

Hypothesis cut1_valid : forall t u, sim t u ->
  @finite_internal E MN MF FI FreeOmegaMixedMeasure A t (cut1 (t,u)).
Hypothesis cut2_valid : forall t u, sim t u ->
  @finite_internal E MN MF FI FreeOmegaMixedMeasure B u (cut2 (t,u)).

Theorem peutt_coinduction_finite_internal_coupling_references t u :
  sim t u ->
  @peutt E MN MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A B RR t u.
Proof.
  intro Hsim. destruct finite_internal_reference_kernels_exists as [left [right Hkernels]].
  eapply peutt_coinduction_finite_internal_references with
    (sim := sim) (cut1 := cut1) (cut2 := cut2)
    (kernel := left) (left_reference := left) (right_reference := right).
  - exact cut1_valid.
  - exact cut2_valid.
  - exact (@node_realizes).
  - intros x y Hxy. exact (proj2 (proj2 (proj2 (Hkernels x y Hxy)))).
  - intros x y _. apply free_omega_qlift_refl. intro z. reflexivity.
  - intros x y Hxy. apply FOQLMono with (T := fun p q => q = p).
    + apply FOQLSym. exact (proj1 (Hkernels x y Hxy)).
    + intros p q Hpq. symmetry. exact Hpq.
  - intros x y Hxy. exact (proj1 (proj2 (Hkernels x y Hxy))).
  - intros x y Hxy. exact (proj1 (proj2 (proj2 (Hkernels x y Hxy)))).
  - exact Hsim.
Qed.

End ResidualReferences.
