Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Logic.ClassicalChoice.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure SemanticCoupling FreeOmegaMeasure.
From PTree.Eq Require Import PStrong PFiniteResidual UnifiedFrontier
  PrimitiveStableHitting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A guarded round keeps its residual as a tree, so the next finite cut
    can depend on the entire pair.  This is an execution certificate, not
    a replacement for the canonical primitive kernel or for peutt. *)
Definition finite_internal_guard_transition
    {E MN : Type -> Type} {A} (t : ptree E MN A) :
    FreeOmega MN (stable_target (ptree E MN A) (stable_head E MN A)) :=
  match observe t with
  | RetF r => FORet (SHStable (FHRet r))
  | VisF _ e k => FORet (SHStable (FHVis e k))
  | TauF u => FORet (SHInternal u)
  | ProbF _ mu k => FOSample mu (fun x => FORet (SHInternal (k x)))
  end.

Section PairedTargets.
Context {E MN : Type -> Type} {A B : Type}.
Local Notation Pair := (ptree E MN A * ptree E MN B)%type.
Local Notation Heads := (stable_head E MN A * stable_head E MN B)%type.

Definition finite_internal_pair_left (target : stable_target Pair Heads) :=
  match target with
  | SHStable heads => SHStable (fst heads)
  | SHInternal trees => SHInternal (fst trees)
  end.

Definition finite_internal_pair_right (target : stable_target Pair Heads) :=
  match target with
  | SHStable heads => SHStable (snd heads)
  | SHInternal trees => SHInternal (snd trees)
  end.

Definition finite_internal_pair_invariant (RR : A -> B -> Prop)
    (sim : ptree E MN A -> ptree E MN B -> Prop)
    (target : stable_target Pair Heads) : Prop :=
  match target with
  | SHStable heads => stable_head_rel RR sim (fst heads) (snd heads)
  | SHInternal trees => sim (fst trees) (snd trees)
  end.
End PairedTargets.

Section JointGuard.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Context {A B : Type} (RR : A -> B -> Prop).
Variable sim : ptree E MN A -> ptree E MN B -> Prop.
Local Notation Pair := (ptree E MN A * ptree E MN B)%type.
Local Notation Heads := (stable_head E MN A * stable_head E MN B)%type.
Local Notation MF := (FreeOmega MN).

Hypothesis node_realizes : forall {X Y} (S : X -> Y -> Prop)
    (mu : MN X) (nu : MN Y), sem_lift S mu nu ->
    exists joint, semantic_coupling S mu nu joint.

(** Only a node-coupling realizer is required for the guard itself.
    Realization of arbitrary residual quotient couplings is a separate
    obligation; it is not hidden in this statement. *)
Theorem finite_internal_guard_joint_exists t u :
  pfinite_guard RR sim t u ->
  exists joint : MF (stable_target Pair Heads),
    free_omega_qlift (fun z x => finite_internal_pair_left z = x)
      joint (finite_internal_guard_transition t) /\
    free_omega_qlift (fun z y => finite_internal_pair_right z = y)
      joint (finite_internal_guard_transition u) /\
    free_omega_ae (finite_internal_pair_invariant RR sim) joint.
Proof.
  intro Hguard. unfold pfinite_guard, finite_internal_guard_transition in *.
  remember (observe t) as ot in Hguard |- *.
  remember (observe u) as ou in Hguard |- *.
  destruct Hguard.
  - exists (FORet (SHStable (FHRet r1, FHRet r2))). split.
    + apply FOQLStructural, FOLRet. reflexivity.
    + split; [apply FOQLStructural, FOLRet; reflexivity|].
      apply FOAERet. cbn. constructor. exact H.
  - exists (FORet (SHInternal (t1,t2))). split.
    + apply FOQLStructural, FOLRet. reflexivity.
    + split; [apply FOQLStructural, FOLRet; reflexivity|].
      apply FOAERet. exact H.
  - exists (FORet (SHStable (FHVis e k1, FHVis e k2))). split.
    + apply FOQLStructural, FOLRet. reflexivity.
    + split; [apply FOQLStructural, FOLRet; reflexivity|].
      apply FOAERet. cbn. constructor. exact H.
  - destruct (node_realizes H) as [node_joint Hjoint].
    exists (FOSample node_joint
      (fun p => FORet (SHInternal (k1 (fst p), k2 (snd p))))). split.
    + eapply FOQLSample; [exact (semantic_coupling_left_supported Hjoint)|].
      intros [x y] z [<- Hxy]. apply FOQLStructural, FOLRet. reflexivity.
    + split.
      * eapply FOQLSample; [exact (semantic_coupling_right_supported Hjoint)|].
        intros [x y] z [<- Hxy]. apply FOQLStructural, FOLRet. reflexivity.
      * eapply FOAESample; [exact (proj2 (proj2 Hjoint))|].
        intros [x y] Hxy. apply FOAERet. exact Hxy.
Qed.

End JointGuard.

Section JointRounds.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Context {A B : Type} (RR : A -> B -> Prop).
Variable sim : ptree E MN A -> ptree E MN B -> Prop.
Local Notation Pair := (ptree E MN A * ptree E MN B)%type.
Local Notation Heads := (stable_head E MN A * stable_head E MN B)%type.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

Hypothesis node_realizes : forall {X Y} (S : X -> Y -> Prop)
    (mu : MN X) (nu : MN Y), sem_lift S mu nu ->
    exists joint, semantic_coupling S mu nu joint.

Variable cut1 : Pair -> MF (ptree E MN A).
Variable cut2 : Pair -> MF (ptree E MN B).
Hypothesis cuts_realized : forall t u, sim t u ->
  exists joint, @semantic_coupling MF FI _ _ (pfinite_guard RR sim)
    (cut1 (t,u)) (cut2 (t,u)) joint.

(** The two cut functions and their coupling depend on the PAIR.  No
    marginal policy is selected or assumed to exist.  Cut validity is used
    by acceleration adequacy, not by this construction of the joint round.
    In particular this theorem does not claim that arbitrary residual
    quotient couplings have the supplied [cuts_realized] witnesses. *)
Theorem finite_internal_paired_kernel_exists :
  exists kernel : Pair -> MF (stable_target Pair Heads),
    forall t u, sim t u ->
      free_omega_qlift (fun z x => finite_internal_pair_left z = x)
        (kernel (t,u))
        (free_omega_bind (cut1 (t,u)) finite_internal_guard_transition) /\
      free_omega_qlift (fun z y => finite_internal_pair_right z = y)
        (kernel (t,u))
        (free_omega_bind (cut2 (t,u)) finite_internal_guard_transition) /\
      free_omega_ae (finite_internal_pair_invariant RR sim) (kernel (t,u)).
Proof.
  assert (Hcuts : forall p : Pair, exists joint : MF Pair,
    sim (fst p) (snd p) ->
      @semantic_coupling MF FI _ _ (pfinite_guard RR sim)
        (cut1 p) (cut2 p) joint).
  { intros [t u]. destruct (classic (sim t u)) as [Hsim|Hnot].
    - destruct (cuts_realized Hsim) as [joint Hjoint].
      exists joint. intros _. exact Hjoint.
    - exists FOZero. intro Hsim. contradiction. }
  destruct (choice _ Hcuts) as [cut_joint Hcut_joint].
  assert (Hex : forall p : Pair, exists step : MF (stable_target Pair Heads),
    pfinite_guard RR sim (fst p) (snd p) ->
      free_omega_qlift (fun z x => finite_internal_pair_left z = x)
        step (finite_internal_guard_transition (fst p)) /\
      free_omega_qlift (fun z y => finite_internal_pair_right z = y)
        step (finite_internal_guard_transition (snd p)) /\
      free_omega_ae (finite_internal_pair_invariant RR sim) step).
  { intros [t u]. destruct (classic (pfinite_guard RR sim t u)) as [Hguard|Hnot].
    - destruct (finite_internal_guard_joint_exists (@node_realizes) Hguard)
        as [step Hstep]. exists step. intros _. exact Hstep.
    - exists FOZero. intro Hguard. contradiction. }
  destruct (choice _ Hex) as [step Hstep].
  exists (fun p => free_omega_bind (cut_joint p) step).
  intros t u Hsim. pose proof (Hcut_joint (t,u) Hsim) as Hjoint. split.
  - eapply FOQLBind; [exact (semantic_coupling_left_supported Hjoint)|].
    intros [x y] z [<- Hxy]. exact (proj1 (Hstep (x,y) Hxy)).
  - split.
    + eapply FOQLBind; [exact (semantic_coupling_right_supported Hjoint)|].
      intros [x y] z [<- Hxy]. exact (proj1 (proj2 (Hstep (x,y) Hxy))).
    + eapply free_omega_ae_bind; [exact (proj2 (proj2 Hjoint))|].
      intros [x y] Hxy. exact (proj2 (proj2 (Hstep (x,y) Hxy))).
Qed.

(** Once a joint round kernel is fixed, its increasing approximants come
    from recursive execution of THAT kernel.  We never select fresh
    couplings independently at each fuel and assume they are increasing. *)
Variable kernel : Pair -> MF (stable_target Pair Heads).
Hypothesis kernel_closed : forall t u, sim t u ->
  free_omega_ae (finite_internal_pair_invariant RR sim) (kernel (t,u)).

Theorem finite_internal_paired_rounds_increasing p :
  forall n, free_omega_approx eq
    (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
      Pair Heads kernel n p)
    (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
      Pair Heads kernel (S n) p).
Proof.
  exact (@stable_hitting_increasing MF FI FreeOmegaObservableSemanticOmega
    FreeOmegaObservableSemanticMeasureOrderLaws Pair Heads kernel p).
Qed.

(** Arbitrarily many correlated rounds preserve the head relation,
    including purely internal loops and partial divergence.  Their two
    projected limits are coupled.  Identifying those projections with the
    ORIGINAL trees' complete hitting still requires correlated acceleration
    adequacy; that conclusion is deliberately absent here. *)
Theorem finite_internal_paired_hitting_coupled t u out :
  sim t u ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega
    Pair Heads kernel (t,u) out ->
  free_omega_ae (fun p => stable_head_rel RR sim (fst p) (snd p)) out /\
  free_omega_qlift (stable_head_rel RR sim)
    (free_omega_bind out (fun p => FORet (fst p)))
    (free_omega_bind out (fun p => FORet (snd p))).
Proof.
  intros Hsim Hhit.
  assert (Hae : free_omega_ae
    (fun p => stable_head_rel RR sim (fst p) (snd p)) out).
  { eapply (@stable_hitting_ae MF FI FreeOmegaObservableSemanticOmega
      FreeOmegaObservableSemanticMeasureAEKleisliLaws
      FreeOmegaObservableSemanticOmegaAELaws Pair Heads kernel
      (fun p => sim (fst p) (snd p))
      (fun p => stable_head_rel RR sim (fst p) (snd p)))
      with (state := (t,u)).
    - intros [x y] Hxy. exact (kernel_closed Hxy).
    - exact Hsim.
    - exact Hhit. }
  split; [exact Hae|].
  eapply FOQLBind with
    (T := fun p q => p = q /\ stable_head_rel RR sim (fst p) (snd p)).
  - eapply FOQLAERestrict with (T := eq)
      (P := fun p => stable_head_rel RR sim (fst p) (snd p))
      (Q := fun _ => True).
    + apply free_omega_qlift_refl. intro p. reflexivity.
    + exact Hae.
    + apply (@sem_ae_true MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
    + intros p q [Hp [HR _]]. split; assumption.
  - intros p q [<- HR]. apply FOQLStructural, FOLRet. exact HR.
Qed.

End JointRounds.
