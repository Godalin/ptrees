(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From Coq.Arith Require Import PeanoNat.
From Coq Require Import Lia.
From Coq.Logic Require Import ClassicalChoice.
From Coq.Program Require Import Equality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure SemanticCoupling.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Eq.Internal Require Import FiniteInternal.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier PTreeKernel.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternal FiniteInternalJoint FiniteInternalJointCoverage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Truncation of a structurally realized round, retaining the original
    joint carrier.  Sampling witnesses are refined by a NODE joint, not
    by selecting a deterministic partner for an existential support fact. *)
Section JointTruncation.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NO : @SemanticOmega MN NI} {A Z : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation tree := (ptree E MN A).
Local Notation head := (stable_head E MN A).
Local Notation hit := (@ptree_hitting_approx E MN MF FI
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A).
Local Notation guard_approx := (@finite_internal_guard_approx E MN NI NO A).

Variable project : Z -> stable_target tree head.
Local Notation finish := (fun n z => guard_approx n (project z)).

Definition finite_internal_joint_approximates t (joint : MF Z)
    (chain : nat -> MF Z) : Prop :=
  (forall n, free_omega_approx eq (chain n) (chain (S n))) /\
  free_omega_qlift eq joint (FOLub chain) /\
  (forall n, free_omega_approx eq (chain n) joint) /\
  (forall n m, free_omega_approx eq (free_omega_bind (chain n) (finish m))
    (hit (n + m) (observe t))) /\
  (forall n, free_omega_approx eq (hit n (observe t))
    (free_omega_bind (chain n) (finish n))).

Lemma finite_internal_guard_approx_increasing n target :
  free_omega_approx eq (guard_approx n target) (guard_approx (S n) target).
Proof.
  destruct target as [h|t]; [apply FOApproxRet; reflexivity|].
  destruct n as [|n]; [apply FOApproxZero|].
  apply (@PTreeKernel.ptree_hitting_mono E MN MF FI
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
    FreeOmegaObservableSemanticMeasureOrderLaws A). lia.
Qed.

Hypothesis node_realizes : forall {X Y} (R : X -> Y -> Prop)
    (mu : MN X) (nu : MN Y), sem_lift R mu nu ->
    exists joint, semantic_coupling R mu nu joint.

Theorem finite_internal_joint_approximation_exists t out :
  @finite_internal E MN MF FI FreeOmegaMixedMeasure A t out ->
  forall joint,
  free_omega_lift (fun target z => project z = target)
    (free_omega_bind out finite_internal_guard_transition) joint ->
  exists chain, finite_internal_joint_approximates t joint chain.
Proof.
  intro Hcut. induction Hcut as [t|t out Hcut IH|X mu k out Hcuts IH];
    intros joint Hgraph.
  - exists (fun _ => joint). repeat split.
    + intro n. apply free_omega_approx_refl. intro z. reflexivity.
    + apply FOQLLubConstantR, free_omega_qlift_refl. intro z. reflexivity.
    + intro n. apply free_omega_approx_refl. intro z. reflexivity.
    + intros n m. eapply free_omega_approx_trans with (nu := hit m (observe t)).
      * rewrite finite_internal_guard_approxE.
        eapply free_omega_approx_bind.
        -- apply free_omega_lift_to_approx, free_omega_lift_sym. exact Hgraph.
        -- intros z target <-. apply free_omega_approx_refl. intro h. reflexivity.
      * apply (@PTreeKernel.ptree_hitting_mono E MN MF FI
          FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
          FreeOmegaObservableSemanticMeasureOrderLaws A). lia.
    + intro n. rewrite finite_internal_guard_approxE.
      eapply free_omega_approx_bind.
      * apply free_omega_lift_to_approx. exact Hgraph.
      * intros target z <-. apply free_omega_approx_refl. intro h. reflexivity.
  - destruct (IH joint Hgraph) as [chain [Hinc [Hlim [Hbelow [Hupper Hcover]]]]].
    exists (fun n => match n with 0 => FOZero | S m => chain m end).
    repeat split.
    + intros [|n]; [apply FOApproxZero|apply Hinc].
    + apply finite_internal_prefix_limit. exact Hlim.
    + intros [|n]; [apply FOApproxZero|apply Hbelow].
    + intros [|n] m; [apply FOApproxZero|]. exact (Hupper n m).
    + intros [|n]; [apply FOApproxZero|].
      eapply free_omega_approx_trans; [exact (Hcover n)|].
      eapply free_omega_approx_bind with (R := eq).
      * apply free_omega_approx_refl. intro z. reflexivity.
      * intros x y ->. apply finite_internal_guard_approx_increasing.
  - change (free_omega_lift (fun target z => project z = target)
      (FOSample mu (fun x => free_omega_bind (out x) finite_internal_guard_transition))
      joint) in Hgraph.
    dependent destruction Hgraph.
    rename S into Related.
    destruct (node_realizes H) as [node_joint Hjoint].
    assert (Hex : forall p : X * Y, exists c : nat -> MF Z,
      Related (fst p) (snd p) ->
      finite_internal_joint_approximates (k (fst p)) (h (snd p)) c).
    { intros [x y]. destruct (classic (Related x y)) as [Hxy|Hnot].
      - destruct (IH x (h y) (H0 x y Hxy)) as [c Hc].
        exists c. intros _. exact Hc.
      - exists (fun _ => FOZero). intro Hxy. contradiction. }
    destruct (choice _ Hex) as [chains Hchains].
    pose (rows := fun (p : X * Y) n =>
      match n with 0 => FOZero | Datatypes.S m => chains p m end).
    pose proof (semantic_coupling_left_supported Hjoint) as Hleft.
    pose proof (semantic_coupling_right_supported Hjoint) as Hright.
    assert (Hrows_inc : forall p, Related (fst p) (snd p) -> forall n,
      free_omega_approx eq (rows p n) (rows p (Datatypes.S n))).
    { intros p Hp [|n]; [apply FOApproxZero|]. exact (proj1 (Hchains p Hp) n). }
    assert (Hrows_lim : forall p, Related (fst p) (snd p) ->
      free_omega_qlift eq (h (snd p)) (FOLub (rows p))).
    { intros p Hp. apply finite_internal_prefix_limit.
      exact (proj1 (proj2 (Hchains p Hp))). }
    exists (fun n => FOSample node_joint (fun p => rows p n)). repeat split.
    + intro n. eapply FOApproxSample with
        (S := fun p q => p = q /\ Related (fst p) (snd p)).
      * apply sem_lift_refl_ae. exact (proj2 (proj2 Hjoint)).
      * intros p q [<- Hp]. apply Hrows_inc. exact Hp.
    + eapply FOQLComp with (T := eq) (U := eq)
        (mid := FOSample node_joint (fun p => h (snd p))).
      * eapply FOQLSample; [apply sem_lift_sym; exact Hright|].
        intros y [x z] [<- Hxz]. apply free_omega_qlift_refl. intro w. reflexivity.
      * eapply FOQLSampleLub with (Good := fun p => Related (fst p) (snd p)).
        -- exact (proj2 (proj2 Hjoint)).
        -- exact Hrows_inc.
        -- exact Hrows_lim.
      * intros x z [y [-> ->]]. reflexivity.
    + intro n. eapply FOApproxSample; [exact Hright|].
      intros [x y] z [<- Hxy]. destruct n as [|n]; [apply FOApproxZero|].
      exact (proj1 (proj2 (proj2 (Hchains (x,y) Hxy))) n).
    + intros [|n] m.
      * destruct m; eapply FOApproxSample; try exact Hleft;
          intros p x Hp; apply FOApproxZero.
      * eapply FOApproxSample; [exact Hleft|].
        intros [x y] z [<- Hxy].
        exact (proj1 (proj2 (proj2 (proj2 (Hchains (x,y) Hxy)))) n m).
    + intros [|n].
      * eapply FOApproxSample; [apply sem_lift_sym; exact Hleft|].
        intros x p Hp. apply FOApproxZero.
      * eapply FOApproxSample; [apply sem_lift_sym; exact Hleft|].
        intros x [a b] [<- Hab]. eapply free_omega_approx_trans.
        -- exact (proj2 (proj2 (proj2 (proj2 (Hchains (a,b) Hab)))) n).
        -- eapply free_omega_approx_bind with (R := eq).
           ++ apply free_omega_approx_refl. intro z. reflexivity.
           ++ intros z w ->. apply finite_internal_guard_approx_increasing.
Qed.

End JointTruncation.
