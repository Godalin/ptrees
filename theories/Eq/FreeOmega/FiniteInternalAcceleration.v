Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Arith.PeanoNat Lia Logic.ClassicalChoice
  FunctionalExtensionality Program.Equality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure
  SemanticCoupling FreeOmegaCoupling.
From PTree.Eq Require Import
  FiniteInternal UnifiedFrontier PrimitiveStableHitting PTreeKernel
  PFinite PEutt.
From PTree.Eq.FreeOmega Require Import FiniteInternal FiniteInternalJoint KernelContinuity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Adequacy of repeatedly taking a selected well-founded internal cut and
    then a primitive guard.  All indices below belong to the adequacy proof;
    the operational cut and the residual finite relation remain unindexed. *)
Section Acceleration.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI} {R : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation hit := (@ptree_hitting_approx E MN MF FI
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega R).

Lemma finite_internal_hitting_zero :
  (fun t => hit 0 (observe t)) = finite_internal_advance (fun _ => FOZero).
Proof.
  apply functional_extensionality. intro t.
  unfold finite_internal_advance. destruct (observe t); reflexivity.
Qed.

Lemma finite_internal_hitting_succ n :
  (fun t => hit (S n) (observe t)) =
  finite_internal_advance (fun t => hit n (observe t)).
Proof.
  apply functional_extensionality. intro t.
  unfold finite_internal_advance. destruct (observe t); reflexivity.
Qed.

Lemma finite_internal_rounds_cut_mono
    (cut1 cut2 : ptree E MN R -> MF (ptree E MN R)) :
  (forall t, free_omega_approx eq (cut1 t) (cut2 t)) ->
  forall n t, free_omega_approx eq
    (finite_internal_rounds cut1 n t) (finite_internal_rounds cut2 n t).
Proof.
  intro Hcut. intro n. induction n as [|n IH]; intro t;
    cbn [finite_internal_rounds];
    eapply free_omega_approx_bind with (R := eq).
  all: try apply Hcut.
  - intros x y ->. apply free_omega_approx_refl. intro h. reflexivity.
  - intros x y ->. apply finite_internal_advance_mono. exact IH.
Qed.

Definition finite_internal_round_kernel
    (selected : ptree E MN R -> MF (ptree E MN R)) t :=
  free_omega_bind (selected t) finite_internal_guard_transition.

Lemma finite_internal_rounds_kernelE selected n t :
  finite_internal_rounds selected n t =
  @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
    (ptree E MN R) (stable_head E MN R)
    (finite_internal_round_kernel selected) n t.
Proof.
  change (finite_internal_rounds selected n t =
    free_omega_bind (free_omega_bind (selected t) finite_internal_guard_transition)
      (@stable_target_approx MF FI FreeOmegaObservableSemanticOmega
        (ptree E MN R) (stable_head E MN R)
        (finite_internal_round_kernel selected) n)).
  induction n as [|n IH] in t |- *;
    cbn [finite_internal_rounds]; rewrite free_omega_bind_assoc;
    f_equal; apply functional_extensionality; intro u;
    unfold finite_internal_advance, finite_internal_guard_transition;
    destruct (observe u); cbn [free_omega_bind stable_target_approx].
  all: try reflexivity.
  - apply IH.
  - f_equal. apply functional_extensionality. intro x. apply IH.
Qed.

Variable cut : ptree E MN R -> MF (ptree E MN R).
Variable trunc : ptree E MN R -> nat -> MF (ptree E MN R).
Hypothesis trunc_spec : forall t, finite_internal_approximates t (cut t) (trunc t).

Definition finite_internal_grid n m t :=
  finite_internal_rounds (fun u => trunc u m) n t.

Lemma finite_internal_grid_inner n m t :
  free_omega_approx eq (finite_internal_grid n m t)
    (finite_internal_grid n (S m) t).
Proof.
  apply finite_internal_rounds_cut_mono. intro u.
  exact (proj1 (trunc_spec u) m).
Qed.

Lemma finite_internal_grid_outer n m t :
  free_omega_approx eq (finite_internal_grid n m t)
    (finite_internal_grid (S n) m t).
Proof. apply finite_internal_rounds_increasing. Qed.

Lemma finite_internal_grid_upper n m t :
  free_omega_approx eq (finite_internal_grid n m t)
    (hit ((S n) * (S m)) (observe t)).
Proof.
  induction n as [|n IH] in t |- *.
  - eapply free_omega_approx_trans.
    + unfold finite_internal_grid. cbn [finite_internal_rounds].
      rewrite <- finite_internal_hitting_zero.
      exact (proj1 (proj2 (proj2 (trunc_spec t))) m 0).
    + apply (@PTreeKernel.ptree_hitting_mono E MN MF FI
        FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
        FreeOmegaObservableSemanticMeasureOrderLaws R). lia.
  - eapply free_omega_approx_trans with
      (nu := free_omega_bind (trunc t m)
        (fun u => hit (S ((S n) * (S m))) (observe u))).
    + rewrite finite_internal_hitting_succ.
      change (free_omega_approx eq
        (free_omega_bind (trunc t m)
          (finite_internal_advance (finite_internal_grid n m)))
        (free_omega_bind (trunc t m)
          (finite_internal_advance (fun u => hit ((S n) * (S m)) (observe u))))).
      eapply free_omega_approx_bind with (R := eq).
      * apply free_omega_approx_refl. intro u. reflexivity.
      * intros u v ->. apply finite_internal_advance_mono. exact IH.
    + eapply free_omega_approx_trans.
      * exact (proj1 (proj2 (proj2 (trunc_spec t))) m (S ((S n) * (S m)))).
      * apply (@PTreeKernel.ptree_hitting_mono E MN MF FI
          FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
          FreeOmegaObservableSemanticMeasureOrderLaws R). lia.
Qed.

Lemma finite_internal_trunc_mono t n m : n <= m ->
  free_omega_approx eq (trunc t n) (trunc t m).
Proof.
  intro Hle. induction Hle.
  - apply free_omega_approx_refl. intro u. reflexivity.
  - eapply free_omega_approx_trans; [exact IHHle|].
    exact (proj1 (trunc_spec t) m).
Qed.

Lemma finite_internal_grid_covers n m t : n <= m ->
  free_omega_approx eq (hit n (observe t)) (finite_internal_grid n m t).
Proof.
  induction n as [|n IH] in t |- *; intro Hnm;
    eapply free_omega_approx_trans.
  - exact (proj2 (proj2 (proj2 (trunc_spec t))) 0).
  - unfold finite_internal_grid. cbn [finite_internal_rounds].
    rewrite <- finite_internal_hitting_zero.
    change (free_omega_approx eq
      (free_omega_bind (trunc t 0) (fun u => hit 0 (observe u)))
      (free_omega_bind (trunc t m) (fun u => hit 0 (observe u)))).
    eapply free_omega_approx_bind with (R := eq).
    + apply finite_internal_trunc_mono. exact Hnm.
    + intros u v ->. apply free_omega_approx_refl. intro h. reflexivity.
  - exact (proj2 (proj2 (proj2 (trunc_spec t))) (S n)).
  - rewrite finite_internal_hitting_succ.
    change (free_omega_approx eq
      (free_omega_bind (trunc t (S n))
        (finite_internal_advance (fun u => hit n (observe u))))
      (free_omega_bind (trunc t m)
        (finite_internal_advance (finite_internal_grid n m)))).
    eapply free_omega_approx_bind with (R := eq).
    + apply finite_internal_trunc_mono. exact Hnm.
    + intros u v ->. apply finite_internal_advance_mono.
      intro w. apply IH. lia.
Qed.

Theorem finite_internal_grid_cofinal t :
  free_omega_chains_cofinal eq
    (fun n => hit n (observe t)) (fun n => finite_internal_grid n n t).
Proof.
  split.
  - intro n. exists n. apply finite_internal_grid_covers. reflexivity.
  - intro n. exists ((S n) * (S n)).
    eapply free_omega_approx_mono with (R := eq).
    + intros x y ->. reflexivity.
    + apply finite_internal_grid_upper.
Qed.

Context `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}.

Lemma finite_internal_round_kernel_increasing n t :
  free_omega_approx eq
    (finite_internal_round_kernel (fun u => trunc u n) t)
    (finite_internal_round_kernel (fun u => trunc u (S n)) t).
Proof.
  eapply free_omega_approx_bind with (R := eq).
  - exact (proj1 (trunc_spec t) n).
  - intros x y ->. apply free_omega_approx_refl. intro z. reflexivity.
Qed.

Lemma finite_internal_round_kernel_limit t :
  free_omega_qlift eq (finite_internal_round_kernel cut t)
    (FOLub (fun n => finite_internal_round_kernel (fun u => trunc u n) t)).
Proof.
  unfold finite_internal_round_kernel.
  change (free_omega_qlift eq (free_omega_bind (cut t) finite_internal_guard_transition)
    (free_omega_bind (FOLub (trunc t)) finite_internal_guard_transition)).
  eapply FOQLBind with (T := eq).
  - exact (proj1 (proj2 (trunc_spec t))).
  - intros x y ->. apply free_omega_qlift_refl. intro z. reflexivity.
Qed.

Lemma finite_internal_rounds_limit n t :
  free_omega_qlift eq (finite_internal_rounds cut n t)
    (FOLub (fun m => finite_internal_grid n m t)).
Proof.
  unfold finite_internal_grid. rewrite finite_internal_rounds_kernelE.
  assert (Hrows : (fun m => finite_internal_rounds (fun u => trunc u m) n t) =
    (fun m => @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
      (ptree E MN R) (stable_head E MN R)
      (finite_internal_round_kernel (fun u => trunc u m)) n t)).
  { apply functional_extensionality. intro m. apply finite_internal_rounds_kernelE. }
  rewrite Hrows.
  exact (kernel_hitting_approx_limit finite_internal_round_kernel_increasing
    finite_internal_round_kernel_limit n t).
Qed.

Theorem finite_internal_acceleration_limit t :
  free_omega_qlift eq
    (FOLub (fun n => finite_internal_rounds cut n t))
    (FOLub (fun n => hit n (observe t))).
Proof.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := FOLub (fun n => FOLub (fun m => finite_internal_grid n m t))).
  - apply FOQLLub. intro n. apply finite_internal_rounds_limit.
  - eapply FOQLComp with (T := eq) (U := eq)
      (mid := FOLub (fun n => finite_internal_grid n n t)).
    + eapply FOQLDoubleDiagonal with (HAB := eq_refl).
      * intros n m. apply finite_internal_grid_inner.
      * intros n m. apply finite_internal_grid_outer.
      * intro h. reflexivity.
      * apply free_omega_support_lift_double_diagonal.
        -- intros n m. apply finite_internal_grid_inner.
        -- intros n m. apply finite_internal_grid_outer.
    + apply FOQLSym. eapply FOQLMono.
      * apply FOQLCofinal.
        -- intro n. apply (@PTreeKernel.ptree_hitting_mono E MN MF FI
             FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega);
             try typeclasses eauto; lia.
        -- intro n. eapply free_omega_approx_trans.
           ++ apply finite_internal_grid_inner.
           ++ apply finite_internal_grid_outer.
        -- apply finite_internal_grid_cofinal.
      * intros x y ->. reflexivity.
    + intros x z [y [-> ->]]. reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

End Acceleration.

(** There is no scheduling assumption here: the truncation grid is obtained
    from the well-founded cut derivations themselves.  This establishes
    complete hitting adequacy for any single selected compression policy. *)
Theorem finite_internal_acceleration
    {E MN : Type -> Type}
    `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NO : @SemanticOmega MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {R : Type}
    (cut : ptree E MN R -> FreeOmega MN (ptree E MN R)) :
  (forall t, @finite_internal E MN (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure R t (cut t)) ->
  forall t, free_omega_qlift eq
    (FOLub (fun n => finite_internal_rounds cut n t))
    (FOLub (fun n => @ptree_hitting_approx E MN (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega R n (observe t))).
Proof.
  intro Hcut.
  assert (Hex : forall t, exists chain, finite_internal_approximates t (cut t) chain).
  { intro t. apply finite_internal_approximation_exists. apply Hcut. }
  destruct (choice _ Hex) as [trunc Htrunc]. intro t.
  exact (finite_internal_acceleration_limit Htrunc t).
Qed.

(** The complete acceleration equality also has an explicit joint witness.
    Unlike structural realization, this corollary accepts the quotient
    equality proved above, including its diagonal/cofinal limit steps. *)
Corollary finite_internal_acceleration_joint
    {E MN : Type -> Type}
    `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NO : @SemanticOmega MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {R : Type}
    (cut : ptree E MN R -> FreeOmega MN (ptree E MN R))
    (Hcut : forall t, @finite_internal E MN (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure R t (cut t)) t :
  exists joint, @semantic_coupling (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    (stable_head E MN R) (stable_head E MN R) eq
    (FOLub (fun n => finite_internal_rounds cut n t))
    (FOLub (fun n => @ptree_hitting_approx E MN (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega R n (observe t))) joint.
Proof.
  eexists. apply free_omega_qlift_eq_realization.
  exact (finite_internal_acceleration Hcut t).
Qed.

Section PolicyCoinduction.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}.
Context {A B : Type} (RR : A -> B -> Prop).
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Variable sim : ptree E MN A -> ptree E MN B -> Prop.
Variable cut1 : ptree E MN A -> MF (ptree E MN A).
Variable cut2 : ptree E MN B -> MF (ptree E MN B).
Hypothesis cut1_valid : forall t,
  @finite_internal E MN MF FI FreeOmegaMixedMeasure A t (cut1 t).
Hypothesis cut2_valid : forall t,
  @finite_internal E MN MF FI FreeOmegaMixedMeasure B t (cut2 t).
Hypothesis cuts_coupled : forall t1 t2, sim t1 t2 ->
  free_omega_qlift (pfinite_guard RR sim) (cut1 t1) (cut2 t2).

(** A sound guarded coinduction rule allowing internal progress forever,
    not merely between visible events.  The marginal policies are explicit:
    this does not silently assert that arbitrary pair-dependent witnesses
    in the residual GFP can be uniformized. *)
Theorem peutt_coinduction_finite_internal_policies t1 t2 :
  sim t1 t2 ->
  @peutt E MN MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A B RR t1 t2.
Proof.
  intro Hsim.
  eapply peutt_coinduction with
    (sim := fun s1 s2 => exists u v,
      s1 = observe u /\ s2 = observe v /\ sim u v).
  - intros s1 s2 [u [v [-> [-> Huv]]]].
    eapply stable_hitting_match_of_hitting_lift with
      (out1 := FOLub (fun n => @ptree_hitting_approx E MN MF FI
        FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A n (observe u)))
      (out2 := FOLub (fun n => @ptree_hitting_approx E MN MF FI
        FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega B n (observe v))).
    + apply free_omega_qlift_refl. intro h. reflexivity.
    + apply free_omega_qlift_refl. intro h. reflexivity.
    + eapply FOQLMono with (T := stable_head_rel RR sim).
      * eapply FOQLComp with (T := eq) (U := stable_head_rel RR sim)
          (mid := FOLub (fun n => finite_internal_rounds cut1 n u)).
        -- apply FOQLSym. eapply FOQLMono.
           ++ exact (finite_internal_acceleration cut1_valid u).
           ++ intros x y ->. reflexivity.
        -- eapply FOQLComp with (T := stable_head_rel RR sim) (U := eq)
             (mid := FOLub (fun n => finite_internal_rounds cut2 n v)).
           ++ exact (finite_internal_round_limits_coupled cuts_coupled Huv).
           ++ exact (finite_internal_acceleration cut2_valid v).
           ++ intros x z [y [Hxy ->]]. exact Hxy.
        -- intros x z [y [-> Hyz]]. exact Hyz.
      * intros h1 h2 Hhead. dependent destruction Hhead.
        -- constructor. exact H.
        -- constructor. intro x. exists (k1 x), (k2 x).
           repeat split; try reflexivity. exact (H x).
  - exists t1, t2. repeat split; try reflexivity. exact Hsim.
Qed.

End PolicyCoinduction.
