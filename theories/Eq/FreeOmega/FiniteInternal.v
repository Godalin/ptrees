Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Arith.PeanoNat Logic.ClassicalChoice Lia.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import
  FiniteInternal UnifiedFrontier PrimitiveStableHitting PTreeKernel
  PStrong PFiniteResidual.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FreeOmegaFiniteInternal.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmega MN NI} {R : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation execute :=
  (@finite_internal E MN MF FI FreeOmegaMixedMeasure R).
Local Notation hit := (@ptree_hitting_approx E MN MF FI
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega R).

(** A compression cannot hide an observation already reached in n primitive
    steps.  The right-hand side may reveal more behavior, since those n
    steps start only after the well-founded compression.  The index is used
    for the soundness proof, not as a bound on [finite_internal]. *)
Theorem finite_internal_hitting_covered t out :
  execute t out -> forall n,
  free_omega_approx eq (hit n (observe t))
    (free_omega_bind out (fun u => hit n (observe u))).
Proof.
  intro Hexec. induction Hexec; intro n.
  - cbn. apply free_omega_approx_refl. intro h. reflexivity.
  - destruct n as [|n].
    + apply FOApproxZero.
    + change (free_omega_approx eq (hit n (observe t))
        (free_omega_bind out (fun u => hit (S n) (observe u)))).
      eapply free_omega_approx_trans; [|apply IHHexec].
      exact (@PTreeKernel.ptree_hitting_mono E MN MF FI
        FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
        FreeOmegaObservableSemanticMeasureOrderLaws R (observe t)
        n (S n) (Nat.le_succ_diag_r n)).
  - destruct n as [|n].
    + change (free_omega_approx eq (FOSample mu (fun _ => FOZero))
        (FOSample mu (fun x => free_omega_bind (out x)
          (fun u => hit 0 (observe u))))).
      eapply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intro x. reflexivity.
      * intros x y ->. apply FOApproxZero.
    + change (free_omega_approx eq (FOSample mu (fun x => hit n (observe (k x))))
        (FOSample mu (fun x => free_omega_bind (out x)
          (fun u => hit (S n) (observe u))))).
      eapply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intro x. reflexivity.
      * intros x y ->. eapply free_omega_approx_trans; [|apply H0].
        exact (@PTreeKernel.ptree_hitting_mono E MN MF FI
          FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
          FreeOmegaObservableSemanticMeasureOrderLaws R (observe (k y))
          n (S n) (Nat.le_succ_diag_r n)).
Qed.

(** Uniform truncations of a well-founded cut, not a uniform bound on the
    cut itself.  They recover its full residual distribution only at omega.
    Both inequalities are raw approximation statements, so later cofinality
    arguments do not need an unjustified order/properness law for qlift. *)
Definition finite_internal_approximates t out
    (chain : nat -> MF (ptree E MN R)) : Prop :=
  (forall n, free_omega_approx eq (chain n) (chain (S n))) /\
  free_omega_qlift eq out (FOLub chain) /\
  (forall n m, free_omega_approx eq
    (free_omega_bind (chain n) (fun u => hit m (observe u)))
    (hit (n + m) (observe t))) /\
  (forall n, free_omega_approx eq (hit n (observe t))
    (free_omega_bind (chain n) (fun u => hit n (observe u)))).

Lemma finite_internal_prefix_limit {A} (out : MF A) (chain : nat -> MF A) :
  free_omega_qlift eq out (FOLub chain) ->
  free_omega_qlift eq out
    (FOLub (fun n => match n with O => FOZero | S m => chain m end)).
Proof.
  intro Hlimit. eapply FOQLComp with (T := eq) (U := eq).
  - exact Hlimit.
  - apply FOQLLubZeroPrefixR. intro n.
    apply free_omega_qlift_refl. intro x. reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

Theorem finite_internal_approximation_exists t out :
  execute t out -> exists chain, finite_internal_approximates t out chain.
Proof.
  intro Hexec. induction Hexec.
  - exists (fun _ => FORet t). repeat split.
    + intro n. apply free_omega_approx_refl. intro x. reflexivity.
    + apply FOQLLubConstantR. apply free_omega_qlift_refl.
      intro x. reflexivity.
    + intros n m. change (free_omega_approx eq
        (hit m (observe t)) (hit (n + m) (observe t))).
      apply (@PTreeKernel.ptree_hitting_mono E MN MF FI
        FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
        FreeOmegaObservableSemanticMeasureOrderLaws R). lia.
    + intro n. apply free_omega_approx_refl. intro x. reflexivity.
  - destruct IHHexec as [chain [Hinc [Hlimit [Hupper Hcover]]]].
    exists (fun n => match n with O => FOZero | S m => chain m end).
    repeat split.
    + intros [|n]; [apply FOApproxZero|apply Hinc].
    + apply finite_internal_prefix_limit. exact Hlimit.
    + intros [|n] m; [apply FOApproxZero|]. exact (Hupper n m).
    + intros [|n]; [apply FOApproxZero|].
      eapply free_omega_approx_trans; [exact (Hcover n)|].
      eapply free_omega_approx_bind with (R := eq).
      * apply free_omega_approx_refl. intro x. reflexivity.
      * intros x y ->.
        exact (@PTreeKernel.ptree_hitting_mono E MN MF FI
          FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
          FreeOmegaObservableSemanticMeasureOrderLaws R (observe y)
          n (S n) (Nat.le_succ_diag_r n)).
  - destruct (choice _ H0) as [chains Hchains].
    exists (fun n => FOSample mu (fun x =>
      match n with O => FOZero | S m => chains x m end)).
    repeat split.
    + intros [|n]; eapply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intro x. reflexivity.
      * intros x y ->. apply FOApproxZero.
      * apply sem_lift_refl. intro x. reflexivity.
      * intros x y ->. exact (proj1 (Hchains y) n).
    + apply FOQLSampleLub with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros x _. apply finite_internal_prefix_limit.
        exact (proj1 (proj2 (Hchains x))).
    + intros [|n] m.
      * destruct m as [|m].
        -- apply free_omega_approx_refl. intro x. reflexivity.
        -- change (free_omega_approx eq
             (FOSample mu (fun _ => FOZero))
             (FOSample mu (fun x => hit m (observe (k x))))).
           eapply FOApproxSample with (S := eq).
           ++ apply sem_lift_refl. intro x. reflexivity.
           ++ intros x y ->. apply FOApproxZero.
      * eapply FOApproxSample with (S := eq).
        -- apply sem_lift_refl. intro x. reflexivity.
        -- intros x y ->. exact (proj1 (proj2 (proj2 (Hchains y))) n m).
    + intros [|n].
      * apply free_omega_approx_refl. intro x. reflexivity.
      * eapply FOApproxSample with (S := eq).
        -- apply sem_lift_refl. intro x. reflexivity.
        -- intros x y ->. eapply free_omega_approx_trans.
           ++ exact (proj2 (proj2 (proj2 (Hchains y))) n).
           ++ eapply free_omega_approx_bind with (R := eq).
              ** apply free_omega_approx_refl. intro z. reflexivity.
              ** intros u v ->.
                 exact (@PTreeKernel.ptree_hitting_mono E MN MF FI
                   FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
                   FreeOmegaObservableSemanticMeasureOrderLaws R (observe v)
                   n (S n) (Nat.le_succ_diag_r n)).
Qed.

(** A selected compression policy, followed by one genuine primitive step.
    The policy may vary with the whole residual tree and its derivations
    need not admit a uniform depth bound.  This is proof machinery for
    acceleration, not a new definition of the finite relation. *)
Variable cut : ptree E MN R -> MF (ptree E MN R).
Hypothesis cut_valid : forall t, execute t (cut t).

Definition finite_internal_advance
    (next : ptree E MN R -> MF (stable_head E MN R))
    (t : ptree E MN R) : MF (stable_head E MN R) :=
  match observe t with
  | RetF r => FORet (FHRet r)
  | VisF _ e k => FORet (FHVis e k)
  | TauF u => next u
  | ProbF _ mu k => FOSample mu (fun x => next (k x))
  end.

Fixpoint finite_internal_rounds (n : nat) (t : ptree E MN R) :
    MF (stable_head E MN R) :=
  free_omega_bind (cut t)
    (finite_internal_advance
      (match n with
       | O => fun _ => FOZero
       | S m => finite_internal_rounds m
       end)).

Lemma finite_internal_advance_mono next1 next2 :
  (forall t, free_omega_approx eq (next1 t) (next2 t)) ->
  forall t, free_omega_approx eq
    (finite_internal_advance next1 t) (finite_internal_advance next2 t).
Proof.
  intros Hnext t. unfold finite_internal_advance. destruct (observe t).
  - apply FOApproxRet. reflexivity.
  - apply Hnext.
  - apply FOApproxRet. reflexivity.
  - eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. apply Hnext.
Qed.

Lemma finite_internal_rounds_increasing n t :
  free_omega_approx eq
    (finite_internal_rounds n t) (finite_internal_rounds (S n) t).
Proof.
  induction n as [|n IH] in t |- *; cbn [finite_internal_rounds];
    eapply free_omega_approx_bind with (R := eq).
  all: try (apply free_omega_approx_refl; intro x; reflexivity).
  - intros x y ->. apply finite_internal_advance_mono.
    intro u. apply FOApproxZero.
  - intros x y ->. apply finite_internal_advance_mono. exact IH.
Qed.

(** After n+1 guarded rounds, every observation reachable in n internal
    primitive steps has been covered.  Unlike a one-round preservation
    lemma, this gives progress through arbitrarily many internal rounds.
    It is only the lower-coverage half of acceleration adequacy: equality
    of the two complete limits still requires the converse direction. *)
Theorem finite_internal_rounds_cover_hitting n t :
  free_omega_approx eq (hit n (observe t)) (finite_internal_rounds n t).
Proof.
  induction n as [|n IH] in t |- *.
  - eapply free_omega_approx_trans.
    + exact (finite_internal_hitting_covered (cut_valid t) 0).
    + change (free_omega_approx eq
        (free_omega_bind (cut t) (fun u => hit 0 (observe u)))
        (free_omega_bind (cut t)
          (finite_internal_advance (fun _ => FOZero)))).
      eapply free_omega_approx_bind with (R := eq).
      * apply free_omega_approx_refl. intro x. reflexivity.
      * intros x y ->. unfold finite_internal_advance.
        destruct (observe y); apply free_omega_approx_refl;
          intro h; reflexivity.
  - eapply free_omega_approx_trans.
    + exact (finite_internal_hitting_covered (cut_valid t) (S n)).
    + change (free_omega_approx eq
        (free_omega_bind (cut t) (fun u => hit (S n) (observe u)))
        (free_omega_bind (cut t)
          (finite_internal_advance (finite_internal_rounds n)))).
      eapply free_omega_approx_bind with (R := eq).
      * apply free_omega_approx_refl. intro x. reflexivity.
      * intros x y ->. unfold finite_internal_advance.
        destruct (observe y).
        -- apply FOApproxRet. reflexivity.
        -- apply IH.
        -- apply FOApproxRet. reflexivity.
        -- eapply FOApproxSample with (S := eq).
           ++ apply sem_lift_refl. intro x. reflexivity.
           ++ intros x z ->. apply IH.
Qed.

End FreeOmegaFiniteInternal.

Section CoupledInternalRounds.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NO : @SemanticOmega MN NI}.
Context {A B : Type} (RR : A -> B -> Prop).
Variable sim : ptree E MN A -> ptree E MN B -> Prop.
Variable cut1 : ptree E MN A -> FreeOmega MN (ptree E MN A).
Variable cut2 : ptree E MN B -> FreeOmega MN (ptree E MN B).

(** Here the cuts are independently chosen functions of each marginal
    state.  This hypothesis must not be inferred just by choosing witnesses
    in [pfinite_residual_unfold]: those witnesses may depend on the pair. *)
Hypothesis cuts_coupled : forall t1 t2, sim t1 t2 ->
  free_omega_qlift (pfinite_guard RR sim) (cut1 t1) (cut2 t2).

Lemma finite_internal_advance_coupled next1 next2 :
  (forall t1 t2, sim t1 t2 ->
    free_omega_qlift (stable_head_rel RR sim) (next1 t1) (next2 t2)) ->
  forall t1 t2, pfinite_guard RR sim t1 t2 ->
    free_omega_qlift (stable_head_rel RR sim)
      (finite_internal_advance next1 t1)
      (finite_internal_advance next2 t2).
Proof.
  intros Hnext t1 t2 Hguard.
  unfold finite_internal_advance, pfinite_guard in *.
  remember (observe t1) as o1 in Hguard |- *.
  remember (observe t2) as o2 in Hguard |- *.
  destruct Hguard.
  - apply FOQLStructural. apply FOLRet. constructor. exact H.
  - apply Hnext. exact H.
  - apply FOQLStructural. apply FOLRet. constructor. exact H.
  - eapply FOQLSample; [exact H|].
    intros x y Hxy. apply Hnext. exact Hxy.
Qed.

(** An actual coupling of complete accelerated chains, not merely the
    implication F(peutt) <= peutt.  It does not yet identify either chain
    with its original primitive hitting limit. *)
Theorem finite_internal_rounds_coupled n t1 t2 :
  sim t1 t2 -> free_omega_qlift (stable_head_rel RR sim)
    (finite_internal_rounds cut1 n t1)
    (finite_internal_rounds cut2 n t2).
Proof.
  induction n as [|n IH] in t1, t2 |- *; intro Hsim;
    cbn [finite_internal_rounds]; eapply FOQLBind.
  all: try (apply cuts_coupled; exact Hsim).
  - intros u v Huv. eapply finite_internal_advance_coupled; [|exact Huv].
    intros x y Hxy. apply FOQLStructural. apply FOLZero.
  - intros u v Huv. eapply finite_internal_advance_coupled; [|exact Huv].
    exact IH.
Qed.

Corollary finite_internal_round_limits_coupled t1 t2 :
  sim t1 t2 -> free_omega_qlift (stable_head_rel RR sim)
    (FOLub (fun n => finite_internal_rounds cut1 n t1))
    (FOLub (fun n => finite_internal_rounds cut2 n t2)).
Proof.
  intro Hsim. apply FOQLLub. intro n.
  apply finite_internal_rounds_coupled. exact Hsim.
Qed.

End CoupledInternalRounds.
