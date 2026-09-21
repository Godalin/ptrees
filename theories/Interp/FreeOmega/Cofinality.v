(** Role: Interpreter compositionality. Depends on equational theory (and comparison semantics for Atomic/MDP); not primitive syntax. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq.Arith Require Import PeanoNat.
Require Import Lia.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Eq Require Import Shallow UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Eq.FreeOmega Require Import Base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From PTree.Eq.FreeOmega Require Import Bind.
Require Import PTree.Interp.Kernel.
Section FreeOmegaInterpCofinality.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).

Section InterpCofinality.
Context {F : Type -> Type}.
Variable handler : forall X, E X -> ptree F MN X.

Definition ptree_interp_approx_cofinal {R}
    (t : ptree E MN R) : Prop :=
  free_omega_chains_cofinal eq
    (fun fuel => ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.interp handler t)))
    (fun fuel => ptree_interp_diagonal_approx fuel handler t).

Lemma ptree_interp_hitting_le_diagonal {R}
    (fuel : nat) (t : ptree E MN R) :
  free_omega_approx eq
    (ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.interp handler t)))
    (ptree_interp_diagonal_approx fuel handler t).
Proof.
  revert t. induction fuel as [|fuel IH]; intro t.
  all: unfold ptree_interp_diagonal_approx;
    rewrite observe_interp; remember (observe t) as ot eqn:Hot;
    destruct ot as [r|u|X e k|X mu k].
  - cbn [ptree_hitting_approx ptree_primitive_kernel
      ptree_interp_head_approx ptree_interp_head_tree
      free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - constructor.
  - constructor.
  - change (free_omega_approx eq
      (FOSample mu (fun _ : X => FOZero))
      (free_omega_bind (FOSample mu (fun _ : X => FOZero))
        (ptree_interp_head_approx (MF := MF) (R := R) 0 handler))).
    cbn [free_omega_bind]. eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. constructor.
  - cbn [ptree_hitting_approx ptree_primitive_kernel
      ptree_interp_head_approx ptree_interp_head_tree
      free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - cbn [ptree_hitting_approx ptree_primitive_kernel].
    eapply free_omega_approx_trans; [apply IH|].
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply free_omega_approx_refl. intro h. reflexivity.
    + intros h1 h2 ->. apply ptree_hitting_mono. lia.
  - cbn [ptree_hitting_approx ptree_primitive_kernel
      ptree_interp_head_approx free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - change (free_omega_approx eq
      (FOSample mu (fun x => ptree_hitting_approx (MF := MF)
        fuel (observe (PTree.interp handler (k x)))))
      (free_omega_bind
        (FOSample mu (fun x => ptree_hitting_approx (MF := MF)
          fuel (observe (k x))))
        (ptree_interp_head_approx (MF := MF) (R := R)
          (S fuel) handler))).
    cbn [free_omega_bind]. eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. eapply free_omega_approx_trans; [apply IH|].
      eapply free_omega_approx_bind with (R := eq) (T := eq).
      * apply free_omega_approx_refl. intro h. reflexivity.
      * intros h1 h2 ->. apply ptree_hitting_mono. lia.
Qed.

Definition ptree_interp_split_approx {R}
    (source_fuel head_fuel : nat) (t : ptree E MN R) :
    MF (stable_head F MN R) :=
  free_omega_bind
    (ptree_hitting_approx (MF := MF) source_fuel (observe t))
    (ptree_interp_head_approx (MF := MF) (R := R)
      head_fuel handler).

Lemma ptree_interp_split_le_hitting {R}
    (source_fuel head_fuel : nat) (t : ptree E MN R) :
  free_omega_approx eq
    (ptree_interp_split_approx source_fuel head_fuel t)
    (ptree_hitting_approx (MF := MF) (source_fuel + head_fuel)
      (observe (PTree.interp handler t))).
Proof.
  revert t. induction source_fuel as [|source_fuel IH]; intro t.
  all: unfold ptree_interp_split_approx;
    rewrite observe_interp; remember (observe t) as ot eqn:Hot;
    destruct ot as [r|u|X e k|X mu k].
  - cbn [ptree_hitting_approx ptree_primitive_kernel
      ptree_interp_head_approx ptree_interp_head_tree
      free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - constructor.
  - cbn [free_omega_bind ptree_interp_head_approx
      ptree_interp_head_tree].
    apply free_omega_approx_refl. intro h. reflexivity.
  - change (free_omega_approx eq
      (free_omega_bind (FOSample mu (fun _ : X => FOZero))
        (ptree_interp_head_approx (MF := MF) (R := R)
          head_fuel handler))
      (ptree_hitting_approx (MF := MF) head_fuel
        (observe (Prob mu (fun x => PTree.interp handler (k x)))))).
    cbn [free_omega_bind ptree_hitting_approx ptree_primitive_kernel].
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. constructor.
  - unfold ptree_hitting_approx, ptree_primitive_kernel,
      ptree_interp_head_approx, ptree_interp_head_tree.
    cbn. rewrite !stable_target_stableE. cbn [free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - cbn [ptree_hitting_approx ptree_primitive_kernel]. apply IH.
  - cbn [free_omega_bind ptree_interp_head_approx
      ptree_interp_head_tree].
    apply ptree_hitting_mono. lia.
  - change (free_omega_approx eq
      (FOSample mu (fun x => ptree_interp_split_approx
        source_fuel head_fuel (k x)))
      (FOSample mu (fun x => ptree_hitting_approx (MF := MF)
        (source_fuel + head_fuel)
        (observe (PTree.interp handler (k x)))))).
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. apply IH.
Qed.

Lemma ptree_interp_diagonal_le_hitting {R}
    (fuel : nat) (t : ptree E MN R) :
  free_omega_approx eq
    (ptree_interp_diagonal_approx fuel handler t)
    (ptree_hitting_approx (MF := MF) (2 * fuel)
      (observe (PTree.interp handler t))).
Proof.
  change (free_omega_approx eq
    (ptree_interp_split_approx fuel fuel t)
    (ptree_hitting_approx (MF := MF) (2 * fuel)
      (observe (PTree.interp handler t)))).
  replace (2 * fuel) with (fuel + fuel) by lia.
  apply ptree_interp_split_le_hitting.
Qed.

Theorem ptree_interp_approx_cofinal_all {R}
    (t : ptree E MN R) : ptree_interp_approx_cofinal t.
Proof.
  split.
  - intro fuel. exists fuel.
    apply ptree_interp_hitting_le_diagonal.
  - intro fuel. exists (2 * fuel).
    eapply free_omega_approx_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + apply ptree_interp_diagonal_le_hitting.
Qed.

Corollary ptree_interp_cofinal_all {R}
    (t : ptree E MN R) :
  @PTree.Interp.Kernel.ptree_interp_cofinal E F MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R handler t.
Proof.
  intro out. unfold PTree.Interp.Kernel.ptree_interp_cofinal.
  apply free_omega_cofinal_lub_iff.
  - intro n. apply ptree_observable_hitting_increasing.
  - intro n. unfold ptree_interp_diagonal_approx.
    apply free_omega_approx_bind with (R := eq).
    + apply ptree_observable_hitting_increasing.
    + intros x y ->. unfold ptree_interp_head_approx.
      apply ptree_observable_hitting_increasing.
  - apply ptree_interp_approx_cofinal_all.
Qed.

End InterpCofinality.
End FreeOmegaInterpCofinality.
