(** Role: Interpreter compositionality. Depends on equational theory (and comparison semantics for Atomic/MDP); not primitive syntax. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq.Arith Require Import PeanoNat.
Require Import Lia.

From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import Shallow UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Eq.FreeOmega Require Import Base.

Set Implicit Arguments.
#[local] Existing Instance FreeOmegaSemanticMeasure.
#[local] Existing Instance FreeOmegaSemanticOmega.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From PTree.Eq.FreeOmega Require Import Bind.
Require Import PTree.Interp.Kernel.
Require PTree.Interp.Scheduling.
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
  exact (@Scheduling.ptree_interp_hitting_le_diagonal E F MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)) FreeOmegaMixedMeasure (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO))
    _ _ _ handler R fuel t).
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
  exact (@Scheduling.ptree_interp_split_le_hitting E F MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)) FreeOmegaMixedMeasure (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO))
    _ _ _ handler R source_fuel head_fuel t).
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
  exact (@Scheduling.ptree_interp_cofinal_all E F MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)) FreeOmegaMixedMeasure (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO))
    _ _ _ _ handler R t).
Qed.

End InterpCofinality.
End FreeOmegaInterpCofinality.
