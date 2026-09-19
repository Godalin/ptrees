Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Relations.Relation_Operators.
From mathcomp Require Import ssreflect reals.
From mathcomp.reals_stdlib Require Import Rstruct.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum
  SemanticCoupling SemanticCouplingEnum FreeOmegaMeasure FreeOmegaNative
  FreeOmegaNativeTransportSubEnum.
From PTree.Eq Require Import PFiniteResidual FiniteInternalPlan PEutt.
From PTree.Eq.FreeOmega Require Import FiniteInternalNative FiniteInternalRoundCoupling
  FiniteInternalNativeJoint FiniteInternalJointRows.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The scalar model supplies an actual native transport, so the candidate
    may now be arbitrary and heterogeneous.  Coq's standard reals instantiate
    the audit model internally; the caller supplies no numerical model,
    equivalence proof, or measure-level gluing axiom. *)
Section ResidualTransport.
Local Notation F := (@Real.Pack Rdefinitions.R (Real.on Rdefinitions.R)).
Context {E : Type -> Type} {A B : Type}.
Variable RR : A -> B -> Prop.
Variable sim : ptree E SubEnum A -> ptree E SubEnum B -> Prop.
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).

Theorem pfinite_subenum_joint_round t u :
  @pfinite_residualF E SubEnum MF SubEnum_SemanticMeasure FI
    FreeOmegaMixedMeasure A B RR sim t u ->
  inhabited (@finite_internal_joint_row E SubEnum SubEnum_SemanticMeasure
    SubEnum_SemanticOmega A B RR sim t u).
Proof.
  intro Hstep. apply pfinite_residual_native_characterization in Hstep.
  destruct Hstep as [p [q Hdecoded]].
  destruct (subenum_native_quotient_coupling F Hdecoded) as [joint [Hl [Hr Hguard]]].
  have Hql : free_omega_qlift (fun z x => fst z = x)
    (FOSample joint FORet : FreeOmegaAt SubEnum (ptree E SubEnum A * ptree E SubEnum B) _)
    (FOSample (native_sample_measure (internal_plan_native p)) FORet).
  { eapply FOQLSample; [exact Hl|]. intros z x Hz. apply FOQLStructural, FOLRet. exact Hz. }
  have Hqr : free_omega_qlift (fun z y => snd z = y)
    (FOSample joint FORet : FreeOmegaAt SubEnum (ptree E SubEnum A * ptree E SubEnum B) _)
    (FOSample (native_sample_measure (internal_plan_native q)) FORet).
  { eapply FOQLSample; [exact Hr|]. intros z y Hz. apply FOQLStructural, FOLRet. exact Hz. }
  destruct (finite_internal_native_joint_round (@subenum_coupling_realization) Hql Hqr Hguard)
    as [W [round [left [right [Hleft [Hright Hrelated]]]]]].
  constructor. exact {|
    joint_row_left_plan := p;
    joint_row_right_plan := q;
    joint_row_sample := W;
    joint_row_measure := round;
    joint_row_left := left;
    joint_row_right := right;
    joint_row_left_marginal := Hleft;
    joint_row_right_marginal := Hright;
    joint_row_related := Hrelated
  |}.
Qed.

Theorem peutt_coinduction_residual_subenum
    (postfixed : forall t u, sim t u ->
      @pfinite_residualF E SubEnum MF SubEnum_SemanticMeasure FI
        FreeOmegaMixedMeasure A B RR sim t u) t u :
  sim t u -> @peutt E SubEnum MF FI
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A B RR t u.
Proof.
  apply peutt_coinduction_joint_rows with (sim := sim).
  intros x y Hxy. apply pfinite_subenum_joint_round. exact (postfixed x y Hxy).
Qed.
End ResidualTransport.

Corollary pfinite_residual_rel_peutt_subenum
    {E : Type -> Type} {A B : Type} (RR : A -> B -> Prop) t u :
  @pfinite_residual_rel E SubEnum (FreeOmega SubEnum)
    SubEnum_SemanticMeasure SubEnum_SemanticMeasureCoreLaws
    (FreeOmegaObservableSemanticMeasure (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure A B RR t u ->
  @peutt E SubEnum (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A B RR t u.
Proof.
  apply peutt_coinduction_residual_subenum.
  intros x y Hxy. apply pfinite_residual_unfold. exact Hxy.
Qed.

(** Finite equational chaining remains sound without assuming that the
    raw greatest fixed point is transitive or using an up-to-closure rule. *)
Corollary pfinite_residual_peutt_subenum
    {E : Type -> Type} {A : Type} (t u : ptree E SubEnum A) :
  @pfinite_residual E SubEnum (FreeOmega SubEnum)
    SubEnum_SemanticMeasure SubEnum_SemanticMeasureCoreLaws
    (FreeOmegaObservableSemanticMeasure (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure A t u ->
  @peutt E SubEnum (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A A eq t u.
Proof.
  intro H. induction H.
  - apply pfinite_residual_rel_peutt_subenum. exact H.
  - apply peutt_refl.
  - apply peutt_sym. exact IHclos_refl_sym_trans.
  - eapply peutt_trans; eassumption.
Qed.
