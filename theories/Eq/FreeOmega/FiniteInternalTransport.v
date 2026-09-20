Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Relations.Relation_Operators.
From mathcomp Require Import ssreflect.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure SemanticCoupling FreeOmegaMeasure
  FreeOmegaNative FreeOmegaNativeCoupling.
From PTree.Eq Require Import PFinite FiniteInternalPlan PEutt.
From PTree.Eq.FreeOmega Require Import FiniteInternalNative FiniteInternalRoundCoupling
  FiniteInternalNativeJoint FiniteInternalJointRows.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Backend-generic residual soundness.  Realizing quotient couplings of
    native presentations is an explicit measure capability, not an
    assumption that the recursive candidate is already behaviorally sound. *)
Section ResidualTransport.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
  `{NJ : @FreeOmegaNativeCouplingLaws MN NI NO}.
Context {A B : Type}.
Variable RR : A -> B -> Prop.
Variable sim : ptree E MN A -> ptree E MN B -> Prop.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

Theorem pfinite_joint_round t u :
  @pfiniteF E MN MF NI FI FreeOmegaMixedMeasure A B RR sim t u ->
  inhabited (@finite_internal_joint_row E MN NI NO A B RR sim t u).
Proof.
  intro Hstep. apply pfinite_native_characterization in Hstep.
  destruct Hstep as [p [q Hdecoded]].
  destruct (free_omega_native_coupling Hdecoded) as [joint [Hl [Hr Hguard]]].
  have Hql : free_omega_qlift (fun z x => fst z = x)
    (FOSample joint FORet : FreeOmegaAt MN (ptree E MN A * ptree E MN B) _)
    (FOSample (native_sample_measure (internal_plan_native p)) FORet).
  { eapply FOQLSample; [exact Hl|]. intros z x Hz. apply FOQLStructural, FOLRet. exact Hz. }
  have Hqr : free_omega_qlift (fun z y => snd z = y)
    (FOSample joint FORet : FreeOmegaAt MN (ptree E MN A * ptree E MN B) _)
    (FOSample (native_sample_measure (internal_plan_native q)) FORet).
  { eapply FOQLSample; [exact Hr|]. intros z y Hz. apply FOQLStructural, FOLRet. exact Hz. }
  destruct (finite_internal_native_joint_round
    (@free_omega_native_node_coupling MN NI NO NJ) Hql Hqr Hguard)
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

Theorem peutt_coinduction_residual
    (postfixed : forall t u, sim t u ->
      @pfiniteF E MN MF NI FI FreeOmegaMixedMeasure A B RR sim t u) t u :
  sim t u -> @peutt E MN MF FI
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A B RR t u.
Proof.
  apply peutt_coinduction_joint_rows with (sim := sim).
  intros x y Hxy. apply pfinite_joint_round. exact (postfixed x y Hxy).
Qed.
End ResidualTransport.

Section ResidualSoundness.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
  `{NJ : @FreeOmegaNativeCouplingLaws MN NI NO}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

Corollary peutt_of_pfinite_rel {A B} (RR : A -> B -> Prop) t u :
  @pfinite_rel E MN MF NI NC FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure A B RR t u ->
  @peutt E MN MF FI FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A B RR t u.
Proof.
  apply peutt_coinduction_residual.
  intros x y Hxy. apply pfinite_rel_unfold. exact Hxy.
Qed.

Corollary peutt_of_pfinite {A} (t u : ptree E MN A) :
  @pfinite E MN MF NI NC FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure A t u ->
  @peutt E MN MF FI FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A A eq t u.
Proof.
  intro H. induction H.
  - apply peutt_of_pfinite_rel. exact H.
  - apply peutt_refl.
  - apply peutt_sym. exact IHclos_refl_sym_trans.
  - eapply peutt_trans; eassumption.
Qed.
End ResidualSoundness.
