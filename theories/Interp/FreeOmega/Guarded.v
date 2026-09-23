(** Role: Interpreter compositionality. Depends on equational theory (and comparison semantics for Atomic/MDP); not primitive syntax. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From PTree.Eq Require Import StableHittingRelation.
From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Eq.FreeOmega Require Import Base Relation Bind.
From PTree.Interp.FreeOmega Require Import Base.
From PTree.Interp Require Export Guarded.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Canonical completion specializations of the generic guarded theory.
    These keep the established native capability contract; no proof is copied. *)
Section GuardedInterp.
Context {E F MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI} `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NC := NC) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Variable handler : forall X, E X -> ptree F MN X.

Definition guarded_handler : Prop :=
  @Guarded.guarded_handler E F MN MF FI FreeOmegaMixedMeasure FO handler.

Context `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.

(** A convenient complete witness suffices; the public contract holds for
    every representative, by uniqueness and coupling support transport. *)
Lemma guarded_handler_of_hitting
    (H : forall X (e : E X), exists out,
      @ptree_stable_hitting F MN MF FI FreeOmegaMixedMeasure FO X
        (observe (handler e)) out /\
      @sem_ae MF FI _ out stable_head_is_visible) : guarded_handler.
Proof. apply Guarded.guarded_handler_of_hitting. exact H. Qed.

Theorem guarded_handler_vis_fusion {A B} (RR : A -> B -> Prop)
    (Hguard : guarded_handler) :
  interp_vis_fusion (NI := NI) (NO := NO) RR handler.
Proof. apply Guarded.guarded_handler_vis_fusion. exact Hguard. Qed.

Theorem peutt_interp_guarded {A B} (RR : A -> B -> Prop)
    (Hguard : guarded_handler) (t1 : ptree E MN A) (t2 : ptree E MN B) :
  @peutt E MN MF FI FC FreeOmegaMixedMeasure FO A B RR t1 t2 ->
  @peutt F MN MF FI FC FreeOmegaMixedMeasure FO A B RR
    (PTree.interp handler t1) (PTree.interp handler t2).
Proof. apply Guarded.peutt_interp_guarded. exact Hguard. Qed.

(** Guardedness is an explicit local premise, not a globally synthesized
    typeclass obligation or an assumption on every effect handler. *)
Lemma peutt_interp_guarded_Proper {R} (Hguard : guarded_handler) :
  Proper (@peutt E MN MF FI FC FreeOmegaMixedMeasure FO R R eq ==>
          @peutt F MN MF FI FC FreeOmegaMixedMeasure FO R R eq)
    (@PTree.interp E F MN handler R).
Proof. intros t u Htu. exact (peutt_interp_guarded Hguard Htu). Qed.
End GuardedInterp.
