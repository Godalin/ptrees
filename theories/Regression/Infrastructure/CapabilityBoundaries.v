(** Compile-time capability boundaries, not new public theory.
    These Sections intentionally provide no native AELift instance. *)
Set Warnings "-notation-overridden".
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Eq Require Import PStruct PEutt PTreeKernel.
From PTree.Eq.FreeOmega Require Import Base Relation Bind Iter.
From PTree.Interp.FreeOmega Require Import Base Cofinality Guarded MDP.
From PTree.Semantics Require Import MDPFragment.
Set Implicit Arguments.

Section DefinitionalBridge.
Context {E MN MF : Type -> Type} `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.
(** No native measure interface, bind laws, or omega laws are supplied. *)
Example complete_bridge_without_laws {R} (ot : ptree' E MN R) out :
  PTree.Eq.PrimitiveStableHitting.stable_hitting (FI := FI) (FO := FO)
    (@ptree_primitive_kernel E MN MF FI MX R) ot out <->
  ptree_stable_hitting (MF := MF) ot out.
Proof. apply ptree_primitive_stable_hitting_adequate. Qed.
End DefinitionalBridge.

Section StructuralCapabilities.
Context {E F MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NC := NC) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).

(** Genuine Gate C weakening: arbitrary structural interpretation needs
    neither native AELift nor CouplingAE/CountableAE. *)
Example structural_interp_without_ae {A B} (RR : A -> B -> Prop)
    (handler : forall X, E X -> ptree F MN X)
    (t : ptree E MN A) (u : ptree E MN B) :
  pstruct RR t u ->
  @peutt F MN MF FI FC FreeOmegaMixedMeasure FO A B RR
    (PTree.interp handler t) (PTree.interp handler u).
Proof. apply peutt_interp_structural. Qed.

Example structural_translate_without_ae {A B} (RR : A -> B -> Prop)
    (rename : forall X, E X -> F X)
    (t : ptree E MN A) (u : ptree E MN B) :
  pstruct RR t u ->
  @peutt F MN MF FI FC FreeOmegaMixedMeasure FO A B RR
    (PTree.translate rename t) (PTree.translate rename u).
Proof. apply peutt_translate_structural. Qed.

Example behavioral_translate_without_ae {A B} (RR : A -> B -> Prop)
    (rename : forall X, E X -> F X)
    (t : ptree E MN A) (u : ptree E MN B) :
  @peutt E MN MF FI FC FreeOmegaMixedMeasure FO A B RR t u ->
  @peutt F MN MF FI FC FreeOmegaMixedMeasure FO A B RR
    (PTree.translate rename t) (PTree.translate rename u).
Proof. apply PTree.Interp.FreeOmega.Translate.peutt_translate. Qed.

(** Scheduling and fragment preservation already had these weaker types
    before Gate C. Removing source-only Context is not a new theorem. *)
Example interp_cofinal_without_ae {R}
    (handler : forall X, E X -> ptree F MN X) (t : ptree E MN R) :
  @PTree.Interp.Kernel.ptree_interp_cofinal E F MN MF FI
    FreeOmegaMixedMeasure FO R handler t.
Proof. apply ptree_interp_cofinal_all. Qed.

Context `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.
Example mdp_interp_without_aelift {R}
    (handler : forall X, E X -> ptree F MN X)
    (Hhandler : mdp_handler (R := R) handler) (t : ptree E MN R) :
  @mdp_state E MN MF FI FC FreeOmegaMixedMeasure FO R t ->
  @mdp_state F MN MF FI FC FreeOmegaMixedMeasure FO R (PTree.interp handler t).
Proof. apply mdp_state_interp. exact Hhandler. Qed.
End StructuralCapabilities.
