(** Thin specializations: all source-eutt and source-interpreter proofs are
    generic. The completion supplies only the probability certificates. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ITree.Core Require Import ITreeDefinition.
From ITree.Eq Require Import Eqit.
From ITree.Interp Require Import Interp.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Handler ITreeBridge.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure BindOrder RelationalLimit.
From PTree.Eq Require Import PEutt.
From PTree.Interp Require Import ITreeEutt ITreePreservation.
Set Implicit Arguments.
Unset Strict Implicit.

Section Completion.
Context {MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

Theorem free_omega_from_itree_eutt {E A B} (RR : A -> B -> Prop)
    (t : itree E A) (u : itree E B) :
  eutt RR t u -> peutt (FI := FI) RR (@from_itree E MN A t) (from_itree u).
Proof. apply (from_itree_eutt free_omega_relational_zero). Qed.

Theorem free_omega_interp_itree_eutt {E F A B} (h : Handler MN E F)
    (RR : A -> B -> Prop) (t : itree E A) (u : itree E B) :
  eutt RR t u -> peutt (FI := FI) RR (interp_itree h t) (interp_itree h u).
Proof. apply (interp_itree_eutt free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_elaborate_eutt {E A B} (RR : A -> B -> Prop)
    (t : itree (probE MN +' E) A) (u : itree (probE MN +' E) B) :
  eutt RR t u -> peutt (FI := FI) RR (elaborate t) (elaborate u).
Proof. apply free_omega_interp_itree_eutt. Qed.

Theorem free_omega_elaborate_closed_eutt {A B} (RR : A -> B -> Prop)
    (t : itree (probE MN) A) (u : itree (probE MN) B) :
  eutt RR t u -> peutt (FI := FI) RR (elaborate_closed t) (elaborate_closed u).
Proof. apply free_omega_interp_itree_eutt. Qed.

Theorem free_omega_from_itree_interp {E F A}
    (h : forall X, E X -> itree F X) (t : itree E A) :
  peutt (FI := FI) eq (from_itree (Interp.interp h t))
    (PTree.interp (fun X e => @from_itree F MN X (h X e)) (from_itree t)).
Proof.
  apply (from_itree_interp free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_interp_itree_source_interp {E F G A}
    (h : forall X, E X -> itree F X) (g : Handler MN F G) (t : itree E A) :
  peutt (FI := FI) eq (interp_itree g (Interp.interp h t))
    (interp_itree (fun X e => interp_itree g (h X e)) t).
Proof.
  apply (interp_itree_source_interp free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.
End Completion.
