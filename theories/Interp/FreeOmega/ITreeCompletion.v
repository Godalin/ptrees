(** Thin completion specializations of the generic ITree bridge laws. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms.
From ITree.Core Require Import ITreeDefinition.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Handler ITreeBridge.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure BindOrder RelationalLimit.
From PTree.Eq Require Import PEutt.
From PTree.Interp Require Import ITreeFacts.
Set Implicit Arguments.
Unset Strict Implicit.

Section Completion.
Context {MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Theorem free_omega_elab_ret {E F A} (h : Handler MN E F) (a : A) :
  peutt (FI := FI) eq (interp_itree h (ITreeDefinition.Ret a)) (Ret a).
Proof.
  apply (elab_ret free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_elab_tau {E F A} (h : Handler MN E F) (t : itree E A) :
  peutt (FI := FI) eq (interp_itree h (ITreeDefinition.Tau t)) (interp_itree h t).
Proof.
  apply (elab_tau free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_elab_event {E F A X} (h : Handler MN E F) (e : E X) (k : X -> itree E A) :
  peutt (FI := FI) eq (interp_itree h (ITreeDefinition.Vis e k))
    (PTree.bind (h X e) (fun x => interp_itree h (k x))).
Proof.
  apply (elab_event free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_elab_trigger {E F X} (h : Handler MN E F) (e : E X) :
  peutt (FI := FI) eq (interp_itree h (ITree.trigger e)) (h X e).
Proof.
  apply (elab_trigger free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_elab_sample {E A X} (mu : MN X) (k : X -> itree (probE MN +' E) A) :
  peutt (FI := FI) eq (elaborate (ITreeDefinition.Vis (inl1 (Sample mu)) k))
    (Prob mu (fun x => elaborate (k x))).
Proof.
  apply (elab_sample free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_elab_vis {E A X} (e : E X) (k : X -> itree (probE MN +' E) A) :
  peutt (FI := FI) eq (elaborate (ITreeDefinition.Vis (inr1 e) k))
    (Vis e (fun x => elaborate (k x))).
Proof.
  apply (elab_vis free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_elab_bind {E F A B} (h : Handler MN E F)
    (t : itree E A) (k : A -> itree E B) :
  peutt (FI := FI) eq (interp_itree h (ITree.bind t k))
    (PTree.bind (interp_itree h t) (fun x => interp_itree h (k x))).
Proof.
  apply (elab_bind free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_elab_iter {E F I A} (h : Handler MN E F)
    (step : I -> itree E (I+A)) i :
  peutt (FI := FI) eq (interp_itree h (ITree.iter step i))
    (PTree.iter (fun j => interp_itree h (step j)) i).
Proof.
  apply (elab_iter free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_elab_sample_trigger {X} (mu : MN X) :
  peutt (FI := FI) eq (elaborate_closed (ITree.trigger (Sample mu)))
    (Prob mu (fun x => Ret x)).
Proof.
  apply (elab_sample_trigger free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_elab_postcompose {E F G A} (h : Handler MN E F)
    (g : Handler MN F G) (t : itree E A) :
  peutt (FI := FI) eq (PTree.interp g (interp_itree h t))
    (interp_itree (Handler.cat h g) t).
Proof.
  apply (elab_postcompose free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.
End Completion.
