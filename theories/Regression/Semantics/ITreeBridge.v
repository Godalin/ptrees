(** Datatype, administrative Tau, native sampling, and effect boundaries. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ITree.Core Require Import ITreeDefinition.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition ITreeBridge.

Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Eq.PEutt.peutt.

From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ.
From PTree.Interp Require Import ITreeStructural.
From PTree.Interp.FreeOmega Require Import ITreeCompletion.
Set Implicit Arguments.

Variant interactionE : Type -> Type := Ask : interactionE bool.

Example sample_is_native {A} (mu : SubEnumQ A) :
  elaborate_closed (ITree.trigger (Sample mu)) ≈ₚ Prob mu (fun x => Ret x).
Proof. apply free_omega_elab_sample_trigger. Qed.

(** The actual syntax has one administrative Tau, not a residual Sample Vis. *)
Example native_observation {MN X} (mu : MN X) :
  observe (elaborate_closed (ITree.trigger (Sample mu))) =
  TauF (PTree.bind (Prob mu (fun x => Ret x))
    (fun x => interp_itree sample_handler (ITreeDefinition.Ret x))).
Proof. reflexivity. Qed.

Example source_tau {A} (t : itree (probE SubEnumQ) A) :
  elaborate_closed (ITreeDefinition.Tau t) ≈ₚ elaborate_closed t.
Proof. apply free_omega_elab_tau. Qed.

Example ordinary_event_retained :
  elaborate (ITreeDefinition.Vis (inr1 Ask)
    (fun x => (ITreeDefinition.Ret x : itree (probE SubEnumQ +' interactionE) bool))) ≈ₚ
  Vis Ask (fun x => elaborate (ITreeDefinition.Ret x)).
Proof. apply free_omega_elab_vis. Qed.

Example open_sampling {X A} (mu : SubEnumQ X)
    (k : X -> itree (probE SubEnumQ +' interactionE) A) :
  elaborate (ITreeDefinition.Vis (inl1 (Sample mu)) k) ≈ₚ
  Prob mu (fun x => elaborate (k x)).
Proof. apply free_omega_elab_sample. Qed.

Example partial_sampling_not_normalized {A} :
  elaborate_closed (ITree.trigger (Sample (@subenumQ_zero A))) ≈ₚ
  Prob subenumQ_zero (fun x => Ret x).
Proof. apply free_omega_elab_sample_trigger. Qed.

Example embedding_bind {E MN A B} (t : itree E A) (k : A -> itree E B) :
  pstruct eq (@from_itree E MN B (ITree.bind t k))
    (PTree.bind (from_itree t) (fun x => from_itree (k x))).
Proof. apply from_itree_bind. Qed.

Example target_handler_postcomposition {E F G MN A}
    (h : Handler MN E F) (g : Handler MN F G) (t : itree E A) :
  pstruct eq (PTree.interp g (interp_itree h t))
    (interp_itree (Handler.cat h g) t).
Proof. apply interp_itree_postcompose. Qed.

Section LargeCarrier.
Universe hi.
Constraint Set < hi.
Example high_embedding (A : Type@{hi}) (a : A) :
  pstruct eq (@from_itree void1 SubEnumQ A (ITreeDefinition.Ret a)) (Ret a).
Proof. apply from_itree_ret. Qed.
End LargeCarrier.

Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.Backend.MathComp.Direct.MathComp_CanonicalBehavior.
