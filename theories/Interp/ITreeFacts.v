(** Backend-independent behavioral laws for ITree elaboration. These are
    homomorphism laws, not an inverse or a source-eutt preservation theorem. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ITree.Core Require Import ITreeDefinition.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Handler ITreeBridge.
From PTree.Prob.Interface Require Import Measure Omega Mixed RelationalClosure.
From PTree.Eq Require Import PEutt Relation.
From PTree.Interp Require Import ITreeStructural.
Set Implicit Arguments.
Unset Strict Implicit.

Section Laws.
Context {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}.
Variables (Hmixed : relational_mixed_bind NI FI MX)
  (Hzero : relational_zero FO) (Hlimit : relational_lub FO).
Local Notation structural := (Relation.peutt_of_pstruct (relational_bind_of_laws FB) Hmixed Hzero Hlimit).

Theorem elab_ret {E F A} (h : Handler MN E F) (a : A) :
  peutt (MF := MF) eq (interp_itree h (ITreeDefinition.Ret a)) (Ret a).
Proof. apply structural. apply interp_itree_ret. Qed.

Theorem elab_tau {E F A} (h : Handler MN E F) (t : itree E A) :
  peutt (MF := MF) eq (interp_itree h (ITreeDefinition.Tau t)) (interp_itree h t).
Proof.
  eapply peutt_trans; [apply structural; apply interp_itree_tau|apply peutt_tau_l].
Qed.

Theorem elab_event {E F A X} (h : Handler MN E F) (e : E X) (k : X -> itree E A) :
  peutt (MF := MF) eq (interp_itree h (ITreeDefinition.Vis e k))
    (PTree.bind (h X e) (fun x => interp_itree h (k x))).
Proof.
  eapply peutt_trans; [apply structural; apply interp_itree_vis|apply peutt_tau_l].
Qed.

Theorem elab_trigger {E F X} (h : Handler MN E F) (e : E X) :
  peutt (MF := MF) eq (interp_itree h (ITree.trigger e)) (h X e).
Proof.
  eapply peutt_trans; [apply structural; apply interp_itree_trigger_structural|apply peutt_tau_l].
Qed.

Theorem elab_sample {E A X} (mu : MN X) (k : X -> itree (probE MN +' E) A) :
  peutt (MF := MF) eq (elaborate (ITreeDefinition.Vis (inl1 (Sample mu)) k))
    (Prob mu (fun x => elaborate (k x))).
Proof.
  eapply peutt_trans; [apply structural; apply elaborate_sample_structural|apply peutt_tau_l].
Qed.

Theorem elab_vis {E A X} (e : E X) (k : X -> itree (probE MN +' E) A) :
  peutt (MF := MF) eq (elaborate (ITreeDefinition.Vis (inr1 e) k))
    (Vis e (fun x => elaborate (k x))).
Proof.
  eapply peutt_trans; [apply structural; apply elaborate_vis_structural|apply peutt_tau_l].
Qed.

Theorem elab_bind {E F A B} (h : Handler MN E F)
    (t : itree E A) (k : A -> itree E B) :
  peutt (MF := MF) eq (interp_itree h (ITree.bind t k))
    (PTree.bind (interp_itree h t) (fun x => interp_itree h (k x))).
Proof. apply structural. apply interp_itree_bind. Qed.

Theorem elab_iter {E F I A} (h : Handler MN E F)
    (step : I -> itree E (I+A)) i :
  peutt (MF := MF) eq (interp_itree h (ITree.iter step i))
    (PTree.iter (fun j => interp_itree h (step j)) i).
Proof. apply structural. apply interp_itree_iter. Qed.

Theorem elab_sample_trigger {X} (mu : MN X) :
  peutt (MF := MF) eq (elaborate_closed (ITree.trigger (Sample mu)))
    (Prob mu (fun x => Ret x)).
Proof. exact (elab_trigger (@sample_handler MN void1) (Sample mu)). Qed.

Theorem elab_postcompose {E F G A} (h : Handler MN E F)
    (g : Handler MN F G) (t : itree E A) :
  peutt (MF := MF) eq (PTree.interp g (interp_itree h t))
    (interp_itree (Handler.cat h g) t).
Proof. apply structural. apply interp_itree_postcompose. Qed.
End Laws.
