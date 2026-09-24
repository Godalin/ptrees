(** Behavioral source congruence and genuine source-interpreter commuting.
    The source relation is ITree.eutt, not an assumed PTree equivalence. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms.
From ITree.Core Require Import ITreeDefinition.
From ITree.Eq Require Import Eqit.
From ITree.Interp Require Import Interp.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Handler ITreeBridge.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder RelationalClosure.
From PTree.Eq Require Import PEutt Relation.
From PTree.Interp Require Import ITreeEutt ITreeSourceInterp ITreeStructural Unrestricted.
Set Implicit Arguments.
Unset Strict Implicit.

Section Square.
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

Theorem from_itree_interp {E F A} (h : forall X, E X -> itree F X) (t : itree E A) :
  peutt (MF := MF) eq (from_itree (Interp.interp h t))
    (PTree.interp (fun X e => @from_itree F MN X (h X e)) (from_itree t)).
Proof.
  eapply peutt_trans.
  - apply (from_itree_eutt (u := itree_interp_before h t) Hzero).
    symmetry. apply itree_interp_before_eutt.
  - apply (Relation.peutt_of_pstruct (relational_bind_of_laws FB) Hmixed Hzero Hlimit).
    apply from_itree_interp_before.
Qed.

Context
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BindOrd : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MixedOrd : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.

Theorem interp_itree_eutt {E F A B} (h : Handler MN E F) (RR : A -> B -> Prop)
    (t : itree E A) (u : itree E B) :
  eutt RR t u -> peutt (MF := MF) RR (interp_itree h t) (interp_itree h u).
Proof.
  intro H. unfold interp_itree.
  apply (Unrestricted.peutt_interp Hzero Hlimit).
  exact (from_itree_eutt Hzero H).
Qed.

Theorem elaborate_eutt {E A B} (RR : A -> B -> Prop)
    (t : itree (probE MN +' E) A) (u : itree (probE MN +' E) B) :
  eutt RR t u -> peutt (MF := MF) RR (elaborate t) (elaborate u).
Proof. apply interp_itree_eutt. Qed.

Theorem elaborate_closed_eutt {A B} (RR : A -> B -> Prop)
    (t : itree (probE MN) A) (u : itree (probE MN) B) :
  eutt RR t u -> peutt (MF := MF) RR (elaborate_closed t) (elaborate_closed u).
Proof. apply interp_itree_eutt. Qed.

(** First interpret a source ITree handler, then lower into PTree; or lower
    that handler and interpret once. Arbitrary returning, divergent, and
    multi-event handlers are allowed. *)
Theorem interp_itree_source_interp {E F G A}
    (h : forall X, E X -> itree F X) (g : Handler MN F G) (t : itree E A) :
  peutt (MF := MF) eq (interp_itree g (Interp.interp h t))
    (interp_itree (fun X e => interp_itree g (h X e)) t).
Proof.
  unfold interp_itree at 1. eapply peutt_trans.
  - apply (Unrestricted.peutt_interp Hzero Hlimit). apply from_itree_interp.
  - apply (Relation.peutt_of_pstruct (relational_bind_of_laws FB) Hmixed Hzero Hlimit).
    apply interp_itree_postcompose.
Qed.

Corollary elaborate_source_interp {E F A}
    (h : forall X, E X -> itree (probE MN +' F) X) (t : itree E A) :
  peutt (MF := MF) eq (elaborate (Interp.interp h t))
    (interp_itree (fun X e => elaborate (h X e)) t).
Proof. apply interp_itree_source_interp. Qed.

Lemma elaborate_eutt_Proper {E A} :
  Proper (eutt eq ==> peutt (MF := MF) eq) (@elaborate MN E A).
Proof. intros t u H. exact (elaborate_eutt H). Qed.
End Square.
