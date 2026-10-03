(** Canonical completion clients of the generic handler calculus.
    These names do not shadow the generic theorem owners. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition Handler Fold.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure BindOrder RelationalLimit.
From PTree.Eq Require Import PEutt.
From PTree.Interp Require Import HandlerRelation HandlerFacts FoldPTree.
Set Implicit Arguments.
Unset Strict Implicit.

Section Completion.
Context {MN : Type → Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation W E A B RR := (@peutt E MN MF FI FC FreeOmegaMixedMeasure FO A B RR).
Local Notation HE E F := (@peutt_handler E F MN MF FI FC FreeOmegaMixedMeasure FO).

Theorem free_omega_peutt_interp_handler_rel {E F A B}
    (RR : A → B → Prop) (h g : Handler MN E F)
    (t : ptree E MN A) (u : ptree E MN B) :
  HE E F h g → W E A B RR t u →
  W F A B RR (PTree.interp_tree h t) (PTree.interp_tree g u).
Proof.
  intros H Htu.
  exact (peutt_interp_handler_rel free_omega_relational_zero free_omega_relational_lub H Htu).
Qed.

Lemma free_omega_peutt_interp_handler_Proper {E F A} :
  Proper (HE E F ==> W E A A eq ==> W F A A eq)
    (λ h t, @PTree.interp_tree E F MN h A t).
Proof.
  apply (peutt_interp_handler_Proper free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_handler_cat_congr {E F G}
    (h1 h2 : Handler MN E F) (g1 g2 : Handler MN F G) :
  HE E F h1 h2 → HE F G g1 g2 →
  HE E G (Handler.cat h1 g1) (Handler.cat h2 g2).
Proof. apply (handler_cat_congr free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_handler_cat_id_l {E F} (h : Handler MN E F) :
  HE E F (Handler.cat Handler.id_ h) h.
Proof.
  apply (handler_cat_id_l free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_handler_cat_id_r {E F} (h : Handler MN E F) :
  HE E F (Handler.cat h Handler.id_) h.
Proof. apply handler_cat_id_r. Qed.

Theorem free_omega_handler_cat_assoc {E F G H}
    (h : Handler MN E F) (g : Handler MN F G) (k : Handler MN G H) :
  HE E H (Handler.cat (Handler.cat h g) k) (Handler.cat h (Handler.cat g k)).
Proof.
  apply (handler_cat_assoc free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_handler_case_inl {E F G}
    (h : Handler MN E G) (g : Handler MN F G) :
  HE E G (Handler.cat Handler.inl_ (Handler.case_ h g)) h.
Proof.
  apply (handler_case_inl free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_handler_case_inr {E F G}
    (h : Handler MN E G) (g : Handler MN F G) :
  HE F G (Handler.cat Handler.inr_ (Handler.case_ h g)) g.
Proof.
  apply (handler_case_inr free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem free_omega_handler_bimap_congr {E1 E2 F1 F2}
    (h1 h2 : Handler MN E1 F1) (g1 g2 : Handler MN E2 F2) :
  HE E1 F1 h1 h2 → HE E2 F2 g1 g2 →
  peutt_handler (FI := FI)
    (Handler.bimap h1 g1) (Handler.bimap h2 g2).
Proof. apply (handler_bimap_congr free_omega_relational_zero free_omega_relational_lub). Qed.

Lemma free_omega_peutt_interp_handler_polymorphic_Proper {E F} :
  Proper (HE E F ==>
    forall_relation (λ A, W E A A eq ==> W F A A eq)) (@PTree.interp_tree E F MN).
Proof.
  apply (peutt_interp_handler_polymorphic_Proper
    free_omega_relational_zero free_omega_relational_lub).
Qed.

(** Public selected-sampling interpretation. These corollaries discharge the
    same three completion certificates once; they add no behavioral proof. *)
Theorem free_omega_interp_agrees {E F A} (h : Handler MN E F) (t : ptree E MN A) :
  W F A A eq (interp h t) (PTree.interp_tree h t).
Proof. apply (interp_ptree_agrees free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_interp_ret {E F A} (h : Handler MN E F) (a : A) :
  W F A A eq (interp h (Ret a)) (Ret a).
Proof. apply (interp_ptree_ret free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_interp_tau {E F A} (h : Handler MN E F) (t : ptree E MN A) :
  W F A A eq (interp h (Tau t)) (interp h t).
Proof. apply (interp_ptree_tau free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_interp_bind {E F A B} (h : Handler MN E F)
    (t : ptree E MN A) (k : A → ptree E MN B) :
  W F B B eq (interp h (PTree.bind t k))
    (PTree.bind (interp h t) (λ x, interp h (k x))).
Proof. apply (interp_ptree_bind free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_interp_vis {E F X A} (h : Handler MN E F)
    (e : E X) (k : X → ptree E MN A) :
  W F A A eq (interp h (Vis e k)) (PTree.bind (h X e) (λ x, interp h (k x))).
Proof. apply (interp_ptree_vis free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_interp_prob {E F X A} (h : Handler MN E F)
    (mu : MN X) (k : X → ptree E MN A) :
  W F A A eq (interp h (Prob mu k)) (Prob mu (λ x, interp h (k x))).
Proof. apply (interp_ptree_prob free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_interp_iter {E F I A} (h : Handler MN E F)
    (step : I → ptree E MN (I+A)) i :
  W F A A eq (interp h (PTree.iter step i)) (PTree.iter (λ j, interp h (step j)) i).
Proof. apply (interp_ptree_iter free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_interp_trigger {E F X} (h : Handler MN E F) (e : E X) :
  W F X X eq (interp h (PTree.trigger e)) (h X e).
Proof. apply (interp_ptree_trigger free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_interp_sample {E F X} (h : Handler MN E F) (mu : MN X) :
  W F X X eq (interp h (PTree.sample mu)) (PTree.sample mu).
Proof. apply (interp_ptree_sample free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_interp_identity {E A} (t : ptree E MN A) :
  W E A A eq (interp Handler.id_ t) t.
Proof. apply (interp_ptree_identity free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_interp_compose {E F G A}
    (h : Handler MN E F) (g : Handler MN F G) (t : ptree E MN A) :
  W G A A eq (interp g (interp h t)) (interp (Handler.cat h g) t).
Proof. apply (interp_ptree_compose free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_interp_handler_rel {E F A B} (RR : A → B → Prop)
    (h g : Handler MN E F) (t : ptree E MN A) (u : ptree E MN B) :
  HE E F h g → W E A B RR t u → W F A B RR (interp h t) (interp g u).
Proof. apply (interp_ptree_handler_rel free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Theorem free_omega_interp_peutt {E F A B} (RR : A → B → Prop)
    (h : Handler MN E F) (t : ptree E MN A) (u : ptree E MN B) :
  W E A B RR t u → W F A B RR (interp h t) (interp h u).
Proof. apply (interp_ptree_peutt free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Lemma free_omega_interp_source_Proper {E F A} (h : Handler MN E F) :
  Proper (W E A A eq ==> W F A A eq) (@interp E MN (ptree F MN) _ _ _ h A).
Proof. apply (interp_ptree_Proper free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Lemma free_omega_interp_handler_Proper {E F A} :
  Proper (HE E F ==> W E A A eq ==> W F A A eq)
    (λ h t, @interp E MN (ptree F MN) _ _ _ h A t).
Proof. apply (interp_ptree_handler_Proper free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.

Lemma free_omega_interp_handler_polymorphic_Proper {E F} :
  Proper (HE E F ==> forall_relation (λ A, W E A A eq ==> W F A A eq))
    (@interp E MN (ptree F MN) _ _ _).
Proof. apply (interp_ptree_handler_polymorphic_Proper free_omega_relational_mixed_bind
  free_omega_relational_zero free_omega_relational_lub). Qed.
End Completion.
