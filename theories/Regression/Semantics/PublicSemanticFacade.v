(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

(** Regression: a client importing only the public facade can elaborate the
    curated semantic vocabulary and canonical equivalence notation. *)
From PTree Require Import PTree PTreeFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Direct exports expose the selected theorem modules, not a hand-maintained
    list of aliases. Unselected implementation modules remain qualified. *)
Check @frontier_certificate.
Fail Check @ptree_stable_hitting.
Check @stable_head_bind_front.
Fail Check pfinite.
Fail Check pfinite_rel.

Local Notation facade_ptree := ptree.
Local Notation facade_probabilistic_ptree := probabilistic_ptree.
Local Notation facade_probabilistic_ptree_ret := probabilistic_ptree_ret.
Local Notation facade_probabilistic_ptree_tau := probabilistic_ptree_tau.
Local Notation facade_probabilistic_ptree_vis := probabilistic_ptree_vis.
Local Notation facade_probabilistic_ptree_prob := probabilistic_ptree_prob.
Local Notation facade_probabilistic_ptree_bind := probabilistic_ptree_bind.
Local Notation facade_probabilistic_ptree_iter := probabilistic_ptree_iter.
Local Notation facade_stable_head := stable_head.
Local Notation facade_stable_head_rel := stable_head_rel.
Local Notation facade_stable_hitting := stable_hitting.
Local Notation facade_stable_hitting_exists := stable_hitting_exists.
Local Notation facade_stable_hitting_unique := stable_hitting_unique.
Local Notation facade_stable_hitting_ret_iff := stable_hitting_ret_iff.
Local Notation facade_stable_hitting_vis_iff := stable_hitting_vis_iff.
Local Notation facade_stable_hitting_tau_iff := stable_hitting_tau_iff.
Local Notation facade_stable_hitting_tau_iter := stable_hitting_tau_iter.
Local Notation facade_stable_hitting_prob_decompose := stable_hitting_prob_decompose.
Local Notation facade_stable_hitting_prob_compute := stable_hitting_prob_compute.
Local Notation facade_stable_hitting_prob_dirac := stable_hitting_prob_dirac.
Local Notation facade_stable_hitting_prob_flatten := stable_hitting_prob_flatten.
Local Notation facade_peutt_iff_hitting := peutt_iff_hitting.
Local Notation facade_peutt := peutt.
Local Notation facade_peutt_coinduction :=
  peutt_coinduction.
Local Notation facade_peutt_refl := peutt_refl.
Local Notation facade_peutt_sym := peutt_sym.
Local Notation facade_peutt_trans := peutt_trans.
Local Notation facade_peutt_ret := peutt_ret.
Local Notation facade_peutt_tau_l := peutt_tau_l.
Local Notation facade_peutt_tau_r := peutt_tau_r.
Local Notation facade_peutt_vis := peutt_vis.
Local Notation facade_peutt_prob := peutt_prob.
Local Notation facade_peutt_prob_rewrite := peutt_prob_rewrite.
Local Notation facade_finite_interaction_pattern := finite_interaction_pattern.
Local Notation facade_finite_interaction_query := finite_interaction_query.
Local Notation facade_finite_interaction_sem := finite_interaction_sem.
Local Notation facade_finite_interaction_sem_spec :=
  finite_interaction_sem_spec.
Local Notation facade_peutt_preserves_finite_interaction_sem :=
  peutt_preserves_finite_interaction_sem.

(** Parsing the notation through the facade is checked independently of a
    concrete measure instance.  Capability classes stay under their owning
    measure module rather than becoming extra facade aliases. *)
Section NotationRegression.
Context {E MN : Type -> Type}
  `{CB : PTree.Eq.Canonical.CanonicalBehavior MN}
  `{FC : @PTree.Prob.Interface.Measure.SemanticMeasureCoreLaws
    (@PTree.Eq.Canonical.behavior_frontier MN CB)
    (@PTree.Eq.Canonical.behavior_measure MN CB)}.
Context {R : Type}.

Lemma public_peutt_notation (t u : ptree E MN R) :
  t ≈ₚ u -> @PTree.Eq.Canonical.canonical_peutt E MN CB FC R R eq t u.
Proof. exact (fun H => H). Qed.

End NotationRegression.

From PTree Require Import PTreeFacts.
Local Notation facade_peutt_bind := peutt_bind.

From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
From PTree.Eq Require Import PTreeKernel PEutt.
Module PEuttNotationTests.
(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NotationRegression.
Context {E MN : Type -> Type}
  `{CB : PTree.Eq.Canonical.CanonicalBehavior MN}
  `{FC : @SemanticMeasureCoreLaws
    (@PTree.Eq.Canonical.behavior_frontier MN CB)
    (@PTree.Eq.Canonical.behavior_measure MN CB)}.

Lemma peutt_notation_homogeneous {R}
    (t u : ptree E MN R) :
  (t ≈ₚ u) <-> @PTree.Eq.Canonical.canonical_peutt E MN CB FC R R eq t u.
Proof. reflexivity. Qed.

Lemma peutt_notation_heterogeneous {R1 R2}
    (RR : R1 -> R2 -> Prop) (t : ptree E MN R1) (u : ptree E MN R2) :
  (t ≈ₚ[RR] u) <-> @PTree.Eq.Canonical.canonical_peutt E MN CB FC R1 R2 RR t u.
Proof. reflexivity. Qed.

End NotationRegression.

End PEuttNotationTests.
