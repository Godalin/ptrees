Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

(** Regression: a client importing only the public facade can elaborate the
    curated semantic vocabulary and canonical equivalence notation. *)
From PTree.Eq Require Import ProbabilisticSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Implementation modules remain addressable by qualified names, but their
    historical short names are not transitively imported by the facade. *)
Fail Check frontier.
Fail Check operational_weak.
Fail Check frontier_head_bind_front.

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
Local Notation facade_probabilistic_eutt := probabilistic_eutt.
Local Notation facade_probabilistic_eutt_coinduction :=
  probabilistic_eutt_coinduction.
Local Notation facade_probabilistic_eutt_refl := probabilistic_eutt_refl.
Local Notation facade_probabilistic_eutt_sym := probabilistic_eutt_sym.
Local Notation facade_probabilistic_eutt_trans := probabilistic_eutt_trans.
Local Notation facade_probabilistic_eutt_ret := probabilistic_eutt_ret.
Local Notation facade_probabilistic_eutt_tau_l := probabilistic_eutt_tau_l.
Local Notation facade_probabilistic_eutt_tau_r := probabilistic_eutt_tau_r.
Local Notation facade_probabilistic_eutt_vis := probabilistic_eutt_vis.
Local Notation facade_probabilistic_eutt_prob := probabilistic_eutt_prob.
Local Notation facade_probabilistic_eutt_bind := probabilistic_eutt_bind.
Local Notation facade_finite_interaction_pattern := finite_interaction_pattern.
Local Notation facade_finite_interaction_query := finite_interaction_query.
Local Notation facade_finite_interaction_sem := finite_interaction_sem.
Local Notation facade_finite_interaction_sem_spec :=
  finite_interaction_sem_spec.
Local Notation facade_probabilistic_eutt_preserves_finite_interaction_sem :=
  probabilistic_eutt_preserves_finite_interaction_sem.

(** Parsing the notation through the facade is checked independently of a
    concrete measure instance.  Capability classes stay under their owning
    measure module rather than becoming extra facade aliases. *)
Section NotationRegression.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{FI : TwoLevelMeasure.SemanticMeasure MF}
  `{FC : @TwoLevelMeasure.SemanticMeasureCoreLaws MF FI}
  `{MX : TwoLevelMeasure.MixedMeasure MN MF}
  `{FO : @TwoLevelMeasure.SemanticOmega MF FI}.
Context {R : Type}.

Lemma public_probabilistic_eutt_notation (t u : ptree E MN R) :
  t ≈ₚ u -> probabilistic_eutt eq t u.
Proof. exact (fun H => H). Qed.

End NotationRegression.
