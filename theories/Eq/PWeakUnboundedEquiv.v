Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 RelationClasses.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift MeasureIteration.
From PTree.Eq Require Import PWeakUnbounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [auweak] is the coinductively generated one-step weak-bisimulation
    evidence.  Its reflexivity and symmetry are available without choosing a
    canonical representation for omega limits, while raw transitivity needs
    an additional frontier-coherence principle.

    [auequiv] is the explicit equivalence closure exposed to clients that
    need an actual program equivalence.  Keeping the closure named avoids
    silently claiming raw transitivity from insufficient measure axioms. *)
Section UnboundedWeakEquivalence.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M}
  `{MC : @MeasureCoreLaws M MI}
  `{MO : @MeasureOmegaInterface M MI}.

Inductive auequiv {R : Type} : ptree E M R -> ptree E M R -> Prop :=
  | AUEWeak t1 t2 : auweak eq t1 t2 -> auequiv t1 t2
  | AUERefl t : auequiv t t
  | AUESym t1 t2 : auequiv t1 t2 -> auequiv t2 t1
  | AUETrans t1 t2 t3 :
      auequiv t1 t2 -> auequiv t2 t3 -> auequiv t1 t3.

Lemma auequiv_of_auweak {R} (t1 t2 : ptree E M R) :
  auweak eq t1 t2 -> auequiv t1 t2.
Proof. intro H. constructor. exact H. Qed.

Lemma auequiv_refl {R} : Reflexive (@auequiv R).
Proof. intro t. exact (AUERefl t). Qed.

Lemma auequiv_sym {R} : Symmetric (@auequiv R).
Proof. intros t1 t2 H. exact (AUESym H). Qed.

Lemma auequiv_trans {R} : Transitive (@auequiv R).
Proof. intros t1 t2 t3 H12 H23. exact (AUETrans H12 H23). Qed.

#[global] Instance auequiv_equivalence {R} :
  Equivalence (@auequiv R).
Proof.
  constructor.
  - exact auequiv_refl.
  - exact auequiv_sym.
  - exact auequiv_trans.
Qed.

(** Symmetry of a base coinductive proof can be used without adding an
    extra closure step. *)
Lemma auequiv_auweak_sym
    `{ML : @MeasureLaws M MI MC}
    {R} (t1 t2 : ptree E M R) :
  auweak eq t1 t2 -> auequiv t2 t1.
Proof.
  intro H. constructor. exact (auweak_sym_eq H).
Qed.

End UnboundedWeakEquivalence.
