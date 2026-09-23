(** Operation-level relational closure properties. These are ordinary Prop
    parameters, not typeclasses or conclusions about a program relation.
    Keeping the relational fields separate avoids requiring unrelated AE
    congruence laws when only relational bind is used. *)
Set Universe Polymorphism.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition relational_bind {M} (MI : SemanticMeasure M) : Prop :=
  forall A B C D (R : A -> B -> Prop) (T : C -> D -> Prop)
    (mu : M A) (nu : M B) (k : A -> M C) (h : B -> M D),
    sem_lift R mu nu ->
    (forall x y, R x y -> sem_lift T (k x) (h y)) ->
    sem_lift T (sem_bind mu k) (sem_bind nu h).

Definition relational_mixed_bind {MN MF}
    (NI : SemanticMeasure MN) (FI : SemanticMeasure MF)
    (MX : MixedMeasure MN MF) : Prop :=
  forall A B C D (R : A -> B -> Prop) (T : C -> D -> Prop)
    (mu : MN A) (nu : MN B) (k : A -> MF C) (h : B -> MF D),
    sem_lift R mu nu ->
    (forall x y, R x y -> sem_lift T (k x) (h y)) ->
    sem_lift T (mixed_bind mu k) (mixed_bind nu h).

Definition relational_zero {M} (MI : SemanticMeasure M)
    (MO : @SemanticOmega M MI) : Prop :=
  forall A B (R : A -> B -> Prop),
    sem_lift R (@sem_zero M MI MO A) (@sem_zero M MI MO B).

(** Only increasing chains are required. In particular this does not
    assert that arbitrary pointwise couplings admit increasing joints. *)
Definition relational_lub {M} (MI : SemanticMeasure M)
    (MO : @SemanticOmega M MI) : Prop :=
  forall A B (R : A -> B -> Prop) (c : nat -> M A) (d : nat -> M B) mu nu,
    sem_increasing c -> sem_increasing d ->
    sem_lub c mu -> sem_lub d nu ->
    (forall n, sem_lift R (c n) (d n)) -> sem_lift R mu nu.

Lemma relational_bind_of_laws {M} (MI : SemanticMeasure M)
    (MB : @SemanticMeasureBindLaws M MI) : relational_bind MI.
Proof. exact (@sem_lift_bind M MI MB). Qed.

Lemma relational_mixed_bind_of_laws {MN MF}
    (NI : SemanticMeasure MN) (FI : SemanticMeasure MF)
    (MX : MixedMeasure MN MF) (ML : @MixedMeasureLaws MN MF NI FI MX) :
  relational_mixed_bind NI FI MX.
Proof. exact (@mixed_lift_bind MN MF NI FI MX ML). Qed.
