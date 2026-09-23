(** Role: Mass comparison and support transport/restriction for couplings. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.AE.

(** Abstract equality of total semantic weight.  On a subprobability backend
    this is equality of total subprobability mass.  The formulation avoids
    committing the generic interface to a numeric mass operation: a coupling
    for the total relation exists exactly when the two marginals carry the
    same amount of mass in the intended backends. *)
Polymorphic Definition sem_same_mass@{carrier representation}
    {S : Type@{carrier} -> Type@{representation}}
    `{SI : SemanticMeasure S} {A B : Type@{carrier}}
    (mu : S A) (nu : S B) : Prop :=
  sem_lift (fun _ _ => True) mu nu.

Polymorphic Lemma sem_lift_same_mass@{carrier representation}
    {S : Type@{carrier} -> Type@{representation}}
    `{SI : SemanticMeasure S}
    `{SL : @SemanticMeasureCoreLaws S SI}
    {A B : Type@{carrier}} (R : A -> B -> Prop) mu nu :
  sem_lift R mu nu -> sem_same_mass mu nu.
Proof.
  intro Hlift. eapply sem_lift_mono; [|exact Hlift].
  intros x y Hxy. exact I.
Qed.

(** A coupling can be replaced by one supported on predicates that hold
    almost everywhere in its two marginals.  This is the standard bridge
    from measure-theoretic AE invariants to pointwise relational coinduction;
    it is intentionally not bundled into the basic coupling algebra. *)
Polymorphic Class SemanticMeasureCouplingAELaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S} := {
  sem_lift_ae_transport_r : forall {A B : Type@{carrier}}
      (R : A -> B -> Prop) (mu : S A) (nu : S B) (P : A -> Prop),
      sem_lift R mu nu -> sem_ae mu P ->
      sem_ae nu (fun y => exists x, R x y /\ P x);
  sem_lift_ae_restrict : forall {A B : Type@{carrier}}
      (R : A -> B -> Prop) (mu : S A) (nu : S B)
      (P : A -> Prop) (Q : B -> Prop),
      sem_lift R mu nu ->
      sem_ae mu P -> sem_ae nu Q ->
      sem_lift (fun x y => R x y /\ P x /\ Q y) mu nu
}.

(** Derived diagonal restriction. Deliberately not a global instance: clients
    may use this constructor explicitly without adding a search cycle. *)
Lemma coupling_ae_implies_ae_lift {S : Type -> Type}
    `{SI : SemanticMeasure S} `{SC : @SemanticMeasureCoreLaws S SI}
    `{CA : @SemanticMeasureCouplingAELaws S SI} :
  @SemanticMeasureAELiftLaws S SI.
Proof.
  constructor. intros A mu P HP.
  eapply sem_lift_mono with (R := fun x y => x = y /\ P x /\ P y).
  - intros x y [Hxy [Hx Hy]]. split; assumption.
  - eapply sem_lift_ae_restrict.
    + apply sem_lift_refl. intro x. reflexivity.
    + exact HP.
    + exact HP.
Qed.
