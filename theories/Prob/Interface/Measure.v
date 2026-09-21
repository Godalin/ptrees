(** Role: Generic semantic operations, core relational laws and Kleisli laws. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A universe-polymorphic semantic measure structure.  Unlike the legacy
    [MeasureInterface], its carrier and representation universes are explicit,
    so independent instances may be used for source-level samples and for
    higher-universe semantic states.  Operation-bearing classes use noun
    names; separate property packages carry the [Laws] suffix. *)
Polymorphic Class SemanticMeasure@{carrier representation}
    (S : Type@{carrier} -> Type@{representation}) := {
  sem_ret : forall {A : Type@{carrier}}, A -> S A;
  sem_bind : forall {A B : Type@{carrier}},
      S A -> (A -> S B) -> S B;
  sem_eq : forall {A : Type@{carrier}}, S A -> S A -> Prop;
  sem_ae : forall {A : Type@{carrier}}, S A -> (A -> Prop) -> Prop;
  sem_lift : forall {A B : Type@{carrier}},
      (A -> B -> Prop) -> S A -> S B -> Prop
}.

(** Core extensional and relational laws shared by node and frontier
    measures.  More expensive Kleisli, gluing and omega assumptions remain
    separate capabilities. *)
Polymorphic Class SemanticMeasureCoreLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S} := {
  sem_eq_refl : forall (A : Type@{carrier}), Reflexive (@sem_eq S SI A);
  sem_eq_sym : forall (A : Type@{carrier}), Symmetric (@sem_eq S SI A);
  sem_eq_trans : forall (A : Type@{carrier}), Transitive (@sem_eq S SI A);

  sem_ae_true : forall {A : Type@{carrier}} (mu : S A),
      sem_ae mu (fun _ => True);
  sem_ae_mono : forall {A : Type@{carrier}}
      (mu : S A) (P Q : A -> Prop),
      (forall x, P x -> Q x) -> sem_ae mu P -> sem_ae mu Q;
  sem_ae_conj : forall {A : Type@{carrier}}
      (mu : S A) (P Q : A -> Prop),
      sem_ae mu P -> sem_ae mu Q ->
      sem_ae mu (fun x => P x /\ Q x);

  sem_lift_mono : forall {A B : Type@{carrier}}
      (R T : A -> B -> Prop) mu nu,
      (forall x y, R x y -> T x y) ->
      sem_lift R mu nu -> sem_lift T mu nu;
  sem_lift_refl : forall {A : Type@{carrier}} (R : A -> A -> Prop) mu,
      Reflexive R -> sem_lift R mu mu;
  sem_lift_ret : forall {A B : Type@{carrier}} (R : A -> B -> Prop) x y,
      R x y -> sem_lift R (sem_ret x) (sem_ret y);
  sem_lift_proper_l : forall {A B : Type@{carrier}}
      (R : A -> B -> Prop) mu mu' nu,
      sem_eq mu mu' -> sem_lift R mu nu -> sem_lift R mu' nu;
  sem_lift_proper_r : forall {A B : Type@{carrier}}
      (R : A -> B -> Prop) mu nu nu',
      sem_eq nu nu' -> sem_lift R mu nu -> sem_lift R mu nu';
  sem_lift_sym : forall {A B : Type@{carrier}}
      (R : A -> B -> Prop) mu nu,
      sem_lift R mu nu -> sem_lift (fun y x => R x y) nu mu;
  sem_lift_comp : forall {A B C : Type@{carrier}}
      (R : A -> B -> Prop) (T : B -> C -> Prop) mu nu xi,
      sem_lift R mu nu -> sem_lift T nu xi ->
      sem_lift (fun x z => exists y, R x y /\ T y z) mu xi
}.

(** Ordinary semantic-measure Kleisli laws, used when resolving an existing
    distribution of residual PTS states. *)
Polymorphic Class SemanticMeasureBindLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S} := {
  sem_bind_ret_l : forall {A B : Type@{carrier}} (x : A) (k : A -> S B),
      sem_eq (sem_bind (sem_ret x) k) (k x);
  sem_bind_assoc : forall {A B C : Type@{carrier}} (mu : S A)
      (k : A -> S B) (h : B -> S C),
      sem_eq (sem_bind (sem_bind mu k) h)
        (sem_bind mu (fun x => sem_bind (k x) h));
  sem_bind_ae_proper : forall {A B : Type@{carrier}} (mu : S A)
      (k h : A -> S B),
      sem_ae mu (fun x => sem_eq (k x) (h x)) ->
      sem_eq (sem_bind mu k) (sem_bind mu h);
  sem_lift_bind : forall {A B C D : Type@{carrier}}
      (R : A -> B -> Prop) (T : C -> D -> Prop)
      (mu : S A) (nu : S B) (k : A -> S C) (h : B -> S D),
      sem_lift R mu nu ->
      (forall x y, R x y -> sem_lift T (k x) (h y)) ->
      sem_lift T (sem_bind mu k) (sem_bind nu h)
}.


#[global] Polymorphic Instance sem_eq_equivalence
    {S} `{SI : SemanticMeasure S}
    `{SL : @SemanticMeasureCoreLaws S SI} A :
  Equivalence (@sem_eq S SI A).
Proof.
  split; [apply sem_eq_refl | apply sem_eq_sym | apply sem_eq_trans].
Qed.
