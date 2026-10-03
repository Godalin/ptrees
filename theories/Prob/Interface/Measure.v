(** Role: Generic semantic operations, core relational laws and Kleisli laws. *)
From Coq Require Import Utf8.

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
    (S : Type@{carrier} → Type@{representation}) := {
  sem_ret : ∀ {A : Type@{carrier}}, A → S A;
  sem_bind : ∀ {A B : Type@{carrier}},
      S A → (A → S B) → S B;
  sem_eq : ∀ {A : Type@{carrier}}, S A → S A → Prop;
  sem_ae : ∀ {A : Type@{carrier}}, S A → (A → Prop) → Prop;
  sem_lift : ∀ {A B : Type@{carrier}},
      (A → B → Prop) → S A → S B → Prop
}.

(** Opt-in semantic algebra, shared by native [MN] and frontier [MF].
    The subscript identifies the interface, not a particular carrier or
    instance. Import [SemanticMeasureNotations], then open the scope (or use
    [%sm]); this does not select a backend or change typeclass search. *)
Declare Scope semantic_measure_scope.
Delimit Scope semantic_measure_scope with sm.

Module SemanticMeasureNotations.
Notation "'ηₘ' x" := (sem_ret x)
  (at level 10, x at next level) : semantic_measure_scope.
Notation "mu '>>=ₘ' k" := (sem_bind mu k)
  (at level 50, left associativity) : semantic_measure_scope.
Notation "mu '≈ₘ' nu" := (sem_eq mu nu)
  (at level 70, no associativity) : semantic_measure_scope.
Notation "mu '≈[' R ']ₘ' nu" := (sem_lift R mu nu)
  (at level 70, R at next level, no associativity) : semantic_measure_scope.
End SemanticMeasureNotations.

(** Core extensional and relational laws shared by node and frontier
    measures.  More expensive Kleisli, gluing and omega assumptions remain
    separate capabilities. *)
Polymorphic Class SemanticMeasureCoreLaws@{carrier representation}
    (S : Type@{carrier} → Type@{representation})
    `{SI : SemanticMeasure S} := {
  sem_eq_refl : ∀ (A : Type@{carrier}), Reflexive (@sem_eq S SI A);
  sem_eq_sym : ∀ (A : Type@{carrier}), Symmetric (@sem_eq S SI A);
  sem_eq_trans : ∀ (A : Type@{carrier}), Transitive (@sem_eq S SI A);

  sem_ae_true : ∀ {A : Type@{carrier}} (mu : S A),
      sem_ae mu (λ _, True);
  sem_ae_mono : ∀ {A : Type@{carrier}}
      (mu : S A) (P Q : A → Prop),
      (∀ x, P x → Q x) → sem_ae mu P → sem_ae mu Q;
  sem_ae_conj : ∀ {A : Type@{carrier}}
      (mu : S A) (P Q : A → Prop),
      sem_ae mu P → sem_ae mu Q →
      sem_ae mu (λ x, P x ∧ Q x);

  sem_lift_mono : ∀ {A B : Type@{carrier}}
      (R T : A → B → Prop) mu nu,
      (∀ x y, R x y → T x y) →
      sem_lift R mu nu → sem_lift T mu nu;
  sem_lift_refl : ∀ {A : Type@{carrier}} (R : A → A → Prop) mu,
      Reflexive R → sem_lift R mu mu;
  sem_lift_ret : ∀ {A B : Type@{carrier}} (R : A → B → Prop) x y,
      R x y → sem_lift R (sem_ret x) (sem_ret y);
  sem_lift_proper_l : ∀ {A B : Type@{carrier}}
      (R : A → B → Prop) mu mu' nu,
      sem_eq mu mu' → sem_lift R mu nu → sem_lift R mu' nu;
  sem_lift_proper_r : ∀ {A B : Type@{carrier}}
      (R : A → B → Prop) mu nu nu',
      sem_eq nu nu' → sem_lift R mu nu → sem_lift R mu nu';
  sem_lift_sym : ∀ {A B : Type@{carrier}}
      (R : A → B → Prop) mu nu,
      sem_lift R mu nu → sem_lift (λ y x, R x y) nu mu;
  sem_lift_comp : ∀ {A B C : Type@{carrier}}
      (R : A → B → Prop) (T : B → C → Prop) mu nu xi,
      sem_lift R mu nu → sem_lift T nu xi →
      sem_lift (λ x z, ∃ y, R x y ∧ T y z) mu xi
}.

(** Ordinary semantic-measure Kleisli laws, used when resolving an existing
    distribution of residual PTS states. *)
Polymorphic Class SemanticMeasureBindLaws@{carrier representation}
    (S : Type@{carrier} → Type@{representation})
    `{SI : SemanticMeasure S} := {
  sem_bind_ret_l : ∀ {A B : Type@{carrier}} (x : A) (k : A → S B),
      sem_eq (sem_bind (sem_ret x) k) (k x);
  sem_bind_assoc : ∀ {A B C : Type@{carrier}} (mu : S A)
      (k : A → S B) (h : B → S C),
      sem_eq (sem_bind (sem_bind mu k) h)
        (sem_bind mu (λ x, sem_bind (k x) h));
  sem_bind_ae_proper : ∀ {A B : Type@{carrier}} (mu : S A)
      (k h : A → S B),
      sem_ae mu (λ x, sem_eq (k x) (h x)) →
      sem_eq (sem_bind mu k) (sem_bind mu h);
  sem_lift_bind : ∀ {A B C D : Type@{carrier}}
      (R : A → B → Prop) (T : C → D → Prop)
      (mu : S A) (nu : S B) (k : A → S C) (h : B → S D),
      sem_lift R mu nu →
      (∀ x y, R x y → sem_lift T (k x) (h y)) →
      sem_lift T (sem_bind mu k) (sem_bind nu h)
}.


#[global] Polymorphic Instance sem_eq_equivalence
    {S} `{SI : SemanticMeasure S}
    `{SL : @SemanticMeasureCoreLaws S SI} A :
  Equivalence (@sem_eq S SI A).
Proof.
  split; [apply sem_eq_refl | apply sem_eq_sym | apply sem_eq_trans].
Qed.
