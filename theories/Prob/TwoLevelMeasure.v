Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A universe-polymorphic semantic measure interface.  Unlike the legacy
    [MeasureInterface], its carrier and representation universes are explicit,
    so independent instances may be used for source-level samples and for
    higher-universe semantic states. *)
Polymorphic Class SemanticMeasureInterface@{carrier representation}
    (S : Type@{carrier} -> Type@{representation}) := {
  sem_ret : forall {A : Type@{carrier}}, A -> S A;
  sem_bind : forall {A B : Type@{carrier}},
      S A -> (A -> S B) -> S B;
  sem_eq : forall {A : Type@{carrier}}, S A -> S A -> Prop;
  sem_ae : forall {A : Type@{carrier}}, S A -> (A -> Prop) -> Prop;
  sem_lift : forall {A B : Type@{carrier}},
      (A -> B -> Prop) -> S A -> S B -> Prop
}.

(** The two-level bridge.  [MN] is the measure stored by a [Prob] node;
    [MF] is the measure of stable heads and residual semantic states.  The
    mixed bind is exactly the operation used by the probabilistic frontier
    rule. *)
Polymorphic Class MixedMeasureInterface@{node node_rep frontier frontier_rep}
    (MN : Type@{node} -> Type@{node_rep})
    (MF : Type@{frontier} -> Type@{frontier_rep}) := {
  mixed_bind : forall {A : Type@{node}} {B : Type@{frontier}},
      MN A -> (A -> MF B) -> MF B
}.

(** Core extensional and relational laws shared by node and frontier
    measures.  More expensive Kleisli, gluing and omega assumptions remain
    separate capabilities. *)
Polymorphic Class SemanticMeasureCoreLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S} := {
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
    `{SI : SemanticMeasureInterface S} := {
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

(** The diagonal coupling may be restricted to an almost-everywhere good
    set.  This capability is precisely what turns AE equality of kernels into
    Kleisli congruence; it is kept separate from the basic coupling algebra. *)
Polymorphic Class SemanticMeasureAELiftLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S} := {
  sem_lift_refl_ae : forall {A : Type@{carrier}}
      (mu : S A) (P : A -> Prop),
      sem_ae mu P ->
      sem_lift (fun x y => x = y /\ P x) mu mu
}.

(** Laws connecting the node and frontier layers.  AE lives at the node
    layer, while equality and couplings of continuations live at the
    frontier layer. *)
Polymorphic Class MixedMeasureLaws@{node node_rep frontier frontier_rep}
    (MN : Type@{node} -> Type@{node_rep})
    (MF : Type@{frontier} -> Type@{frontier_rep})
    `{NI : SemanticMeasureInterface MN}
    `{FI : SemanticMeasureInterface MF}
    `{MX : MixedMeasureInterface MN MF} := {
  mixed_bind_ae_proper : forall {A : Type@{node}} {B : Type@{frontier}}
      (mu : MN A) (k h : A -> MF B),
      sem_ae mu (fun x => sem_eq (k x) (h x)) ->
      sem_eq (mixed_bind mu k) (mixed_bind mu h);
  mixed_bind_assoc : forall
      {A : Type@{node}} {B C : Type@{frontier}}
      (mu : MN A) (k : A -> MF B) (h : B -> MF C),
      sem_eq (sem_bind (mixed_bind mu k) h)
        (mixed_bind mu (fun x => sem_bind (k x) h));
  mixed_lift_bind : forall
      {A B : Type@{node}} {C D : Type@{frontier}}
      (R : A -> B -> Prop) (T : C -> D -> Prop)
      (mu : MN A) (nu : MN B) (k : A -> MF C) (h : B -> MF D),
      sem_lift R mu nu ->
      (forall x y, R x y -> sem_lift T (k x) (h y)) ->
      sem_lift T (mixed_bind mu k) (mixed_bind nu h)
}.

(** Omega structure belongs to the semantic/frontier layer.  The order is
    explicit so a unified frontier can state that finite approximants form an
    increasing chain instead of treating every arbitrary sequence as a lub. *)
Polymorphic Class SemanticOmegaInterface@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S} := {
  sem_zero : forall {A : Type@{carrier}}, S A;
  sem_le : forall {A : Type@{carrier}}, S A -> S A -> Prop;
  sem_lub : forall {A : Type@{carrier}}, (nat -> S A) -> S A -> Prop;
  sem_total : forall {A : Type@{carrier}}, S A -> Prop
}.

Definition sem_increasing {SM} `{SI : SemanticMeasureInterface SM}
    `{SO : @SemanticOmegaInterface SM SI} {A}
    (chain : nat -> SM A) : Prop :=
  forall n, sem_le (chain n) (chain (Datatypes.S n)).

(** Minimal order theory needed to show that primitive stable-hitting
    approximants form an increasing chain.  It is independent of omega-limit
    existence and can therefore be supplied by partial backends. *)
Polymorphic Class SemanticMeasureOrderLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S}
    `{SO : @SemanticOmegaInterface S SI} := {
  sem_le_refl : forall {A : Type@{carrier}} (mu : S A), sem_le mu mu;
  sem_zero_le : forall {A : Type@{carrier}} (mu : S A), sem_le sem_zero mu;
  sem_bind_le_k : forall {A B : Type@{carrier}} (mu : S A)
      (k h : A -> S B),
      (forall x, sem_le (k x) (h x)) ->
      sem_le (sem_bind mu k) (sem_bind mu h)
}.

(** Continuity needed by the absorbing PTS construction.  Existence is
    restricted to increasing chains; uniqueness and bind-continuity are
    extensional. *)
Polymorphic Class SemanticOmegaLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S}
    `{SO : @SemanticOmegaInterface S SI} := {
  sem_lub_exists : forall {A : Type@{carrier}} (chain : nat -> S A),
      sem_increasing chain -> exists out, sem_lub chain out;
  sem_lub_unique : forall {A : Type@{carrier}} (chain : nat -> S A) mu nu,
      sem_lub chain mu -> sem_lub chain nu -> sem_eq mu nu;
  sem_lub_proper : forall {A : Type@{carrier}}
      (chain chain' : nat -> S A) mu nu,
      (forall n, sem_eq (chain n) (chain' n)) ->
      sem_lub chain mu -> sem_lub chain' nu -> sem_eq mu nu;
  sem_lub_chain_proper : forall {A : Type@{carrier}}
      (chain chain' : nat -> S A) mu,
      (forall n, sem_eq (chain n) (chain' n)) ->
      sem_lub chain mu -> sem_lub chain' mu;
  sem_bind_lub : forall {A B : Type@{carrier}} (chain : nat -> S A) mu
      (k : A -> S B),
      sem_increasing chain -> sem_lub chain mu ->
      sem_lub (fun n => sem_bind (chain n) k) (sem_bind mu k)
}.

#[global] Polymorphic Instance sem_eq_equivalence
    {S} `{SI : SemanticMeasureInterface S}
    `{SL : @SemanticMeasureCoreLaws S SI} A :
  Equivalence (@sem_eq S SI A).
Proof.
  split; [apply sem_eq_refl | apply sem_eq_sym | apply sem_eq_trans].
Qed.
