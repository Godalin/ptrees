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

(** Abstract equality of total subprobability mass.  This formulation avoids
    committing the generic interface to a numeric mass operation: a coupling
    for the total relation exists exactly when the two marginals carry the
    same amount of mass in the intended backends. *)
Polymorphic Definition sem_same_mass@{carrier representation}
    {S : Type@{carrier} -> Type@{representation}}
    `{SI : SemanticMeasureInterface S} {A B : Type@{carrier}}
    (mu : S A) (nu : S B) : Prop :=
  sem_lift (fun _ _ => True) mu nu.

Polymorphic Lemma sem_lift_same_mass@{carrier representation}
    {S : Type@{carrier} -> Type@{representation}}
    `{SI : SemanticMeasureInterface S}
    `{SL : @SemanticMeasureCoreLaws S SI}
    {A B : Type@{carrier}} (R : A -> B -> Prop) mu nu :
  sem_lift R mu nu -> sem_same_mass mu nu.
Proof.
  intro Hlift. eapply sem_lift_mono; [|exact Hlift].
  intros x y Hxy. exact I.
Qed.

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

(** A coupling can be replaced by one supported on predicates that hold
    almost everywhere in its two marginals.  This is the standard bridge
    from measure-theoretic AE invariants to pointwise relational coinduction;
    it is intentionally not bundled into the basic coupling algebra. *)
Polymorphic Class SemanticMeasureCouplingAELaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S} := {
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

(** Measures are closed under countable intersections of almost-everywhere
    predicates.  This is the measure-theoretic ingredient needed when an
    omega construction exposes one AE side condition at every finite
    approximation.  It is separate from finite conjunction so finite-state
    clients do not need to assume sigma-completeness. *)
Polymorphic Class SemanticMeasureCountableAELaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S} := {
  sem_ae_countable : forall {A : Type@{carrier}} (mu : S A)
      (P : nat -> A -> Prop),
    (forall n, sem_ae mu (P n)) ->
    sem_ae mu (fun x => forall n, P n x)
}.

(** Predicate semantics for the monadic operations.  These laws are kept
    separate from extensional equality and coupling: they are exactly the
    capability needed to propagate an invariant through a finite kernel
    computation. *)
Polymorphic Class SemanticMeasureAEKleisliLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S} := {
  sem_ae_ret : forall {A : Type@{carrier}} (P : A -> Prop) x,
      P x -> sem_ae (sem_ret x) P;
  sem_ae_bind : forall {A B : Type@{carrier}}
      (mu : S A) (k : A -> S B) (P : A -> Prop) (Q : B -> Prop),
      sem_ae mu P ->
      (forall x, P x -> sem_ae (k x) Q) ->
      sem_ae (sem_bind mu k) Q
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

(** Optional left-unit capability for a two-level measure backend.  It is
    intentionally separate from [MixedMeasureLaws]: a syntax-level free
    omega backend need not quotient a sampled node Dirac to its selected
    continuation unless that equation is explicitly part of its semantic
    quotient. *)
Polymorphic Class MixedMeasureUnitLaws@{node node_rep frontier frontier_rep}
    (MN : Type@{node} -> Type@{node_rep})
    (MF : Type@{frontier} -> Type@{frontier_rep})
    `{NI : SemanticMeasureInterface MN}
    `{FI : SemanticMeasureInterface MF}
    `{MX : MixedMeasureInterface MN MF} := {
  mixed_bind_ret_l : forall {A : Type@{node}} {B : Type@{frontier}}
      (x : A) (k : A -> MF B),
      sem_lift eq (mixed_bind (sem_ret x) k) (k x)
}.

(** Optional compatibility between node-level Kleisli composition and
    mixed binding into the frontier layer.  This is the semantic content of
    flattening two consecutive [Prob] nodes. *)
Polymorphic Class MixedMeasureNodeBindLaws@{node node_rep frontier frontier_rep}
    (MN : Type@{node} -> Type@{node_rep})
    (MF : Type@{frontier} -> Type@{frontier_rep})
    `{NI : SemanticMeasureInterface MN}
    `{FI : SemanticMeasureInterface MF}
    `{MX : MixedMeasureInterface MN MF} := {
  mixed_bind_node_assoc : forall
      {A B : Type@{node}} {C : Type@{frontier}}
      (mu : MN A) (h : A -> MN B) (k : B -> MF C),
      sem_lift eq
        (mixed_bind mu (fun x => mixed_bind (h x) k))
        (mixed_bind (sem_bind mu h) k)
}.

(** Relational Fubini law for one fixed pair of node measures. *)
Polymorphic Definition mixed_measure_exchange@{node node_rep frontier frontier_rep}
    {MN : Type@{node} -> Type@{node_rep}}
    {MF : Type@{frontier} -> Type@{frontier_rep}}
    `{NI : SemanticMeasureInterface MN}
    `{FI : SemanticMeasureInterface MF}
    `{MX : MixedMeasureInterface MN MF}
    {A B : Type@{node}} (mu : MN A) (nu : MN B) : Prop :=
  forall (C D : Type@{frontier}) (R : C -> D -> Prop)
    (k1 : A -> B -> MF C) (k2 : B -> A -> MF D),
    (forall x y, sem_lift R (k1 x y) (k2 y x)) ->
    sem_lift R
      (mixed_bind mu (fun x => mixed_bind nu (k1 x)))
      (mixed_bind nu (fun y => mixed_bind mu (k2 y))).

(** Uniform relational Fubini law across the node/frontier boundary.  It is
    kept optional because commutativity is not a law of every measure-like
    effect. *)
Polymorphic Class MixedMeasureCommutativeLaws@{node node_rep frontier frontier_rep}
    (MN : Type@{node} -> Type@{node_rep})
    (MF : Type@{frontier} -> Type@{frontier_rep})
    `{NI : SemanticMeasureInterface MN}
    `{FI : SemanticMeasureInterface MF}
    `{MX : MixedMeasureInterface MN MF} := {
  mixed_lift_exchange : forall {A B : Type@{node}}
      (mu : MN A) (nu : MN B), mixed_measure_exchange mu nu
}.

(** Exact almost-everywhere characterization of semantic Dirac measures.
    Positive AE introduction alone is insufficient to discard branches other
    than the selected point when quotienting a sampled Dirac. *)
Polymorphic Class SemanticMeasureDiracAELaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S} := {
  sem_ae_ret_iff : forall {A : Type@{carrier}} (x : A) (P : A -> Prop),
      sem_ae (sem_ret x) P <-> P x
}.

(** Exact support decomposition for node-level Kleisli bind.  The forward
    implication supplied by [SemanticMeasureAEKleisliLaws] is sufficient for
    many soundness arguments; quotienting one bound sample with two nested
    samples also needs this reverse characterization. *)
Polymorphic Class SemanticMeasureBindAEExactLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S} := {
  sem_ae_bind_iff : forall {A B : Type@{carrier}}
      (mu : S A) (k : A -> S B) (P : B -> Prop),
      sem_ae (sem_bind mu k) P <->
      sem_ae mu (fun x => sem_ae (k x) P)
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

Definition sem_zero_prefix {SM} `{SI : SemanticMeasureInterface SM}
    `{SO : @SemanticOmegaInterface SM SI} {A}
    (chain : nat -> SM A) : nat -> SM A :=
  fun n => match n with O => sem_zero | Datatypes.S n' => chain n' end.

(** Minimal order theory needed to show that primitive stable-hitting
    approximants form an increasing chain.  It is independent of omega-limit
    existence and can therefore be supplied by partial backends. *)
Polymorphic Class SemanticMeasureOrderLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S}
    `{SO : @SemanticOmegaInterface S SI} := {
  sem_le_refl : forall {A : Type@{carrier}} (mu : S A), sem_le mu mu;
  sem_le_trans : forall {A : Type@{carrier}} (mu nu xi : S A),
      sem_le mu nu -> sem_le nu xi -> sem_le mu xi;
  sem_zero_le : forall {A : Type@{carrier}} (mu : S A), sem_le sem_zero mu;
  sem_bind_le_mu : forall {A B : Type@{carrier}} (mu nu : S A)
      (k : A -> S B),
      sem_le mu nu -> sem_le (sem_bind mu k) (sem_bind nu k);
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

(** Almost-everywhere predicates are admissible for bottom and omega limits.
    Together with [SemanticMeasureAEKleisliLaws], this turns one-step AE
    kernel invariants into invariants of unbounded stable hitting. *)
Polymorphic Class SemanticOmegaAELaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S}
    `{SO : @SemanticOmegaInterface S SI} := {
  sem_ae_zero : forall {A : Type@{carrier}} (P : A -> Prop),
      sem_ae (@sem_zero S SI SO A) P;
  sem_ae_lub : forall {A : Type@{carrier}}
      (chain : nat -> S A) out (P : A -> Prop),
      sem_lub chain out ->
      (forall n, sem_ae (chain n) P) ->
      sem_ae out P
}.

(** Extensionality of almost-sure termination.  It is separated from omega
    completeness because a backend may support a relational limit without
    quotienting its concrete representation strongly enough to prove this
    law.  Operational AST transfer across denotational equality requires it
    explicitly. *)
Polymorphic Class SemanticTotalProperLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S}
    `{SO : @SemanticOmegaInterface S SI} := {
  sem_total_proper : forall {A : Type@{carrier}} (mu nu : S A),
      sem_eq mu nu -> (sem_total mu <-> sem_total nu)
}.

(** Cofinality needed for silent operational steps.  It is deliberately
    separate from ordinary omega completeness: a backend may provide formal
    lub syntax without quotienting away finite prefixes. *)
Polymorphic Class SemanticOmegaCofinalityLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S}
    `{SO : @SemanticOmegaInterface S SI} := {
  sem_lub_zero_prefix : forall {A : Type@{carrier}}
      (chain : nat -> S A) out,
      sem_lub chain out <-> sem_lub (sem_zero_prefix chain) out;
  sem_lub_constant : forall {A : Type@{carrier}} (mu : S A),
      sem_lub (fun _ => mu) mu
}.

(** Monotone convergence across the two measure levels.  This is the exact
    analytic capability needed to turn almost-everywhere branchwise weak
    limits into the weak limit of a primitive Prob transition. *)
Polymorphic Class MixedMeasureOmegaLaws@{node node_rep frontier frontier_rep}
    (MN : Type@{node} -> Type@{node_rep})
    (MF : Type@{frontier} -> Type@{frontier_rep})
    `{NI : SemanticMeasureInterface MN}
    `{FI : SemanticMeasureInterface MF}
    `{MX : MixedMeasureInterface MN MF}
    `{FO : @SemanticOmegaInterface MF FI} := {
  mixed_bind_zero : forall {A : Type@{node}} {B : Type@{frontier}}
      (mu : MN A),
      sem_eq (mixed_bind mu (fun _ => @sem_zero MF FI FO B)) sem_zero;
  mixed_bind_lub : forall {A : Type@{node}} {B : Type@{frontier}}
      (mu : MN A) (Good : A -> Prop)
      (chain : A -> nat -> MF B) (out : A -> MF B),
      sem_ae mu Good ->
      (forall x, Good x -> sem_increasing (chain x)) ->
      (forall x, Good x -> sem_lub (chain x) (out x)) ->
      sem_lub (fun n => mixed_bind mu (fun x => chain x n))
        (mixed_bind mu out)
}.

(** Joint continuity for a growing source measure and growing continuation
    kernels.  This is stronger than [sem_bind_lub], whose kernel is fixed,
    and is exactly the measure-level half of operational Bind soundness. *)
Polymorphic Class SemanticMeasureDiagonalLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S}
    `{SO : @SemanticOmegaInterface S SI} := {
  sem_bind_diagonal_lub : forall {A B : Type@{carrier}}
      (source : nat -> S A) (source_out : S A)
      (kernels : A -> nat -> S B) (kernel_out : A -> S B),
      sem_increasing source ->
      (forall x, sem_increasing (kernels x)) ->
      sem_lub source source_out ->
      (forall x, sem_lub (kernels x) (kernel_out x)) ->
      sem_lub
        (fun n => sem_bind (source n) (fun x => kernels x n))
        (sem_bind source_out kernel_out)
}.

(** Fubini/diagonal continuity for two independent approximation indices.
    This is the semantic capability required by genuinely nested unbounded
    computation.  It is intentionally stronger than finite cofinality: an
    inner AST sampler need not expose its complete output at any finite
    fuel, so no finite maximum can replace this double-limit law.

    Monotonicity in both coordinates makes the diagonal chain cofinal in the
    product order.  Backends based on ordinary subprobability measures can
    discharge this with monotone convergence; formal completions may instead
    provide it through their observation quotient. *)
Polymorphic Class SemanticOmegaFubiniLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasureInterface S}
    `{SO : @SemanticOmegaInterface S SI} := {
  sem_lub_double_diagonal : forall {A : Type@{carrier}}
      (grid : nat -> nat -> S A)
      (row_out : nat -> S A) (out : S A),
      (forall outer, sem_increasing (grid outer)) ->
      (forall inner, sem_increasing (fun outer => grid outer inner)) ->
      (forall outer, sem_lub (grid outer) (row_out outer)) ->
      sem_lub row_out out ->
      sem_lub (fun fuel => grid fuel fuel) out
}.

#[global] Polymorphic Instance sem_eq_equivalence
    {S} `{SI : SemanticMeasureInterface S}
    `{SL : @SemanticMeasureCoreLaws S SI} A :
  Equivalence (@sem_eq S SI A).
Proof.
  split; [apply sem_eq_refl | apply sem_eq_sym | apply sem_eq_trans].
Qed.
