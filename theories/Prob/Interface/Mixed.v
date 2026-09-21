(** Role: Native-to-behavior bridge and its optional unit, bind, exchange and omega laws. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Omega.


(** The two-level bridge.  [MN] is the measure stored by a [Prob] node;
    [MF] is the measure of stable heads and residual semantic states.  The
    mixed bind is exactly the operation used by the probabilistic frontier
    rule. *)
Polymorphic Class MixedMeasure@{node node_rep frontier frontier_rep}
    (MN : Type@{node} -> Type@{node_rep})
    (MF : Type@{frontier} -> Type@{frontier_rep}) := {
  mixed_bind : forall {A : Type@{node}} {B : Type@{frontier}},
      MN A -> (A -> MF B) -> MF B
}.

(** Laws connecting the node and frontier layers.  AE lives at the node
    layer, while equality and couplings of continuations live at the
    frontier layer. *)
Polymorphic Class MixedMeasureLaws@{node node_rep frontier frontier_rep}
    (MN : Type@{node} -> Type@{node_rep})
    (MF : Type@{frontier} -> Type@{frontier_rep})
    `{NI : SemanticMeasure MN}
    `{FI : SemanticMeasure MF}
    `{MX : MixedMeasure MN MF} := {
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
    `{NI : SemanticMeasure MN}
    `{FI : SemanticMeasure MF}
    `{MX : MixedMeasure MN MF} := {
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
    `{NI : SemanticMeasure MN}
    `{FI : SemanticMeasure MF}
    `{MX : MixedMeasure MN MF} := {
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
    `{NI : SemanticMeasure MN}
    `{FI : SemanticMeasure MF}
    `{MX : MixedMeasure MN MF}
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
    `{NI : SemanticMeasure MN}
    `{FI : SemanticMeasure MF}
    `{MX : MixedMeasure MN MF} := {
  mixed_lift_exchange : forall {A B : Type@{node}}
      (mu : MN A) (nu : MN B), mixed_measure_exchange mu nu
}.

(** Monotone convergence across the two measure levels.  This is the exact
    analytic capability needed to turn almost-everywhere branchwise weak
    limits into the weak limit of a primitive Prob transition. *)
Polymorphic Class MixedMeasureOmegaLaws@{node node_rep frontier frontier_rep}
    (MN : Type@{node} -> Type@{node_rep})
    (MF : Type@{frontier} -> Type@{frontier_rep})
    `{NI : SemanticMeasure MN}
    `{FI : SemanticMeasure MF}
    `{MX : MixedMeasure MN MF}
    `{FO : @SemanticOmega MF FI} := {
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
