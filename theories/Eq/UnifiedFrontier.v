(** Role: Canonical equational/hitting theory. Depends on Core and Prob; does not provide comparison or interpreter semantics. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Utf8.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Stable observations for the two-level semantics.  The probability tree
    stores only node measures [MN]; the surrounding semantic measure [MF]
    never appears recursively in the tree. *)
Variant stable_head (E : Type -> Type) (MN : Type -> Type)
    (R : Type) : Type :=
  | FHRet (r : R)
  | FHVis {X : Type} (e : E X) (k : X -> ptree E MN R).

Arguments FHRet {E MN R} _.
Arguments FHVis {E MN R X} _ _.

(** Relational lifting of stable Ret/Vis observations.  This belongs to the
    stable-observation layer, independently of any particular behavioral
    greatest fixed point. *)
Section StableHeadRelation.
Context {E : Type -> Type} {MN : Type -> Type} {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Inductive stable_head_rel
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop) :
    stable_head E MN R1 -> stable_head E MN R2 -> Prop :=
  | FHRRet r1 r2 : RR r1 r2 ->
      stable_head_rel sim (FHRet r1) (FHRet r2)
  | FHRVis {X : Type} (e : E X) k1 k2 :
      (forall x, sim (k1 x) (k2 x)) ->
      stable_head_rel sim (FHVis e k1) (FHVis e k2).

Lemma stable_head_rel_mono sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall h1 h2,
    stable_head_rel sim1 h1 h2 -> stable_head_rel sim2 h1 h2.
Proof.
  intros Hsim h1 h2 Hh. inversion Hh; subst; constructor; auto.
Qed.

End StableHeadRelation.

Definition stable_head_bind_front {E MN MF}
    `{FI : SemanticMeasure MF} {A B}
    (k : A -> ptree E MN B)
    (front : A -> MF (stable_head E MN B))
    (h : stable_head E MN A) : MF (stable_head E MN B) :=
  match h with
  | FHRet a => front a
  | @FHVis _ _ _ X e c =>
      sem_ret (FHVis e (fun x => PTree.bind (c x) k))
  end.

Section MixedIteration.
Context {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.

(** Finite absorbing approximants already live in the stable-head layer.  A
    source transition is a node measure, so every unfolding uses the mixed
    bind rather than assuming [MN = MF]. *)
Fixpoint mixed_iter_approx {I R} (n : nat)
    (transition : I -> MN (I + R)) (i : I) : MF R :=
  match n with
  | O => sem_zero
  | Datatypes.S n' =>
      mixed_bind (transition i) (fun next =>
        match next with
        | inl i' => mixed_iter_approx n' transition i'
        | inr r => sem_ret r
        end)
  end.

Definition mixed_iter {I R} (transition : I -> MN (I + R))
    (i : I) (out : MF R) : Prop :=
  sem_lub (fun n => mixed_iter_approx n transition i) out.

End MixedIteration.

(** A syntax-directed stable-frontier certificate judgment.  Finite internal
    computation is not
    wrapped in a separate [AUFFinite] constructor: [Ret]/[Vis]/[Tau]/[Prob]
    are native rules of this relation.  [UFIter] adds an AST omega proof for
    syntactic iteration without changing the observable result type. *)
Section UnifiedFrontier.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.

Inductive frontier_certificate {R} :
    ptree' E MN R -> MF (stable_head E MN R) -> Prop :=
  | UFRet r :
      frontier_certificate (RetF r) (sem_ret (FHRet r))
  | UFVis {X : Type} (e : E X) k :
      frontier_certificate (VisF e k) (sem_ret (FHVis e k))
  | UFTau t hs :
      frontier_certificate (observe t) hs ->
      frontier_certificate (TauF t) hs
  | UFProb {X : Type} (mu : MN X) k
      (front : X -> MF (stable_head E MN R))
      (Good : X -> Prop) :
      sem_ae mu Good ->
      (forall x, Good x -> frontier_certificate (observe (k x)) (front x)) ->
      frontier_certificate (ProbF mu k) (mixed_bind mu front)
  | UFIter {I : Type}
      (step : I -> ptree E MN (I + R))
      (transition : I -> MN (I + R)) i out :
      (forall j,
        frontier_certificate (observe (step j))
          (mixed_bind (transition j)
            (fun next => sem_ret (FHRet next)))) ->
      mixed_iter transition i out ->
      sem_total out ->
      frontier_certificate (observe (PTree.iter step i))
        (sem_bind out (fun r => sem_ret (FHRet r)))
  | UFBind {A : Type}
      (t : ptree E MN A) (k : A -> ptree E MN R)
      hs (front : A -> MF (stable_head E MN R)) :
      frontier_certificate (observe t) hs ->
      (forall a, frontier_certificate (observe (k a)) (front a)) ->
      frontier_certificate (observe (PTree.bind t k))
        (sem_bind hs (stable_head_bind_front k front)).

(** Coherence is the exact semantic condition needed to treat a certificate as
    an observation rather than a chosen derivation.  Omega-limit uniqueness
    and continuity should discharge [certificate_unique] for concrete
    backends; Tau inversion records that adding one silent step creates no
    new observation.  Keeping this package explicit prevents transitivity
    from assuming canonical representatives. *)
Class UnifiedFrontierCoherence := {
  unified_frontier_unique : forall {R}
      (ot : ptree' E MN R) hs1 hs2,
      frontier_certificate ot hs1 -> frontier_certificate ot hs2 -> sem_eq hs1 hs2;
  unified_frontier_tau_inv : forall {R}
      (t : ptree E MN R) hs,
      frontier_certificate (TauF t) hs -> frontier_certificate (observe t) hs
}.

(** Opaque introduction wrapper for clients with large analytic measure
    terms.  It avoids re-elaborating the dependent [UFIter] constructor and
    its universe arguments at every use site. *)
Lemma certificate_iter_intro {R I}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) i out :
  (forall j,
    frontier_certificate (observe (step j))
      (mixed_bind (transition j)
        (fun next => sem_ret (FHRet next)))) ->
  mixed_iter transition i out ->
  sem_total out ->
  frontier_certificate (observe (PTree.iter step i))
    (sem_bind out (fun r => sem_ret (FHRet r))).
Proof. intros Hstep Hiter Htotal. eapply UFIter; eassumption. Qed.

End UnifiedFrontier.
