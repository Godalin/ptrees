Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Utf8.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Stable observations for the two-level semantics.  The probability tree
    stores only node measures [MN]; the surrounding semantic measure [MF]
    never appears recursively in the tree. *)
Variant frontier_head (E : Type -> Type) (MN : Type -> Type)
    (R : Type) : Type :=
  | FHRet (r : R)
  | FHVis {X : Type} (e : E X) (k : X -> ptree E MN R).

Arguments FHRet {E MN R} _.
Arguments FHVis {E MN R X} _ _.

Definition frontier_head_bind_front {E MN MF}
    `{FI : SemanticMeasureInterface MF} {A B}
    (k : A -> ptree E MN B)
    (front : A -> MF (frontier_head E MN B))
    (h : frontier_head E MN A) : MF (frontier_head E MN B) :=
  match h with
  | FHRet a => front a
  | @FHVis _ _ _ X e c =>
      sem_ret (FHVis e (fun x => PTree.bind (c x) k))
  end.

Section MixedIteration.
Context {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

(** Finite absorbing approximants already live in the frontier layer.  A
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

(** A single public frontier judgment.  Finite internal computation is not
    wrapped in a separate [AUFFinite] constructor: [Ret]/[Vis]/[Tau]/[Prob]
    are native rules of this relation.  [UFIter] adds an AST omega proof for
    syntactic iteration without changing the observable result type. *)
Section UnifiedFrontier.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

Inductive frontier {R} :
    ptree' E MN R -> MF (frontier_head E MN R) -> Prop :=
  | UFRet r :
      frontier (RetF r) (sem_ret (FHRet r))
  | UFVis {X : Type} (e : E X) k :
      frontier (VisF e k) (sem_ret (FHVis e k))
  | UFTau t hs :
      frontier (observe t) hs ->
      frontier (TauF t) hs
  | UFProb {X : Type} (mu : MN X) k
      (front : X -> MF (frontier_head E MN R))
      (Good : X -> Prop) :
      sem_ae mu Good ->
      (forall x, Good x -> frontier (observe (k x)) (front x)) ->
      frontier (ProbF mu k) (mixed_bind mu front)
  | UFIter {I : Type}
      (step : I -> ptree E MN (I + R))
      (transition : I -> MN (I + R)) i out :
      (forall j,
        frontier (observe (step j))
          (mixed_bind (transition j)
            (fun next => sem_ret (FHRet next)))) ->
      mixed_iter transition i out ->
      sem_total out ->
      frontier (observe (PTree.iter step i))
        (sem_bind out (fun r => sem_ret (FHRet r)))
  | UFBind {A : Type}
      (t : ptree E MN A) (k : A -> ptree E MN R)
      hs (front : A -> MF (frontier_head E MN R)) :
      frontier (observe t) hs ->
      (forall a, frontier (observe (k a)) (front a)) ->
      frontier (observe (PTree.bind t k))
        (sem_bind hs (frontier_head_bind_front k front))
  | UFNestedIter {I : Type}
      (step : I -> ptree E MN (I + R))
      (transition : I -> MN (I + R)) i out :
      (forall j,
        frontier (observe (step j))
          (mixed_bind (transition j)
            (fun next => sem_ret (FHRet next)))) ->
      mixed_iter transition i out ->
      sem_total out ->
      frontier (observe (PTree.iter step i))
        (sem_bind out (fun r => sem_ret (FHRet r))).

End UnifiedFrontier.
