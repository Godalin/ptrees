(** Role: Interpreter compositionality. Depends on equational theory (and comparison semantics for Atomic/MDP); not primitive syntax. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import FrontierLift TwoLevelMeasure.
From PTree.Eq Require Import Shallow.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "` R" := (elem R) (at level 10).

From PTree.Eq Require Import PStruct.
Section PStructInterp.
Context {E F : Type -> Type} {M : Type -> Type}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.
Variable handler : forall X, E X -> ptree F M X.

Inductive pstruct_interp_clo :
    ptree F M R1 -> ptree F M R2 -> Prop :=
  | PStInterpMain t1 t2 :
      pstruct RR t1 t2 ->
      pstruct_interp_clo
        (PTree.interp handler t1) (PTree.interp handler t2)
  | PStInterpBind {X} (source : ptree F M X)
      (k1 : X -> ptree E M R1) (k2 : X -> ptree E M R2) :
      (forall x, pstruct RR (k1 x) (k2 x)) ->
      pstruct_interp_clo
        (PTree.bind source (fun x => PTree.interp handler (k1 x)))
        (PTree.bind source (fun x => PTree.interp handler (k2 x)))
  | PStInterpDone u1 u2 :
      pstruct RR u1 u2 -> pstruct_interp_clo u1 u2.

Theorem pstruct_interp (t1 : ptree E M R1) (t2 : ptree E M R2) :
  pstruct RR t1 t2 ->
  pstruct RR (PTree.interp handler t1) (PTree.interp handler t2).
Proof.
  intro Hsource.
  assert (Hinterp : forall u1 u2, pstruct_interp_clo u1 u2 ->
      pstruct RR u1 u2).
  { unfold pstruct. coinduction CH CIH.
    intros u1 u2 Hclo. inversion Hclo; subst.
    - unfold pstruct_body.
      change (pstructF RR (` CH)
        (observe (PTree.interp handler t0))
        (observe (PTree.interp handler t3))).
      rewrite !observe_interp.
      pose proof (pstruct_unfold H) as Hstep.
      dependent destruction Hstep.
      + rewrite <- x0. rewrite <- x. cbn. constructor. exact H0.
      + rewrite <- x0. rewrite <- x. cbn.
        constructor. apply CIH. constructor. exact H0.
      + rewrite <- x0. rewrite <- x. cbn.
        constructor. apply CIH. constructor. intro y. exact (H0 y).
      + rewrite <- x0. rewrite <- x. cbn.
        constructor=> y. apply CIH. constructor. exact (H0 y).
    - unfold pstruct_body.
      change (pstructF RR (` CH)
        (observe (PTree.bind source
          (fun x => PTree.interp handler (k1 x))))
        (observe (PTree.bind source
          (fun x => PTree.interp handler (k2 x))))).
      rewrite !observe_bind.
      remember (observe source) as os eqn:Hos.
      destruct os as [x|source'|Y e c|Y mu c]; cbn.
      + rewrite !observe_interp.
        pose proof (pstruct_unfold (H x)) as Hstep.
        dependent destruction Hstep.
        * rewrite <- x1. rewrite <- x. cbn. constructor. exact H0.
        * rewrite <- x1. rewrite <- x. cbn.
          constructor. apply CIH. constructor. exact H0.
        * rewrite <- x1. rewrite <- x. cbn.
          constructor. apply CIH. constructor. intro z. exact (H0 z).
        * rewrite <- x1. rewrite <- x. cbn.
          constructor=> z. apply CIH. constructor. exact (H0 z).
      + constructor. apply CIH. constructor. exact H.
      + constructor=> y. apply CIH. constructor. exact H.
      + constructor=> y. apply CIH. constructor. exact H.
    - unfold pstruct_body.
      pose proof (pstruct_unfold H) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  apply Hinterp. constructor. exact Hsource.
Qed.

End PStructInterp.

Section PStructInterpBind.
Context {E F : Type -> Type} {M : Type -> Type}.
Context {A B : Type}.
Variable handler : forall X, E X -> ptree F M X.

Inductive pstruct_interp_bind_clo :
    ptree F M B -> ptree F M B -> Prop :=
  | PStInterpBindMain (t : ptree E M A) (k : A -> ptree E M B) :
      pstruct_interp_bind_clo
        (PTree.interp handler (PTree.bind t k))
        (PTree.bind (PTree.interp handler t)
          (fun x => PTree.interp handler (k x)))
  | PStInterpBindHandler {X} (source : ptree F M X)
      (c : X -> ptree E M A) (k : A -> ptree E M B) :
      pstruct_interp_bind_clo
        (PTree.bind source
          (fun x => PTree.interp handler (PTree.bind (c x) k)))
        (PTree.bind
          (PTree.bind source (fun x => PTree.interp handler (c x)))
          (fun y => PTree.interp handler (k y)))
  | PStInterpBindDone (u v : ptree F M B) :
      pstruct eq u v -> pstruct_interp_bind_clo u v.

Theorem pstruct_interp_bind (t : ptree E M A)
    (k : A -> ptree E M B) :
  pstruct eq
    (PTree.interp handler (PTree.bind t k))
    (PTree.bind (PTree.interp handler t)
      (fun x => PTree.interp handler (k x))).
Proof.
  assert (Hstrong : forall u v, pstruct_interp_bind_clo u v ->
      pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo. inversion Hclo; subst.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.interp handler (PTree.bind t0 k0)))
        (observe (PTree.bind (PTree.interp handler t0)
          (fun x => PTree.interp handler (k0 x))))).
      rewrite observe_interp. rewrite !observe_bind. rewrite observe_interp.
      remember (observe t0) as ot eqn:Hot.
      destruct ot as [a|t'|X e c|X mu c]; cbn.
      + rewrite <- observe_interp.
        pose proof (pstruct_unfold
          (pstruct_refl (PTree.interp handler (k0 a)))) as Hrefl.
        eapply pstructF_monotone; [|exact Hrefl].
        intros x y Hxy. apply CIH. constructor. exact Hxy.
      + constructor. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind source
          (fun x => PTree.interp handler (PTree.bind (c x) k0))))
        (observe (PTree.bind
          (PTree.bind source (fun x => PTree.interp handler (c x)))
          (fun y => PTree.interp handler (k0 y))))).
      rewrite !observe_bind.
      remember (observe source) as os eqn:Hos.
      destruct os as [x|source'|Y e d|Y mu d]; cbn.
      + rewrite observe_interp. rewrite !observe_bind. rewrite observe_interp.
        remember (observe (c x)) as oc eqn:Hoc.
        destruct oc as [a|c'|Z e' d'|Z mu' d']; cbn.
        * rewrite <- observe_interp.
          pose proof (pstruct_unfold
            (pstruct_refl (PTree.interp handler (k0 a)))) as Hrefl.
          eapply pstructF_monotone; [|exact Hrefl].
          intros p q Hpq. apply CIH. constructor. exact Hpq.
        * constructor. apply CIH. constructor.
        * constructor. apply CIH. constructor.
        * constructor=> z. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> y. apply CIH. constructor.
      + constructor=> y. apply CIH. constructor.
    - unfold pstruct_body.
      pose proof (pstruct_unfold H) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  apply Hstrong. constructor.
Qed.

End PStructInterpBind.

Section PStructInterpIter.
Context {E F : Type -> Type} {M : Type -> Type}.
Context {I R : Type}.
Variable handler : forall X, E X -> ptree F M X.
Variable step : I -> ptree E M (I + R).

Definition pstruct_interp_iter_source_cont
    (lr : I + R) : ptree E M R :=
  match lr with
  | inl i => Tau (PTree.iter step i)
  | inr r => Ret r
  end.

Definition pstruct_interp_iter_target_step
    (i : I) : ptree F M (I + R) :=
  PTree.interp handler (step i).

Definition pstruct_interp_iter_target_cont
    (lr : I + R) : ptree F M R :=
  match lr with
  | inl i => Tau (PTree.iter pstruct_interp_iter_target_step i)
  | inr r => Ret r
  end.

Inductive pstruct_interp_iter_clo :
    ptree F M R -> ptree F M R -> Prop :=
  | PStInterpIterMain i :
      pstruct_interp_iter_clo
        (PTree.interp handler (PTree.iter step i))
        (PTree.iter pstruct_interp_iter_target_step i)
  | PStInterpIterSource (t : ptree E M (I + R)) :
      pstruct_interp_iter_clo
        (PTree.interp handler
          (PTree.bind t pstruct_interp_iter_source_cont))
        (PTree.bind (PTree.interp handler t)
          pstruct_interp_iter_target_cont)
  | PStInterpIterHandler {X} (source : ptree F M X)
      (c : X -> ptree E M (I + R)) :
      pstruct_interp_iter_clo
        (PTree.bind source (fun x => PTree.interp handler
          (PTree.bind (c x) pstruct_interp_iter_source_cont)))
        (PTree.bind
          (PTree.bind source (fun x => PTree.interp handler (c x)))
          pstruct_interp_iter_target_cont)
  | PStInterpIterDone (u v : ptree F M R) :
      pstruct eq u v -> pstruct_interp_iter_clo u v.

(** Interpretation commutes with guarded iteration.  The proof is purely
    structural: the joint invariant records the source loop, the bind
    exposed by one loop unfolding, and the extra bind introduced when an
    effectful handler runs. *)
Theorem pstruct_interp_iter i :
  pstruct eq
    (PTree.interp handler (PTree.iter step i))
    (PTree.iter pstruct_interp_iter_target_step i).
Proof.
  assert (Hstrong : forall u v, pstruct_interp_iter_clo u v ->
      pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo. inversion Hclo; subst.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.interp handler (PTree.iter step i0)))
        (observe (PTree.iter pstruct_interp_iter_target_step i0))).
      rewrite observe_interp.
      rewrite (observing_observe (unfold_aloop_ step i0)).
      rewrite (observing_observe
        (unfold_aloop_ pstruct_interp_iter_target_step i0)).
      rewrite !observe_bind. rewrite observe_interp.
      remember (observe (step i0)) as ot eqn:Hot.
      destruct ot as [lr|t'|X e c|X mu c]; cbn.
      + destruct lr as [j|r]; cbn [pstruct_interp_iter_source_cont
          pstruct_interp_iter_target_cont].
        * constructor. apply CIH. constructor.
        * constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.interp handler
          (PTree.bind t pstruct_interp_iter_source_cont)))
        (observe (PTree.bind (PTree.interp handler t)
          pstruct_interp_iter_target_cont))).
      rewrite observe_interp. rewrite !observe_bind. rewrite observe_interp.
      remember (observe t) as ot eqn:Hot.
      destruct ot as [lr|t'|X e c|X mu c]; cbn.
      + destruct lr as [j|r]; cbn [pstruct_interp_iter_source_cont
          pstruct_interp_iter_target_cont].
        * constructor. apply CIH. constructor.
        * constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind source (fun x => PTree.interp handler
          (PTree.bind (c x) pstruct_interp_iter_source_cont))))
        (observe (PTree.bind
          (PTree.bind source (fun x => PTree.interp handler (c x)))
          pstruct_interp_iter_target_cont))).
      rewrite !observe_bind.
      remember (observe source) as os eqn:Hos.
      destruct os as [x|source'|Y e d|Y mu d]; cbn.
      + rewrite observe_interp. rewrite !observe_bind. rewrite observe_interp.
        remember (observe (c x)) as oc eqn:Hoc.
        destruct oc as [lr|c'|Z e' d'|Z mu' d']; cbn.
        * destruct lr as [j|r]; cbn
              [pstruct_interp_iter_source_cont
               pstruct_interp_iter_target_cont].
          -- constructor. apply CIH. constructor.
          -- constructor. reflexivity.
        * constructor. apply CIH. constructor.
        * constructor. apply CIH. constructor.
        * constructor=> z. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> y. apply CIH. constructor.
      + constructor=> y. apply CIH. constructor.
    - unfold pstruct_body.
      pose proof (pstruct_unfold H) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  apply Hstrong. constructor.
Qed.

End PStructInterpIter.

Section PStructInterpCompose.
Context {E F G : Type -> Type} {M : Type -> Type}.
Context {R : Type}.
Variable handler1 : forall X, E X -> ptree F M X.
Variable handler2 : forall X, F X -> ptree G M X.

Definition pstruct_interp_compose_handler
    (X : Type) (e : E X) : ptree G M X :=
  PTree.interp handler2 (handler1 e).

Inductive pstruct_interp_compose_clo :
    ptree G M R -> ptree G M R -> Prop :=
  | PStInterpComposeMain (t : ptree E M R) :
      pstruct_interp_compose_clo
        (PTree.interp handler2 (PTree.interp handler1 t))
        (PTree.interp pstruct_interp_compose_handler t)
  | PStInterpComposeBind {X} (source : ptree F M X)
      (k : X -> ptree E M R) :
      pstruct_interp_compose_clo
        (PTree.interp handler2
          (PTree.bind source (fun x => PTree.interp handler1 (k x))))
        (PTree.bind (PTree.interp handler2 source)
          (fun x => PTree.interp pstruct_interp_compose_handler (k x)))
  | PStInterpComposeHandler {X} (source : ptree G M X)
      {Y} (c : X -> ptree F M Y) (k : Y -> ptree E M R) :
      pstruct_interp_compose_clo
        (PTree.bind source (fun x => PTree.interp handler2
          (PTree.bind (c x) (fun y => PTree.interp handler1 (k y)))))
        (PTree.bind
          (PTree.bind source (fun x => PTree.interp handler2 (c x)))
          (fun y => PTree.interp pstruct_interp_compose_handler (k y)))
  | PStInterpComposeDone (u v : ptree G M R) :
      pstruct eq u v -> pstruct_interp_compose_clo u v.

(** Sequential effect handlers compose.  Both handlers are arbitrary
    PTrees; in particular their execution may contain Tau, Vis, and Prob. *)
Theorem pstruct_interp_compose (t : ptree E M R) :
  pstruct eq
    (PTree.interp handler2 (PTree.interp handler1 t))
    (PTree.interp pstruct_interp_compose_handler t).
Proof.
  assert (Hstrong : forall u v, pstruct_interp_compose_clo u v ->
      pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo. inversion Hclo; subst.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.interp handler2 (PTree.interp handler1 t0)))
        (observe (PTree.interp pstruct_interp_compose_handler t0))).
      rewrite !observe_interp.
      remember (observe t0) as ot eqn:Hot.
      destruct ot as [r|t'|X e k|X mu k]; cbn.
      + constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.interp handler2
          (PTree.bind source (fun x => PTree.interp handler1 (k x)))))
        (observe (PTree.bind (PTree.interp handler2 source)
          (fun x => PTree.interp pstruct_interp_compose_handler (k x))))).
      rewrite observe_interp. rewrite !observe_bind. rewrite observe_interp.
      remember (observe source) as os eqn:Hos.
      destruct os as [x|source'|Y e c|Y mu c]; cbn.
      + rewrite !observe_interp.
        remember (observe (k x)) as ok eqn:Hok.
        destruct ok as [r|k'|Z e' d|Z mu' d]; cbn.
        * constructor. reflexivity.
        * constructor. apply CIH. constructor.
        * constructor. apply CIH. constructor.
        * constructor=> z. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> y. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind source (fun x => PTree.interp handler2
          (PTree.bind (c x) (fun y => PTree.interp handler1 (k y))))))
        (observe (PTree.bind
          (PTree.bind source (fun x => PTree.interp handler2 (c x)))
          (fun y => PTree.interp pstruct_interp_compose_handler (k y))))).
      rewrite !observe_bind.
      remember (observe source) as os eqn:Hos.
      destruct os as [x|source'|Z e d|Z mu d]; cbn.
      + rewrite observe_interp. rewrite !observe_bind. rewrite observe_interp.
        remember (observe (c x)) as oc eqn:Hoc.
        destruct oc as [y|c'|W e' d'|W mu' d']; cbn.
        * rewrite !observe_interp.
          remember (observe (k y)) as ok eqn:Hok.
          destruct ok as [r|k'|V e'' q|V mu'' q]; cbn.
          -- constructor. reflexivity.
          -- constructor. apply CIH. constructor.
          -- constructor. apply CIH. constructor.
          -- constructor=> z. apply CIH. constructor.
        * constructor. apply CIH. constructor.
        * constructor. apply CIH. constructor.
        * constructor=> z. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> z. apply CIH. constructor.
      + constructor=> z. apply CIH. constructor.
    - unfold pstruct_body.
      pose proof (pstruct_unfold H) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  apply Hstrong. constructor.
Qed.

End PStructInterpCompose.

Section PStructInterpHandlerCongruence.
Context {E F : Type -> Type} {M : Type -> Type}.
Context {R : Type}.
Variable handler1 handler2 : forall X, E X -> ptree F M X.
Hypothesis handlers_related : forall X (e : E X),
  pstruct eq (@handler1 X e) (@handler2 X e).

Inductive pstruct_interp_handler_clo :
    ptree F M R -> ptree F M R -> Prop :=
  | PStInterpHandlerMain (t : ptree E M R) :
      pstruct_interp_handler_clo
        (PTree.interp handler1 t) (PTree.interp handler2 t)
  | PStInterpHandlerBind {X}
      (source1 source2 : ptree F M X) (k : X -> ptree E M R) :
      pstruct eq source1 source2 ->
      pstruct_interp_handler_clo
        (PTree.bind source1 (fun x => PTree.interp handler1 (k x)))
        (PTree.bind source2 (fun x => PTree.interp handler2 (k x)))
  | PStInterpHandlerDone (u v : ptree F M R) :
      pstruct eq u v -> pstruct_interp_handler_clo u v.

(** Pointwise structurally equivalent effect handlers induce structurally
    equivalent interpretations.  Handler computations may themselves use
    Tau, Vis, and Prob. *)
Theorem pstruct_interp_handler (t : ptree E M R) :
  pstruct eq (PTree.interp handler1 t) (PTree.interp handler2 t).
Proof.
  assert (Hstrong : forall u v, pstruct_interp_handler_clo u v ->
      pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo. inversion Hclo; subst.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.interp handler1 t0))
        (observe (PTree.interp handler2 t0))).
      rewrite !observe_interp.
      remember (observe t0) as ot eqn:Hot.
      destruct ot as [r|t'|X e k|X mu k]; cbn.
      + constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + constructor. apply CIH. constructor. apply handlers_related.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind source1
          (fun x => PTree.interp handler1 (k x))))
        (observe (PTree.bind source2
          (fun x => PTree.interp handler2 (k x))))).
      rewrite !observe_bind.
      pose proof (pstruct_unfold H) as Hstep.
      dependent destruction Hstep.
      + rewrite <- x0, <- x. cbn. rewrite !observe_interp.
        remember (observe (k r2)) as ok eqn:Hok.
        destruct ok as [r|k'|Y e d|Y mu d]; cbn.
        * constructor. reflexivity.
        * constructor. apply CIH. constructor.
        * constructor. apply CIH. constructor. apply handlers_related.
        * constructor=> y. apply CIH. constructor.
      + rewrite <- x0, <- x. cbn. constructor. apply CIH. constructor. exact H0.
      + rewrite <- x0, <- x. cbn. constructor=> y.
        apply CIH. constructor. exact (H0 y).
      + rewrite <- x0, <- x. cbn. constructor=> y.
        apply CIH. constructor. exact (H0 y).
    - unfold pstruct_body.
      pose proof (pstruct_unfold H) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  apply Hstrong. constructor.
Qed.

End PStructInterpHandlerCongruence.
