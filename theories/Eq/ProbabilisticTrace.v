Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Program.Equality.
From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting
  OperationalProbabilisticPTS ProbabilisticEutt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A lightweight quantitative observation layer for eventful PTree
    behavior.  A query classifies the next stable Ret/Vis head and pushes
    that value through the semantic measure.  In particular, choosing
    [O := bool] gives the subprobability of a return or visible-event class;
    no numeric representation is required by the generic theory. *)
Section StableHeadObservation.
Context {E : Type -> Type} {MN : Type -> Type}.

Definition observe_stable_head {R O}
    (on_ret : R -> O) (on_vis : forall X, E X -> O)
    (h : frontier_head E MN R) : O :=
  match h with
  | FHRet r => on_ret r
  | @FHVis _ _ _ X e _ => on_vis X e
  end.

Lemma observe_stable_head_related {R1 R2 O}
    (RR : R1 -> R2 -> Prop)
    (on_ret1 : R1 -> O) (on_ret2 : R2 -> O)
    (on_vis : forall X, E X -> O)
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop) h1 h2 :
  (forall r1 r2, RR r1 r2 -> on_ret1 r1 = on_ret2 r2) ->
  frontier_head_rel RR sim h1 h2 ->
  observe_stable_head on_ret1 on_vis h1 =
    observe_stable_head on_ret2 on_vis h2.
Proof.
  intros Hret Hhead. dependent destruction Hhead; cbn; auto.
Qed.

End StableHeadObservation.

Section ProbabilisticHeadQuery.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

(** A query result is itself a semantic subprobability measure.  This is a
    weakest-preexpectation-style interface with indicator/result carrier
    [O], retaining missing mass and postponing numeric integration to a
    concrete backend such as Enum or MathComp. *)
Definition probabilistic_head_query {R O}
    (on_ret : R -> O) (on_vis : forall X, E X -> O)
    (t : ptree E MN R) (query : MF O) : Prop :=
  exists out : MF (frontier_head E MN R),
    stable_hitting_weak
      (@ptree_primitive_kernel E MN MF FI MX R) (observe t) out /\
    sem_eq
      (sem_bind out
        (fun h => sem_ret (observe_stable_head on_ret on_vis h)))
      query.

(** Canonical equivalence preserves every next-stable-head query whose
    return observations respect [RR].  Visible observations automatically
    agree because [frontier_head_rel] matches the same dependent event.
    The conclusion is coupling equality of query measures, which concrete
    backends turn into equality of probabilities/expectations. *)
Theorem probabilistic_eutt_preserves_head_query {R1 R2 O}
    (RR : R1 -> R2 -> Prop)
    (on_ret1 : R1 -> O) (on_ret2 : R2 -> O)
    (on_vis : forall X, E X -> O)
    (Hret : forall r1 r2, RR r1 r2 -> on_ret1 r1 = on_ret2 r2)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) query1 :
  probabilistic_eutt RR t1 t2 ->
  probabilistic_head_query on_ret1 on_vis t1 query1 ->
  exists query2,
    probabilistic_head_query on_ret2 on_vis t2 query2 /\
    sem_lift eq query1 query2.
Proof.
  intros Heutt [out1 [Hhit1 Hquery1]].
  apply probabilistic_eutt_unfold in Heutt.
  destruct Heutt as [Hforward _].
  destruct (Hforward out1 Hhit1) as [out2 [Hhit2 Hlift]].
  exists (sem_bind out2
    (fun h => sem_ret (observe_stable_head on_ret2 on_vis h))).
  split.
  - exists out2. split; [exact Hhit2|apply sem_eq_refl].
  - eapply sem_lift_proper_l; [exact Hquery1|].
    eapply sem_lift_bind; [exact Hlift|].
    intros h1 h2 Hhead. apply sem_lift_ret.
    eapply observe_stable_head_related; eauto.
Qed.

(** Boolean event classifier: [true] marks the visible event class whose
    probability is being queried; returns are excluded. *)
Definition next_event_query {R}
    (accept : forall X, E X -> bool) (t : ptree E MN R)
    (query : MF bool) : Prop :=
  probabilistic_head_query (fun _ => false) accept t query.

Corollary probabilistic_eutt_preserves_next_event_query {R1 R2}
    (RR : R1 -> R2 -> Prop) (accept : forall X, E X -> bool)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) query1 :
  probabilistic_eutt RR t1 t2 ->
  next_event_query accept t1 query1 ->
  exists query2,
    next_event_query accept t2 query2 /\ sem_lift eq query1 query2.
Proof.
  intros Heutt Hquery.
  eapply probabilistic_eutt_preserves_head_query; eauto.
Qed.

End ProbabilisticHeadQuery.
