Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Program.Equality List ClassicalChoice.
From PTree.Core Require Import PTreeDefinition.
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

(** * Finite interactive trace prefixes

    A selector recognizes one dependent event and, when it matches, supplies
    the environment response used to enter the event continuation.  A list
    of selectors therefore describes a finite interaction prefix without
    assuming decidable equality on the event signature. *)
Section FiniteTraceQuery.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{FA : @SemanticMeasureCouplingAELaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FL : @SemanticOmegaLaws MF FI FO}.

Definition event_selector : Type := forall X, E X -> option X.
Definition finite_event_trace : Type := list event_selector.

(** [finite_trace_query tr t q] says that [q] is the Boolean
    subprobability measure of executions of [t] whose next visible
    interactions have prefix [tr].  The empty prefix succeeds immediately;
    a non-empty prefix rejects a stable return or a non-matching event and
    recursively queries the selected visible continuation. *)
Fixpoint finite_trace_query {R} (tr : finite_event_trace)
    (t : ptree E MN R) (query : MF bool) : Prop :=
  match tr with
  | nil => sem_eq query (sem_ret true)
  | select :: rest =>
      exists out branch,
        stable_hitting_weak
          (@ptree_primitive_kernel E MN MF FI MX R) (observe t) out /\
        sem_ae out (fun h =>
          match h with
          | FHRet _ => sem_eq (branch h) (sem_ret false)
          | @FHVis _ _ _ X e k =>
              match select X e with
              | Some x => finite_trace_query rest (k x) (branch h)
              | None => sem_eq (branch h) (sem_ret false)
              end
          end) /\
        sem_eq (sem_bind out branch) query
  end.

Lemma finite_trace_query_nil {R} (t : ptree E MN R) :
  finite_trace_query nil t (sem_ret true).
Proof. cbn. apply sem_eq_refl. Qed.

Lemma finite_trace_query_cons_inv {R} select rest
    (t : ptree E MN R) query :
  finite_trace_query (select :: rest) t query ->
  exists out branch,
    stable_hitting_weak
      (@ptree_primitive_kernel E MN MF FI MX R) (observe t) out /\
    sem_ae out (fun h =>
      match h with
      | FHRet _ => sem_eq (branch h) (sem_ret false)
      | @FHVis _ _ _ X e k =>
          match select X e with
          | Some x => finite_trace_query rest (k x) (branch h)
          | None => sem_eq (branch h) (sem_ret false)
          end
      end) /\
    sem_eq (sem_bind out branch) query.
Proof. exact (fun Hq => Hq). Qed.

Definition selector_accept (select : event_selector) :
    forall X, E X -> bool :=
  fun X e =>
    match select X e with
    | Some _ => true
    | None => false
    end.

Lemma finite_trace_query_vis_match `{FK : @SemanticMeasureAEKleisliLaws MF FI}
    `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
    {R X} (select : event_selector) rest (e : E X)
    (k : X -> ptree E MN R) x query :
  select X e = Some x ->
  finite_trace_query rest (k x) query ->
  finite_trace_query (select :: rest) (Vis e k) query.
Proof.
  intros Hselect Hrest.
  exists (sem_ret (FHVis e k)),
    (fun _ : frontier_head E MN R => query). repeat split.
  - apply stable_hitting_weak_vis.
  - apply sem_ae_ret. cbn. rewrite Hselect. exact Hrest.
  - exact (sem_bind_ret_l (FHVis e k)
      (fun _ : frontier_head E MN R => query)).
Qed.

Lemma finite_trace_query_vis_reject `{FK : @SemanticMeasureAEKleisliLaws MF FI}
    `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
    {R X} (select : event_selector) rest (e : E X)
    (k : X -> ptree E MN R) :
  select X e = None ->
  finite_trace_query (select :: rest) (Vis e k) (sem_ret false).
Proof.
  intro Hselect.
  exists (sem_ret (FHVis e k)),
    (fun _ : frontier_head E MN R => sem_ret false). repeat split.
  - apply stable_hitting_weak_vis.
  - apply sem_ae_ret. cbn. rewrite Hselect. apply sem_eq_refl.
  - exact (sem_bind_ret_l (FHVis e k)
      (fun _ : frontier_head E MN R => sem_ret false)).
Qed.

(** A singleton interactive prefix is exactly the old next-event query,
    after forgetting the selected response.  This makes
    [next_event_query] a conservative one-step specialization of the finite
    trace interface. *)
Theorem finite_trace_query_singleton_iff_next_event_query {R}
    (select : event_selector) (t : ptree E MN R) query :
  finite_trace_query (select :: nil) t query <->
  next_event_query (selector_accept select) t query.
Proof.
  split.
  - intros [out [branch [Hhit [Hgood Hquery]]]].
    exists out. split; [exact Hhit|].
    eapply sem_eq_trans; [|exact Hquery]. apply sem_eq_sym.
    apply sem_bind_ae_proper.
    eapply sem_ae_mono; [|exact Hgood].
    intros h Hg. destruct h as [r|X e k]; cbn in Hg |- *.
    + exact Hg.
    + destruct (select X e) as [x|] eqn:Hselect; cbn in Hg |- *;
        unfold selector_accept; rewrite Hselect; exact Hg.
  - intros [out [Hhit Hquery]].
    exists out,
      (fun h => sem_ret
        (observe_stable_head (fun _ : R => false)
          (selector_accept select) h)).
    repeat split; try assumption.
    + eapply sem_ae_mono; [|apply sem_ae_true].
      intros h _. destruct h as [r|X e k]; cbn.
      * apply sem_eq_refl.
      * destruct (select X e) as [x|] eqn:Hselect; cbn;
          unfold selector_accept; rewrite Hselect.
        -- apply sem_eq_refl.
        -- apply sem_eq_refl.
Qed.

(** Two witnesses for the same finite prefix are coupled whenever their
    programs are behaviorally equivalent.  Almost-everywhere restriction is
    essential: zero-mass stable heads need not admit a continuation query. *)
Theorem finite_trace_query_related {R1 R2}
    (RR : R1 -> R2 -> Prop) tr
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) query1 query2 :
  probabilistic_eutt RR t1 t2 ->
  finite_trace_query tr t1 query1 ->
  finite_trace_query tr t2 query2 ->
  sem_lift eq query1 query2.
Proof.
  revert R1 R2 RR t1 t2 query1 query2.
  induction tr as [|select rest IH];
    intros R1 R2 RR t1 t2 query1 query2 Heutt Hq1 Hq2.
  - cbn in Hq1, Hq2.
    eapply sem_lift_proper_r; [apply sem_eq_sym; exact Hq2|].
    eapply sem_lift_proper_l with (mu := sem_ret true).
    + apply sem_eq_sym. exact Hq1.
    + apply sem_lift_ret. reflexivity.
  - destruct (finite_trace_query_cons_inv Hq1)
      as [out1 [branch1 [Hhit1 [Hgood1 Hquery1]]]].
    destruct (finite_trace_query_cons_inv Hq2)
      as [out2 [branch2 [Hhit2 [Hgood2 Hquery2]]]].
    apply probabilistic_eutt_unfold in Heutt.
    destruct Heutt as [Hforward _].
    destruct (Hforward out1 Hhit1) as [out2' [Hhit2' Hlift]].
    assert (HoutEq : sem_eq out2' out2).
    { eapply stable_hitting_weak_unique; eassumption. }
    pose proof (sem_lift_proper_r
      (R := ptree_stable_head_rel RR (probabilistic_eutt_state RR))
      (mu := out1) (nu := out2') (nu' := out2) HoutEq Hlift) as Hlift12.
    pose (good1 := fun h : frontier_head E MN R1 =>
      match h with
      | FHRet _ => sem_eq (branch1 h) (sem_ret false)
      | @FHVis _ _ _ X e k =>
          match select X e with
          | Some x => finite_trace_query rest (k x) (branch1 h)
          | None => sem_eq (branch1 h) (sem_ret false)
          end
      end).
    pose (good2 := fun h : frontier_head E MN R2 =>
      match h with
      | FHRet _ => sem_eq (branch2 h) (sem_ret false)
      | @FHVis _ _ _ X e k =>
          match select X e with
          | Some x => finite_trace_query rest (k x) (branch2 h)
          | None => sem_eq (branch2 h) (sem_ret false)
          end
      end).
    assert (Hrestricted := sem_lift_ae_restrict
      (P := good1) (Q := good2) Hlift12 Hgood1 Hgood2).
    eapply sem_lift_proper_r; [exact Hquery2|].
    eapply sem_lift_proper_l; [exact Hquery1|].
    eapply sem_lift_bind; [exact Hrestricted|].
    intros h1 h2 [Hrel [Hg1 Hg2]].
    unfold good1 in Hg1. unfold good2 in Hg2.
    dependent destruction Hrel.
    + eapply sem_lift_proper_r; [apply sem_eq_sym; exact Hg2|].
      eapply sem_lift_proper_l with (mu := sem_ret false).
      * apply sem_eq_sym. exact Hg1.
      * apply sem_lift_ret. reflexivity.
    + destruct (select X e) as [x|] eqn:Hselect.
      * eapply IH; [exact (H x)|exact Hg1|exact Hg2].
      * eapply sem_lift_proper_r; [apply sem_eq_sym; exact Hg2|].
        eapply sem_lift_proper_l with (mu := sem_ret false).
        -- apply sem_eq_sym. exact Hg1.
        -- apply sem_lift_ret. reflexivity.
Qed.

(** Canonical behavioral equivalence preserves all finite dependent event
    prefixes.  Stable-head coupling transports the almost-everywhere domain
    on which recursive continuation queries are required. *)
Theorem probabilistic_eutt_preserves_finite_trace_query {R1 R2}
    (RR : R1 -> R2 -> Prop) tr
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) query1 :
  probabilistic_eutt RR t1 t2 ->
  finite_trace_query tr t1 query1 ->
  exists query2,
    finite_trace_query tr t2 query2 /\ sem_lift eq query1 query2.
Proof.
  revert R1 R2 RR t1 t2 query1.
  induction tr as [|select rest IH]; intros R1 R2 RR t1 t2 query1 Heutt Hq.
  - exists (sem_ret true). split; [apply finite_trace_query_nil|].
    eapply finite_trace_query_related; eauto using finite_trace_query_nil.
  - destruct (finite_trace_query_cons_inv Hq)
      as [out1 [branch1 [Hhit1 [Hgood1 Hquery1]]]].
    apply probabilistic_eutt_unfold in Heutt.
    destruct Heutt as [Hforward _].
    destruct (Hforward out1 Hhit1) as [out2 [Hhit2 Hlift]].
    pose (good1 := fun h : frontier_head E MN R1 =>
      match h with
      | FHRet _ => sem_eq (branch1 h) (sem_ret false)
      | @FHVis _ _ _ X e k =>
          match select X e with
          | Some x => finite_trace_query rest (k x) (branch1 h)
          | None => sem_eq (branch1 h) (sem_ret false)
          end
      end).
    pose (reachable2 := fun h2 : frontier_head E MN R2 =>
      exists h1, frontier_head_rel RR (probabilistic_eutt RR) h1 h2 /\
        good1 h1).
    assert (Hreachable2 : sem_ae out2 reachable2).
    { eapply sem_lift_ae_transport_r; [exact Hlift|exact Hgood1]. }
    assert (Hbranches : forall h2, exists q2,
      (reachable2 h2 ->
        match h2 with
        | FHRet _ => sem_eq q2 (sem_ret false)
        | @FHVis _ _ _ X e k =>
            match select X e with
            | Some x => finite_trace_query rest (k x) q2
            | None => sem_eq q2 (sem_ret false)
            end
        end) /\
      (forall h1, frontier_head_rel RR (probabilistic_eutt RR) h1 h2 ->
        good1 h1 -> sem_lift eq (branch1 h1) q2)).
    { intro h2. destruct (classic (reachable2 h2)) as [Hr|Hnr].
      - destruct Hr as [h1 [Hrel Hg1]].
        destruct h1 as [r1|Y e1 k1]; destruct h2 as [r2|X e k2];
          dependent destruction Hrel.
        + exists (sem_ret false). split.
          * intros Hreachable. apply sem_eq_refl.
          * intros h1' Hrel' Hg1'. dependent destruction Hrel'.
            unfold good1 in Hg1'.
            eapply sem_lift_proper_l with (mu := sem_ret false).
            -- apply sem_eq_sym. exact Hg1'.
            -- apply sem_lift_ret. reflexivity.
        + unfold good1 in Hg1.
          destruct (select X e) as [x|] eqn:Hselect.
          * destruct (IH _ _ RR (k1 x) (k2 x) (branch1 (FHVis e k1))
              (H x) Hg1) as [q2 [Hq2 HqLift]].
            exists q2. split.
            -- intros Hreachable. exact Hq2.
            -- intros h1' Hrel' Hg1'.
               destruct h1' as [r1'|Y' e1' k1']; dependent destruction Hrel'.
               unfold good1 in Hg1'.
               rewrite Hselect in Hg1'.
               eapply finite_trace_query_related;
                 [exact (H0 x)|exact Hg1'|exact Hq2].
          * exists (sem_ret false). split.
            -- intros Hreachable. apply sem_eq_refl.
            -- intros h1' Hrel' Hg1'.
               destruct h1' as [r1'|Y' e1' k1']; dependent destruction Hrel'.
               unfold good1 in Hg1'.
               rewrite Hselect in Hg1'.
               eapply sem_lift_proper_l with (mu := sem_ret false).
               ++ apply sem_eq_sym. exact Hg1'.
               ++ apply sem_lift_ret. reflexivity.
      - exists (sem_ret false). split.
        + contradiction.
        + intros h1 Hrel Hg1. exfalso. apply Hnr.
          exists h1. split; assumption. }
    destruct (@choice (frontier_head E MN R2) (MF bool) _ Hbranches)
      as [branch2 Hbranch2].
    assert (Hgood2 : sem_ae out2 (fun h2 =>
      match h2 with
      | FHRet _ => sem_eq (branch2 h2) (sem_ret false)
      | @FHVis _ _ _ X e k =>
          match select X e with
          | Some x => finite_trace_query rest (k x) (branch2 h2)
          | None => sem_eq (branch2 h2) (sem_ret false)
          end
      end)).
    { eapply sem_ae_mono; [|exact Hreachable2].
      intros h2 Hr. exact (proj1 (Hbranch2 h2) Hr). }
    exists (sem_bind out2 branch2). split.
    + exists out2, branch2. repeat split; try assumption. apply sem_eq_refl.
    + eapply sem_lift_proper_l; [exact Hquery1|].
      assert (Hrestricted := sem_lift_ae_restrict
        (P := good1) (Q := reachable2) Hlift Hgood1 Hreachable2).
      eapply sem_lift_bind; [exact Hrestricted|].
      intros h1 h2 [Hrel [Hg1 Hr]].
      exact (proj2 (Hbranch2 h2) h1 Hrel Hg1).
Qed.

End FiniteTraceQuery.
