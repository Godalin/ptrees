(** Role: Interpreter compositionality. Depends on equational theory (and comparison semantics for Atomic/MDP); not primitive syntax. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Program Require Import Equality.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Eq.FreeOmega Require Import Base Bind.
From PTree.Interp.FreeOmega Require Import Base Guarded.
From PTree.Semantics Require Import HeadTransition TreeTransition TreeTransitionBisim.
Require Import PTree.Interp.Kernel.
From PTree.Interp.FreeOmega Require Import Cofinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AtomicInterp.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI} `{NO : @SemanticOmega MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NC := NC) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation hits t out := (@ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure FO _ (observe t) out).
Variable handler : forall X, E X -> ptree E MN X.

(** An explicit semantic certificate, not a typeclass or a necessary
    characterization. This first profile preserves response values and
    permits event permutations, not event merging. Both internal segments
    have complete Dirac behavior; no finite-fuel or syntactic constraint
    is imposed. In particular a second visible interaction is excluded. *)
Record atomic_handler := {
  atomic_rename : forall X, E X -> E X;
  atomic_unrename : forall X, E X -> E X;
  atomic_unrename_rename : forall X (e : E X), atomic_unrename (atomic_rename e) = e;
  atomic_rename_unrename : forall X (e : E X), atomic_rename (atomic_unrename e) = e;
  atomic_cont : forall X, E X -> X -> ptree E MN X;
  atomic_start : forall X (e : E X),
    hits (handler e) (FORet (FHVis (atomic_rename e) (atomic_cont e)));
  atomic_finish : forall X (e : E X) x,
    hits (atomic_cont e x) (FORet (FHRet x))
}.

Variable atom : atomic_handler.

Lemma atomic_handler_guarded : guarded_handler (NI := NI) (NO := NO) handler.
Proof.
  apply (guarded_handler_of_hitting (NC := NC) (NCAE := NCAE) (NCount := NCount)).
  intros X e. exists (FORet (FHVis (atomic_rename atom e) (atomic_cont atom e))).
  split; [apply atomic_start|constructor; exact I].
Qed.

Definition atomic_label (label : obs_label E) : obs_label E :=
  match label with @Obs _ X e x => Obs (atomic_rename atom e) x end.
Definition atomic_unlabel (label : obs_label E) : obs_label E :=
  match label with @Obs _ X e x => Obs (atomic_unrename atom e) x end.
Lemma atomic_label_unlabel label : atomic_label (atomic_unlabel label) = label.
Proof. destruct label. cbn. rewrite atomic_rename_unrename. reflexivity. Qed.
Lemma atomic_unlabel_label label : atomic_unlabel (atomic_label label) = label.
Proof. destruct label. cbn. rewrite atomic_unrename_rename. reflexivity. Qed.

Definition atomic_offer (o : offered_event E) : offered_event E :=
  match o with @Offered _ X e => Offered (atomic_rename atom e) end.

Section Result.
Context {R : Type}.
Local Notation tree := (ptree E MN R).
Local Notation head := (stable_head E MN R).

Definition atomic_head (h : head) : head :=
  match h with
  | FHRet r => FHRet r
  | @FHVis _ _ _ X e k => FHVis (atomic_rename atom e)
      (fun x => PTree.bind (atomic_cont atom e x) (fun a => PTree.interp handler (k a)))
  end.
Definition atomic_map (mu : MF head) : MF head :=
  free_omega_bind mu (fun h => FORet (atomic_head h)).
Definition atomic_head_graph (h k : head) : Prop := k = atomic_head h.

Lemma atomic_map_lift mu : @sem_lift MF FI _ _ atomic_head_graph mu (atomic_map mu).
Proof.
  unfold atomic_map. induction mu; cbn.
  - apply FOQLStructural, FOLRet. reflexivity.
  - apply FOQLStructural, FOLZero.
  - eapply FOQLSample with (T := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. apply H.
  - apply FOQLLub. exact H.
Qed.

Lemma atomic_interp_head_hitting h :
  hits (ptree_interp_head_tree handler h) (FORet (atomic_head h)).
Proof.
  destruct h as [r|X e k].
  - apply (ptree_stable_hitting_ret (FI := FI) (FO := FO)).
  - destruct (stable_hitting_front_choice (FI := FI) (FO := FO)
      (fun x => PTree.interp handler (k x))) as [front Hfront].
    apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    change (hits (PTree.bind (handler e) (fun x => PTree.interp handler (k x)))
      (sem_bind (FORet (FHVis (atomic_rename atom e) (atomic_cont atom e)))
        (stable_head_bind_front (FI := FI) (fun x => PTree.interp handler (k x)) front))).
    eapply (ptree_stable_hitting_bind (FI := FI) (FO := FO));
      [apply ptree_bind_cofinal_all|apply atomic_start|exact Hfront].
Qed.

Lemma atomic_interp_hitting (t : tree) mu :
  hits t mu -> hits (PTree.interp handler t) (atomic_map mu).
Proof.
  intro Hhit. eapply (ptree_stable_hitting_interp (FI := FI) (FO := FO)).
  - apply ptree_interp_cofinal_all.
  - exact Hhit.
  - apply atomic_interp_head_hitting.
Qed.

Lemma atomic_finish_bind {X} (e : E X) x (k : X -> tree) mu :
  hits (k x) mu -> hits (PTree.bind (atomic_cont atom e x) k) mu.
Proof.
  intro Hhit.
  destruct (stable_hitting_front_choice (FI := FI) (FO := FO) k) as [front Hfront].
  assert (Hbind : hits (PTree.bind (atomic_cont atom e x) k) (front x)).
  { change (hits (PTree.bind (atomic_cont atom e x) k)
      (sem_bind (FORet (FHRet x)) (stable_head_bind_front (FI := FI) k front))).
    eapply (ptree_stable_hitting_bind (FI := FI) (FO := FO));
      [apply ptree_bind_cofinal_all|apply atomic_finish|exact Hfront]. }
  assert (Heq : @sem_eq MF FI _ (front x) mu).
  { eapply stable_hitting_unique; [apply Hfront|exact Hhit]. }
  unfold ptree_stable_hitting, stable_hitting in Hbind |- *.
  eapply FOQLComp with (T := eq) (U := eq) (mid := front x).
  - apply (sem_eq_sym (SI := FI)). exact Heq.
  - exact Hbind.
  - intros a c [b [-> ->]]. reflexivity.
Qed.

(** This normalization relation mentions complete hitting only, never a
    preservation theorem. It also covers the selected successor heads. *)
Definition atomic_normalizes (target source : tree) : Prop :=
  exists mu, hits source mu /\ hits target (atomic_map mu).

Lemma atomic_normalizes_interp t : atomic_normalizes (PTree.interp handler t) t.
Proof.
  destruct (stable_hitting_exists (FI := FI) (FO := FO)
    (@ptree_primitive_kernel E MN MF FI FreeOmegaMixedMeasure R) (observe t)) as [mu Hmu].
  exists mu. split; [exact Hmu|apply atomic_interp_hitting; exact Hmu].
Qed.

Lemma atomic_normalizes_head h :
  atomic_normalizes (stable_head_tree (atomic_head h)) (stable_head_tree h).
Proof.
  exists (FORet h). destruct h; split;
    first [apply (ptree_stable_hitting_ret (FI := FI) (FO := FO)) |
           apply (ptree_stable_hitting_vis (FI := FI) (FO := FO))].
Qed.

Lemma atomic_normalizes_heads target source mu nu :
  atomic_normalizes target source -> hits source mu -> hits target nu ->
  @sem_lift MF FI _ _ atomic_head_graph mu nu.
Proof.
  intros [front [Hs Ht]] Hmu Hnu.
  eapply sem_lift_proper_l.
  - eapply stable_hitting_unique; [exact Hs|exact Hmu].
  - eapply sem_lift_proper_r.
    + eapply stable_hitting_unique; [exact Ht|exact Hnu].
    + apply atomic_map_lift.
Qed.

Definition atomic_unhead (h : head) : head :=
  match h with FHRet r => FHRet r |
    @FHVis _ _ _ X e k => FHVis (atomic_unrename atom e) k end.

Lemma atomic_unhead_enabled h label : head_enabled h label ->
  head_enabled (atomic_unhead h) (atomic_unlabel label).
Proof. intro H. destruct H. constructor. Qed.

Lemma atomic_enabled h label :
  head_enabled (atomic_head h) (atomic_label label) -> head_enabled h label.
Proof.
  intro H. pose proof (atomic_unhead_enabled H) as Hb.
  rewrite atomic_unlabel_label in Hb.
  destruct h as [r|X e k]; cbn [atomic_unhead atomic_head] in Hb.
  - inversion Hb.
  - rewrite atomic_unrename_rename in Hb. dependent destruction Hb. constructor.
Qed.

Lemma atomic_action_result h label out :
  @head_action_result E MN MF FI FreeOmegaMixedMeasure FO R label h out ->
  @head_action_result E MN MF FI FreeOmegaMixedMeasure FO R
    (atomic_label label) (atomic_head h) (atomic_map out).
Proof.
  intros [Hstep|Hmiss Hzero].
  - destruct Hstep. apply HARMatch. constructor.
    apply atomic_finish_bind. apply atomic_interp_hitting. assumption.
  - apply HARMiss.
    + intro H. apply Hmiss. apply atomic_enabled. exact H.
    + change (free_omega_qlift eq (atomic_map out) (atomic_map FOZero)).
      unfold atomic_map. eapply FOQLBind; [exact Hzero|].
      intros a b ->. apply free_omega_qlift_refl. intro z. reflexivity.
Qed.

Lemma atomic_action_lift h label mu nu :
  @head_action_result E MN MF FI FreeOmegaMixedMeasure FO R label h mu ->
  @head_action_result E MN MF FI FreeOmegaMixedMeasure FO R
    (atomic_label label) (atomic_head h) nu ->
  @sem_lift MF FI _ _ atomic_head_graph mu nu.
Proof.
  intros Hmu Hnu. eapply (sem_lift_proper_r (SI := FI)); [|apply atomic_map_lift].
  eapply head_action_result_unique; [apply atomic_action_result; exact Hmu|exact Hnu].
Qed.

Lemma atomic_normalizes_trans target source label mu nu :
  atomic_normalizes target source ->
  @tree_trans E MN MF FI FreeOmegaMixedMeasure FO R source label mu ->
  @tree_trans E MN MF FI FreeOmegaMixedMeasure FO R target (atomic_label label) nu ->
  @sem_lift MF FI _ _ atomic_head_graph mu nu.
Proof.
  intros Hnorm [fs [ks [Hs [Haes Hos]]]] [ft [kt [Ht [Haet Hot]]]].
  pose proof (atomic_normalizes_heads Hnorm Hs Ht) as Hfront.
  pose proof (sem_lift_ae_restrict Hfront Haes Haet) as Hrestricted.
  eapply (sem_lift_proper_l (SI := FI)); [exact Hos|].
  eapply (sem_lift_proper_r (SI := FI)); [exact Hot|].
  eapply (sem_lift_bind (SI := FI)); [exact Hrestricted|].
  intros h k [-> [Hleft Hright]]. eapply atomic_action_lift; eassumption.
Qed.

Lemma atomic_normalizes_projects {O1 O2} (OR : O1 -> O2 -> Prop)
    (p1 : head -> MF O1) (p2 : head -> MF O2)
    (Hp : forall h, @sem_lift MF FI _ _ OR (p1 h) (p2 (atomic_head h)))
    target source mu nu :
  atomic_normalizes target source ->
  @tree_head_observation E MN MF FI FreeOmegaMixedMeasure FO R _ p1 source mu ->
  @tree_head_observation E MN MF FI FreeOmegaMixedMeasure FO R _ p2 target nu ->
  @sem_lift MF FI _ _ OR mu nu.
Proof.
  intros Hnorm [fs [Hs Hos]] [ft [Ht Hot]].
  eapply (sem_lift_proper_l (SI := FI)); [exact Hos|].
  eapply (sem_lift_proper_r (SI := FI)); [exact Hot|].
  eapply (sem_lift_bind (SI := FI)); [eapply atomic_normalizes_heads; eassumption|].
  intros h k ->. apply Hp.
Qed.

Lemma atomic_normalizes_returns target source mu nu :
  atomic_normalizes target source ->
  @tree_return_observation E MN MF FI FreeOmegaMixedMeasure FO R source mu ->
  @tree_return_observation E MN MF FI FreeOmegaMixedMeasure FO R target nu ->
  @sem_lift MF FI _ _ (fun r s => s = r) mu nu.
Proof.
  eapply atomic_normalizes_projects. intros [r|X e k];
    apply FOQLStructural; constructor; reflexivity.
Qed.

Lemma atomic_normalizes_offers target source mu nu :
  atomic_normalizes target source ->
  @tree_offered_event_observation E MN MF FI FreeOmegaMixedMeasure FO R source mu ->
  @tree_offered_event_observation E MN MF FI FreeOmegaMixedMeasure FO R target nu ->
  @sem_lift MF FI _ _ (fun e f => f = atomic_offer e) mu nu.
Proof.
  eapply atomic_normalizes_projects. intros [r|X e k];
    apply FOQLStructural; constructor; reflexivity.
Qed.

(** Push a source coupling across two graph couplings. This is ordinary
    coupling composition, not a whole-continuation comparison. *)
Lemma atomic_couple {A B} (f : A -> B) (AR : A -> A -> Prop) (BR : B -> B -> Prop)
    s1 s2 t1 t2 :
  @sem_lift MF FI _ _ (fun a b => b = f a) s1 t1 ->
  @sem_lift MF FI _ _ AR s1 s2 ->
  @sem_lift MF FI _ _ (fun a b => b = f a) s2 t2 ->
  (forall a b, AR a b -> BR (f a) (f b)) -> @sem_lift MF FI _ _ BR t1 t2.
Proof.
  intros H1 Hmid H2 Hrel.
  pose proof (sem_lift_comp Hmid H2) as Hright.
  pose proof (sem_lift_comp (sem_lift_sym H1) Hright) as Hfull.
  eapply (sem_lift_mono (SI := FI)); [|exact Hfull].
  intros a b [x [-> [y [Hxy ->]]]]. apply Hrel. exact Hxy.
Qed.

Local Lemma atomic_match {A} (AR : A -> A -> Prop) (L U : MF A -> Prop) :
  (exists mu, L mu) -> (exists nu, U nu) ->
  (forall mu nu, L mu -> U nu -> @sem_lift MF FI _ _ AR mu nu) ->
  @tree_measure_match MF FI A A AR L U.
Proof.
  intros [mu Hmu] [nu Hnu] Hlift. split.
  - intros q Hq. exists nu. split; [exact Hnu|apply Hlift; assumption].
  - intros q Hq. exists mu. split; [exact Hmu|apply Hlift; assumption].
Qed.

Variable RR : R -> R -> Prop.
Local Notation TB := (@tree_trans_bisim E MN MF FI FC FreeOmegaMixedMeasure FO R R RR).

Definition atomic_candidate (t u : tree) : Prop :=
  exists s v, atomic_normalizes t s /\ atomic_normalizes u v /\ TB s v.

Lemma atomic_candidate_postfixed t u : atomic_candidate t u ->
  @tree_trans_bisimF E MN MF FI FreeOmegaMixedMeasure FO R R RR atomic_candidate t u.
Proof.
  intros [s [v [Hts [Huv Hsv]]]]. split.
  - eapply atomic_match.
    + apply tree_head_observation_exists.
    + apply tree_head_observation_exists.
    + intros out1 out2 H1 H2.
      destruct (tree_head_observation_exists (FI := FI) (FO := FO)
        (return_projection (FI := FI)) s) as [mu Hmu].
      destruct (tree_head_observation_exists (FI := FI) (FO := FO)
        (return_projection (FI := FI)) v) as [nu Hnu].
      eapply (atomic_couple (f := fun r : R => r) (AR := RR)).
      * exact (atomic_normalizes_returns Hts Hmu H1).
      * exact (tree_trans_bisim_return_observations Hsv Hmu Hnu).
      * exact (atomic_normalizes_returns Huv Hnu H2).
      * intros a b Hab. exact Hab.
  - split.
    + eapply atomic_match.
      * apply tree_head_observation_exists.
      * apply tree_head_observation_exists.
      * intros out1 out2 H1 H2.
        destruct (tree_head_observation_exists (FI := FI) (FO := FO)
          (offered_event_projection (FI := FI)) s) as [mu Hmu].
        destruct (tree_head_observation_exists (FI := FI) (FO := FO)
          (offered_event_projection (FI := FI)) v) as [nu Hnu].
        eapply (atomic_couple (f := atomic_offer) (AR := eq)).
        -- exact (atomic_normalizes_offers Hts Hmu H1).
        -- exact (tree_trans_bisim_offered_observations Hsv Hmu Hnu).
        -- exact (atomic_normalizes_offers Huv Hnu H2).
        -- intros a b ->. reflexivity.
    + intro label. eapply atomic_match.
      * apply tree_trans_exists.
      * apply tree_trans_exists.
      * intros out1 out2 H1 H2.
        destruct (tree_trans_exists (FI := FI) (FO := FO) s (atomic_unlabel label)) as [mu Hmu].
        destruct (tree_trans_exists (FI := FI) (FO := FO) v (atomic_unlabel label)) as [nu Hnu].
        eapply (atomic_couple (f := atomic_head) (AR := tree_trans_head_rel TB)).
        -- eapply atomic_normalizes_trans; [exact Hts|exact Hmu|].
           rewrite atomic_label_unlabel. exact H1.
        -- exact (tree_trans_bisim_transitions Hsv Hmu Hnu).
        -- eapply atomic_normalizes_trans; [exact Huv|exact Hnu|].
           rewrite atomic_label_unlabel. exact H2.
        -- intros h k Hhk. exists (stable_head_tree h), (stable_head_tree k).
           split; [apply atomic_normalizes_head|].
           split; [apply atomic_normalizes_head|exact Hhk].
Qed.

Theorem tree_trans_bisim_interp_atomic (t u : tree) :
  TB t u -> TB (PTree.interp handler t) (PTree.interp handler u).
Proof.
  intro Htu. eapply tree_trans_bisim_coinduction with (sim := atomic_candidate).
  - exact atomic_candidate_postfixed.
  - exists t, u. split; [apply atomic_normalizes_interp|].
    split; [apply atomic_normalizes_interp|exact Htu].
Qed.

End Result.
End AtomicInterp.
