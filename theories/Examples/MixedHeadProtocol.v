(** A canonical probabilistic-LTS example: one coupling matches both Ret
    and Vis heads; visible pairs generate response-dependent recursive
    obligations. All native probability nodes use the bounded SubEnum carrier. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.
From Coq Require Import Program.Equality FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order rat.
From PTree.Core Require Import PTreeDefinition PTreeProbability.
From PTree.Prob Require Import RatSubTypes DiscreteMC EnumBindFacts EnumMap
  Coupling IndexedCoupling FrontierLiftEnum MeasureIterationEnum
  TwoLevelMeasure TwoLevelMeasureSubEnum FreeOmegaMeasure.
From PTree.Eq Require Import Shallow UnifiedFrontier PrimitiveStableHitting
  OperationalProbabilisticPTS OperationalProbabilisticPTSFreeOmega
  ProbabilisticEutt ProbabilisticTraceSubEnum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum EnumMap IndexedCoupling Coupling GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope subenum_probability_scope.

(** The event universe is invariant in PTree. This two-response wrapper
    lifts an ordinary Boolean to that universe without changing its choices. *)
Polymorphic Variant mixed_response@{u} : Type@{u} := Response (response_bit : bool).
Polymorphic Definition response_value@{u} (r : mixed_response@{u}) : bool :=
  match r with Response b => b end.
Polymorphic Variant mixedE@{u v} : Type@{u} -> Type@{u} :=
| Challenge : mixedE mixed_response@{v}
| Reply (b : bool) : mixedE mixed_response@{v}.

Variant mixed_outcome := Stop (b : bool) | Continue (b : bool).
Scheme Equality for mixed_outcome.
Lemma mixed_outcome_eqP : Equality.axiom mixed_outcome_beq.
Proof. intros [[]|[]] [[]|[]]; constructor; congruence. Qed.
HB.instance Definition _ := hasDecEq.Build mixed_outcome mixed_outcome_eqP.

Definition mixed_quarter : nnQ := mknnQ (1 / 4) ltac:(by []).
Definition mixed_pair_raw : Enum (bool * bool) :=
  [:: (mixed_quarter, (false,false)); (mixed_quarter, (false,true));
      (mixed_quarter, (true,false)); (mixed_quarter, (true,true))].
Definition mixed_outcomes_raw : Enum mixed_outcome :=
  [:: (mixed_quarter, Stop false); (mixed_quarter, Stop true);
      (mixed_quarter, Continue false); (mixed_quarter, Continue true)].
Lemma mixed_pair_bound : enum_subprob mixed_pair_raw.
Proof. by vm_compute. Qed.
Lemma mixed_outcomes_bound : enum_subprob mixed_outcomes_raw.
Proof. by vm_compute. Qed.
Definition mixed_pair := enum_as_subprob mixed_pair_bound.
Definition mixed_outcomes := enum_as_subprob mixed_outcomes_bound.

Definition mixed_encode m c (rs : bool * bool) : mixed_outcome :=
  let '(r,s) := rs in
  let b := xorb c (xorb m s) in
  if xorb m r then Continue b else Stop b.
Definition mixed_decode m c o : bool * bool :=
  match o with
  | Stop b => (m, xorb c (xorb m b))
  | Continue b => (negb m, xorb c (xorb m b))
  end.
Lemma mixed_decode_encode m c rs : mixed_decode m c (mixed_encode m c rs) = rs.
Proof. destruct m,c; destruct rs as [r s]; destruct r,s; reflexivity. Qed.
Lemma mixed_encode_decode m c o : mixed_encode m c (mixed_decode m c o) = o.
Proof. destruct m,c; destruct o as [b|b]; destruct b; reflexivity. Qed.
Definition mixed_outcome_rel m c rs o := o = mixed_encode m c rs.

(** An explicit four-atom coupling; its right marginal is uniform because
    encode merely permutes the four atoms for each hidden state/challenge. *)
Definition mixed_joint m c : Enum ((bool * bool) * mixed_outcome) :=
  emap (fun rs => (rs, mixed_encode m c rs)) mixed_pair_raw.
Polymorphic Lemma mixed_pair_outcome_lift m c :
  @sem_lift SubEnum SubEnum_SemanticMeasure _ _ (mixed_outcome_rel m c)
    mixed_pair mixed_outcomes.
Proof.
  change (indexed_coupling (mixed_outcome_rel m c) mixed_pair_raw mixed_outcomes_raw).
  apply indexed_coupling_of_coupling. exists (mixed_joint m c).
  - apply enum_eq_eq. reflexivity.
  - intros [b|b]; destruct m,c,b; apply val_inj; vm_compute; reflexivity.
  - intros [r s] [b|b] Hmass; destruct m,c,r,s,b;
      try reflexivity; vm_compute in Hmass; discriminate.
Qed.

Set Universe Polymorphism.

Definition masked_update (rs : bool * bool) ack := if ack then fst rs else snd rs.
CoFixpoint masked_impl (m : bool) : ptree mixedE SubEnum bool :=
  Vis Challenge (fun answer =>
    let c := response_value answer in
    Prob mixed_pair (fun rs =>
      match mixed_encode m c rs with
      | Stop b => Ret b
      | Continue b => Vis (Reply b) (fun ack => masked_impl (masked_update rs (response_value ack)))
      end)).
CoFixpoint mixed_spec : ptree mixedE SubEnum bool :=
  Vis Challenge (fun _ =>
    Prob mixed_outcomes (fun o =>
      match o with
      | Stop b => Ret b
      | Continue b => Vis (Reply b) (fun _ => mixed_spec)
      end)).
Definition masked_branch m c rs : ptree mixedE SubEnum bool :=
  match mixed_encode m c rs with
  | Stop b => Ret b
  | Continue b => Vis (Reply b) (fun ack => masked_impl (masked_update rs (response_value ack)))
  end.
Definition spec_branch o : ptree mixedE SubEnum bool :=
  match o with
  | Stop b => Ret b
  | Continue b => Vis (Reply b) (fun _ => mixed_spec)
  end.
Definition masked_after m c := Prob mixed_pair (masked_branch m c).
Definition mixed_after := Prob mixed_outcomes spec_branch.
Lemma masked_impl_unfold m : observe (masked_impl m) = VisF Challenge (fun answer => masked_after m (response_value answer)).
Proof. reflexivity. Qed.
Lemma mixed_spec_unfold : observe mixed_spec = VisF Challenge (fun _ => mixed_after).
Proof. reflexivity. Qed.

Example masked_impl_probabilistic m : probabilistic_ptree (masked_impl m).
Proof. apply probabilistic_ptree_intrinsic. Qed.
Example mixed_spec_probabilistic : probabilistic_ptree mixed_spec.
Proof. apply probabilistic_ptree_intrinsic. Qed.

Local Notation MF := (FreeOmega SubEnum).
Local Notation mixed_head := (frontier_head mixedE SubEnum bool).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation kernel := (@ptree_primitive_kernel mixedE SubEnum MF FI FreeOmegaMixedMeasure bool).
Local Notation hitting := (@stable_hitting_weak MF FI FreeOmegaObservableSemanticOmega
  (ptree' mixedE SubEnum bool) mixed_head kernel).
Local Notation peutt := (@probabilistic_eutt mixedE SubEnum MF FI
  FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
  FreeOmegaObservableSemanticOmega).

Definition masked_head m c rs : mixed_head :=
  match mixed_encode m c rs with
  | Stop b => FHRet b
  | Continue b => FHVis (Reply b) (fun ack => masked_impl (masked_update rs (response_value ack)))
  end.
Definition spec_head o : mixed_head :=
  match o with
  | Stop b => FHRet b
  | Continue b => FHVis (Reply b) (fun _ => mixed_spec)
  end.
Definition masked_after_heads m c : MF mixed_head :=
  FOSample mixed_pair (fun rs => FORet (masked_head m c rs)).
Definition spec_after_heads : MF mixed_head :=
  FOSample mixed_outcomes (fun o => FORet (spec_head o)).

Lemma masked_after_hitting m c : hitting (observe (masked_after m c)) (masked_after_heads m c).
Proof.
  unfold masked_after, masked_after_heads.
  eapply (stable_hitting_weak_prob (FI := FI)
    (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure))
    with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros rs _. unfold masked_branch, masked_head.
    destruct (mixed_encode m c rs).
    + apply (stable_hitting_weak_ret (FI := FI) (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure)).
    + apply (stable_hitting_weak_vis (FI := FI) (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure)).
Qed.
Lemma spec_after_hitting : hitting (observe mixed_after) spec_after_heads.
Proof.
  unfold mixed_after, spec_after_heads.
  eapply (stable_hitting_weak_prob (FI := FI)
    (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure))
    with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros [b|b] _; [apply (stable_hitting_weak_ret (FI := FI) (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure))|apply (stable_hitting_weak_vis (FI := FI) (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure))].
Qed.

(** Root quantifies over every hidden bit. After additionally remembers the
    challenge supplied by the environment. No up-to closure is involved. *)
Definition mixed_protocol_sim (s1 s2 : ptree' mixedE SubEnum bool) : Prop :=
  (exists m, s1 = observe (masked_impl m) /\ s2 = observe mixed_spec) \/
  (exists m c, s1 = observe (masked_after m c) /\ s2 = observe mixed_after).
Lemma MPSRoot m : mixed_protocol_sim (observe (masked_impl m)) (observe mixed_spec).
Proof. left. exists m. split; reflexivity. Qed.
Lemma MPSAfter m c : mixed_protocol_sim (observe (masked_after m c)) (observe mixed_after).
Proof. right. exists m, c. split; reflexivity. Qed.

Lemma mixed_heads_lift m c :
  @sem_lift MF FI _ _ (@ptree_stable_head_rel mixedE SubEnum bool bool eq mixed_protocol_sim)
    (masked_after_heads m c) spec_after_heads.
Proof.
  unfold masked_after_heads, spec_after_heads.
  eapply (mixed_lift_bind (NI := SubEnum_SemanticMeasure) (FI := FI)
    (MX := FreeOmegaMixedMeasure)) with (R := mixed_outcome_rel m c).
  - exact (mixed_pair_outcome_lift m c).
  - intros rs o ->. apply (sem_lift_ret (SI := FI)).
    unfold ptree_stable_head_rel, masked_head, spec_head.
    destruct (mixed_encode m c rs) as [b|b].
    + apply FHRRet. reflexivity.
    + apply FHRVis. intro ack. apply MPSRoot.
Qed.

Lemma mixed_protocol_sim_postfixed : forall s1 s2, mixed_protocol_sim s1 s2 ->
  @stable_hitting_match MF FI FreeOmegaObservableSemanticOmega
    (ptree' mixedE SubEnum bool) (ptree' mixedE SubEnum bool)
    mixed_head mixed_head kernel kernel
    (@ptree_stable_head_rel mixedE SubEnum bool bool eq) mixed_protocol_sim s1 s2.
Proof.
  intros s1 s2 [[m [-> ->]]|[m [c [-> ->]]]].
  - rewrite masked_impl_unfold mixed_spec_unfold.
    apply stable_hitting_match_vis. intro answer. apply MPSAfter.
  - eapply stable_hitting_match_of_hitting_lift.
    + exact (masked_after_hitting m c).
    + exact spec_after_hitting.
    + exact (mixed_heads_lift m c).
Qed.

Theorem masked_protocol_equivalent m : peutt eq (masked_impl m) mixed_spec.
Proof.
  eapply probabilistic_eutt_coinduction with (sim := mixed_protocol_sim).
  - exact mixed_protocol_sim_postfixed.
  - apply MPSRoot.
Qed.

(** The Challenge case is a totality default: after-challenge witnesses
    contain only returns and Reply events, as the following proof shows. *)
Definition stable_outcome (h : mixed_head) : mixed_outcome :=
  match h with
  | FHRet b => Stop b
  | @FHVis _ _ _ X e _ =>
      match e with Challenge => Stop false | Reply b => Continue b end
  end.
Lemma masked_head_outcome m c rs : stable_outcome (masked_head m c rs) = mixed_encode m c rs.
Proof. unfold masked_head. destruct (mixed_encode m c rs); reflexivity. Qed.
Definition masked_outcome_observation m c : SubEnum mixed_outcome :=
  subenum_bind mixed_pair (fun rs => subenum_ret (mixed_encode m c rs)).

(** The observation is stated extensionally: list order may change with
    m and c, while each of the four stable outcomes still has mass 1/4. *)
Lemma masked_after_heads_denote_four m c :
  @free_omega_denotes SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
    mixed_head mixed_outcome stable_outcome (masked_after_heads m c) mixed_outcomes.
Proof.
  exists (masked_outcome_observation m c). split.
  - unfold masked_after_heads, masked_outcome_observation.
    apply (FOOObserveSample (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)). intro rs.
    rewrite <- (masked_head_outcome m c rs). constructor.
  - change (enum_meas_eq
      (bind_Enum mixed_pair_raw (fun rs => ret_Enum (mixed_encode m c rs))) mixed_outcomes_raw).
    apply enum_meas_eq_of_eqenum. intros [b|b]; destruct m,c,b;
      apply val_inj; vm_compute; reflexivity.
Qed.

(** Connect the observable distribution to an actual complete-hitting
    witness of the implementation, not merely a standalone measure. *)
Theorem masked_after_uniform_stable_hitting m c :
  exists out : MF mixed_head,
    hitting (observe (masked_after m c)) out /\
    @free_omega_denotes SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
      mixed_head mixed_outcome stable_outcome out mixed_outcomes.
Proof.
  exists (masked_after_heads m c). split.
  - exact (masked_after_hitting m c).
  - exact (masked_after_heads_denote_four m c).
Qed.

Definition select_challenge (c : bool) {X} (e : mixedE X) : option X :=
  match e in mixedE X0 return option X0 with
  | Challenge => Some (Response c)
  | Reply _ => None
  end.
Definition select_true_reply {X} (e : mixedE X) : option X :=
  match e in mixedE X0 return option X0 with
  | Challenge => None
  | Reply b => if b then Some (Response true) else None
  end.
Definition challenge_true_reply_trace c : @finite_interaction_pattern mixedE :=
  cons (@select_challenge c) (cons (@select_true_reply) nil).
Definition accepts_true_reply {X} (e : mixedE X) : bool :=
  match e with Challenge => false | Reply b => b end.
Definition spec_true_reply_query : MF bool :=
  @sem_bind MF FI mixed_head bool spec_after_heads (fun h =>
    @sem_ret MF FI bool (observe_stable_head (fun _ => false) (@accepts_true_reply) h)).
Definition spec_true_reply_observation : SubEnum bool :=
  subenum_bind mixed_outcomes (fun o =>
    subenum_ret (match o with Stop _ => false | Continue b => b end)).

Lemma spec_after_true_reply_query :
  @next_event_query mixedE SubEnum MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool (@accepts_true_reply) mixed_after spec_true_reply_query.
Proof.
  exists spec_after_heads. split; [exact spec_after_hitting|apply sem_eq_refl].
Qed.
Lemma true_reply_selector_accepts :
  @selector_accept mixedE (@select_true_reply) = @accepts_true_reply.
Proof.
  apply functional_extensionality_dep. intro X.
  apply functional_extensionality. intro e. destruct e; [reflexivity|].
  destruct b; reflexivity.
Qed.
Lemma spec_challenge_true_reply_query c :
  @finite_trace_query mixedE SubEnum MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool (challenge_true_reply_trace c)
    mixed_spec spec_true_reply_query.
Proof.
  unfold challenge_true_reply_trace.
  change (@finite_trace_query mixedE SubEnum MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (cons (@select_challenge c) (cons (@select_true_reply) nil))
    (Vis Challenge (fun _ => mixed_after)) spec_true_reply_query).
  eapply finite_trace_query_vis_match.
  - reflexivity.
  - apply (proj2 (finite_trace_query_singleton_iff_next_event_query
      (@select_true_reply) mixed_after spec_true_reply_query)).
    rewrite true_reply_selector_accepts. exact spec_after_true_reply_query.
Qed.
Lemma spec_true_reply_query_denotes :
  @free_omega_denotes SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
    bool bool id spec_true_reply_query spec_true_reply_observation.
Proof.
  exists spec_true_reply_observation. split; [|apply sem_eq_refl].
  unfold spec_true_reply_query, spec_after_heads, spec_true_reply_observation.
  cbn [free_omega_bind]. apply (FOOObserveSample (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
  intros [b|b]; constructor.
Qed.
Lemma spec_true_reply_mass :
  enum_expect subenum_bool_indicator (subenum_raw spec_true_reply_observation) = 1 / 4.
Proof. vm_compute. reflexivity. Qed.

(** Ret mass rejects the nonempty remaining prefix; only Continue(true)
    reaches the second selected event. Hence 1/4, not the 1/2 of a
    reply-only service. The result holds for either challenge and any m. *)
Theorem masked_challenge_true_reply_probability m c :
  Prₛ[ masked_impl m | challenge_true_reply_trace c ] = (1 / 4 : rat).
Proof.
  destruct (probabilistic_eutt_preserves_finite_trace_query
    (probabilistic_eutt_sym (masked_protocol_equivalent m))
    (spec_challenge_true_reply_query c)) as [query [Hquery Hlift]].
  eapply subenum_finite_interaction_probability_intro
    with (query := query) (representative := spec_true_reply_query)
      (out := spec_true_reply_observation).
  - exact Hquery.
  - exact Hlift.
  - exact spec_true_reply_query_denotes.
  - exact spec_true_reply_mass.
Qed.
