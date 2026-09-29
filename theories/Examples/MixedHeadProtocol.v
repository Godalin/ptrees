(** Case role: paper case study.
    Reading entry: mixed_head_bridge; masked_protocol_equivalent; masked_challenge_true_reply_probability.
    Scope: SubEnumQ / observable FreeOmega; mixed return/visible frontiers require the displayed invariant.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
(** Learn: up-to-Prob with a non-functional 3-to-2 coupling and a recursive invariant.
    Reusable endpoints: masked_protocol_equivalent, masked_after_stable_hitting, masked_challenge_true_reply_probability.
    Boundary: this is not a pure rewrite proof or an execution demo.
    User navigation: docs/CASE_STUDIES.md. *)
(** A canonical probabilistic-LTS example: one coupling matches both Ret
    and Vis heads; visible pairs generate response-dependent recursive
    obligations. All native probability nodes use the bounded SubEnumQ carrier. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Eq Require Import StableHittingRelation.
From Coq.Program Require Import Equality.
From Coq Require Import FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order rat.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import WellFormedness.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Bind PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling PTree.Prob.Backend.EnumQ.IndexedCoupling PTree.Prob.Backend.EnumQ.FrontierLift PTree.Prob.Backend.EnumQ.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import Shallow UnifiedFrontier PrimitiveStableHitting PTreeKernel ProbabilisticTrace.
From PTree.Eq.FreeOmega Require Import Base Hitting Relation Bind Algebra Iter.
From PTree.Interp.FreeOmega Require Import Base Guarded.
From PTree.Eq Require Import PEutt UpToProb.
From PTree.Prob.FreeOmega Require Import BindOrder.
From PTree.Eq.Backend Require Import ProbabilisticTraceSubEnumQ.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ PTree.Prob.Backend.EnumQ.Map IndexedCoupling PTree.Prob.Backend.EnumQ.Coupling GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope subenumQ_probability_scope.

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

(** Finite analysis: the middle row genuinely splits between both columns.
    Concrete rational representation stays in these analysis helpers,
    not in the program-level coupling/coinduction proof. *)
Variant hidden3 := L0 | L1 | L2.
Scheme Equality for hidden3.
Lemma hidden3_eqP : Equality.axiom hidden3_beq.
Proof. intros [] []; constructor; congruence. Qed.
HB.instance Definition _ := hasDecEq.Build hidden3 hidden3_eqP.

Definition bridge m z : Prop :=
  match m with L0 => z = false | L1 => True | L2 => z = true end.
Lemma bridge_next m z h j (a : bool) :
  bridge m z -> bridge h j ->
  bridge (if a then h else m) (if a then j else z).
Proof. destruct a; auto. Qed.

Definition uniform3_raw : EnumQ hidden3.
Proof.
  refine (enumQ_of_list (mu := [:: (1/3, L0); (1/3, L1); (1/3, L2)]) _).
  intros p x [He|[He|[He|[]]]]; inversion He; subst; by vm_compute.
Defined.
Definition uniform2_raw : EnumQ bool.
Proof.
  refine (enumQ_of_list (mu := [:: (1/2, false); (1/2, true)]) _).
  intros p x [He|[He|[]]]; inversion He; subst; by vm_compute.
Defined.
Definition coupling32_raw : EnumQ (hidden3 * bool).
Proof.
  refine (enumQ_of_list (mu :=
    [:: (1/3, (L0,false)); (1/6, (L1,false));
        (1/6, (L1,true)); (1/3, (L2,true))]) _).
  intros p x [He|[He|[He|[He|[]]]]]; inversion He; subst; by vm_compute.
Defined.
Lemma uniform3_bound : enumQ_subprob uniform3_raw.
Proof. by vm_compute. Qed.
Lemma uniform2_bound : enumQ_subprob uniform2_raw.
Proof. by vm_compute. Qed.
Definition uniform3 := enumQ_as_subprob uniform3_bound.
Definition uniform2 := enumQ_as_subprob uniform2_bound.

Lemma coupling32_left : emap fst coupling32_raw ==EnumQ uniform3_raw.
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma coupling32_right : emap snd coupling32_raw ==EnumQ uniform2_raw.
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma coupling32_support m z :
  acc_mass (m,z) coupling32_raw != 0 -> bridge m z.
Proof.
  unfold bridge. destruct m,z; try (intros _; reflexivity);
    try (intros _; exact I); vm_compute; discriminate.
Qed.

Polymorphic Lemma coupling32_lift :
  @sem_lift SubEnumQ SubEnumQ_SemanticMeasure _ _ bridge uniform3 uniform2.
Proof.
  change (indexed_coupling bridge (enumQ_prune uniform3_raw) (enumQ_prune uniform2_raw)).
  eapply indexed_coupling_raw with (mu := uniform3_raw) (nu := uniform2_raw);
    [reflexivity|reflexivity|].
  apply indexed_coupling_of_coupling. exists coupling32_raw.
  - exact coupling32_left.
  - exact coupling32_right.
  - exact coupling32_support.
Qed.

(** Stronger than merely displaying a split joint: no deterministic map
    from these three equiprobable atoms has the required fair marginal. *)
Lemma uniform3_no_deterministic_fair (f : hidden3 -> bool) :
  ~ (emap f uniform3_raw ==EnumQ uniform2_raw).
Proof.
  intro H. specialize (H true).
  change (acc_mass true (emap f uniform3_raw) = acc_mass true uniform2_raw) in H.
  change (FiniteAtoms.finite_atom true
    [:: (1/3 : rat, f L0); (1/3 : rat, f L1); (1/3 : rat, f L2)] =
    acc_mass true uniform2_raw) in H.
  destruct (f L0), (f L1), (f L2); vm_compute in H; discriminate.
Qed.

(** Public b = c xor s, with s biased 3/4; Stop/Continue is fair.
    Combine these independent draws into their four-outcome kernel. *)
Definition mixed_eighth : rat := 1 / 8.
Definition mixed_three_eighths : rat := 3 / 8.
Definition mixed_outcomes_raw (c : bool) : EnumQ mixed_outcome.
Proof.
  refine (enumQ_of_list (mu := let w0 := if c then mixed_three_eighths else mixed_eighth in
  let w1 := if c then mixed_eighth else mixed_three_eighths in
  [:: (w0, Stop false); (w1, Stop true);
      (w0, Continue false); (w1, Continue true)]) _).
  intros p x [He|[He|[He|[He|[]]]]]; inversion He; subst; destruct c; by vm_compute.
Defined.
Lemma mixed_outcomes_bound c : enumQ_subprob (mixed_outcomes_raw c).
Proof. destruct c; by vm_compute. Qed.
Definition mixed_outcomes c := enumQ_as_subprob (mixed_outcomes_bound c).

(** Program-facing kernel: sample a new hidden state only on Continue.
    Native bind flattens the finite draws, so the main coinduction needs
    just one up-to-Prob context. No list expansion in the program proof. *)
Definition mixed_samples {H} (hidden : SubEnumQ H) c : SubEnumQ (bool + bool * H) :=
  sem_bind (mixed_outcomes c) (fun o =>
    match o with
    | Stop b => sem_ret (inl b)
    | Continue b => sem_bind hidden (fun h => sem_ret (inr (b,h)))
    end).
Definition mixed_sample_rel (x : bool + bool * hidden3) (y : bool + bool * bool) : Prop :=
  match x, y with
  | inl b, inl b' => b = b'
  | inr (b,h), inr (b',j) => b = b' /\ bridge h j
  | _, _ => False
  end.
Polymorphic Lemma mixed_samples_lift c :
  @sem_lift SubEnumQ SubEnumQ_SemanticMeasure _ _ mixed_sample_rel
    (mixed_samples uniform3 c) (mixed_samples uniform2 c).
Proof.
  unfold mixed_samples. eapply sem_lift_bind with (R := eq).
  - apply sem_lift_refl. congruence.
  - intros [b|b] o <-.
    + apply sem_lift_ret. reflexivity.
    + eapply sem_lift_bind; [exact coupling32_lift|].
      intros h j Hhj. apply sem_lift_ret. split; [reflexivity|exact Hhj].
Qed.

Set Universe Polymorphism.

Local Notation tree := (ptree mixedE SubEnumQ).
Local Notation state := (ptree' mixedE SubEnumQ bool).
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation mixed_head := (stable_head mixedE SubEnumQ bool).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation MX := (@FreeOmegaMixedMeasure SubEnumQ).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation kernel := (@ptree_primitive_kernel mixedE SubEnumQ MF FI FreeOmegaMixedMeasure bool).
Local Notation hitting := (@stable_hitting MF FI FreeOmegaObservableSemanticOmega
  (ptree' mixedE SubEnumQ bool) mixed_head kernel).
(** Fix the observable interpretation once, exactly as in FactoryController;
    this is notation for raw peutt, not an additional relation. *)
Local Notation W := (PEutt.peutt (E := mixedE) (MN := SubEnumQ)
  (MF := MF) (FI := FI) (FC := FC) (MX := MX) (FO := FO)).
Local Notation "t ≈ₚ u" := (W eq t u)
  (at level 70, no associativity) : type_scope.
Local Notation upto := (prob_upto_closure (NI := SubEnumQ_SemanticMeasure)
  (FI := FI) (FC := FC) (MX := MX) (FO := FO) eq).
Local Notation progress := (stable_hitting_match (FI := FI) (FO := FO)
  kernel kernel (@ptree_stable_head_rel mixedE SubEnumQ bool bool eq)).

(** Programs: Challenge is observable; native sampling exposes either a
    return or a Reply whose continuation keeps or refreshes hidden state. *)
CoFixpoint masked_impl (m : hidden3) : tree bool :=
  Vis Challenge (fun answer =>
    Prob (mixed_samples uniform3 (response_value answer)) (fun x =>
      match x with
      | inl b => Ret b
      | inr (b,h) => Vis (Reply b) (fun ack =>
          masked_impl (if response_value ack then h else m))
      end)).
CoFixpoint mixed_spec (z : bool) : tree bool :=
  Vis Challenge (fun answer =>
    Prob (mixed_samples uniform2 (response_value answer)) (fun x =>
      match x with
      | inl b => Ret b
      | inr (b,j) => Vis (Reply b) (fun ack =>
          mixed_spec (if response_value ack then j else z))
      end)).
Definition canonical_spec := mixed_spec false.
Definition masked_branch m (x : bool + bool * hidden3) : tree bool :=
  match x with
  | inl b => Ret b
  | inr (b,h) => Vis (Reply b) (fun ack =>
      masked_impl (if response_value ack then h else m))
  end.
Definition spec_branch z (x : bool + bool * bool) : tree bool :=
  match x with
  | inl b => Ret b
  | inr (b,j) => Vis (Reply b) (fun ack =>
      mixed_spec (if response_value ack then j else z))
  end.
Definition masked_after m c := Prob (mixed_samples uniform3 c) (masked_branch m).
Definition mixed_after z c := Prob (mixed_samples uniform2 c) (spec_branch z).
Lemma masked_impl_unfold m : observe (masked_impl m) = VisF Challenge (fun answer => masked_after m (response_value answer)).
Proof. reflexivity. Qed.
Lemma mixed_spec_unfold z : observe (mixed_spec z) = VisF Challenge (fun answer => mixed_after z (response_value answer)).
Proof. reflexivity. Qed.

Example masked_impl_probabilistic m : probabilistic_ptree (masked_impl m).
Proof. apply probabilistic_ptree_intrinsic. Qed.
Example mixed_spec_probabilistic z : probabilistic_ptree (mixed_spec z).
Proof. apply probabilistic_ptree_intrinsic. Qed.

Definition masked_head m (x : bool + bool * hidden3) : mixed_head :=
  match x with
  | inl b => FHRet b
  | inr (b,h) => FHVis (Reply b) (fun ack =>
      masked_impl (if response_value ack then h else m))
  end.
Definition spec_head z (x : bool + bool * bool) : mixed_head :=
  match x with
  | inl b => FHRet b
  | inr (b,j) => FHVis (Reply b) (fun ack =>
      mixed_spec (if response_value ack then j else z))
  end.
Definition masked_after_heads m c : MF mixed_head :=
  FOSample (mixed_samples uniform3 c) (fun x => FORet (masked_head m x)).
Definition spec_after_heads z c : MF mixed_head :=
  FOSample (mixed_samples uniform2 c) (fun x => FORet (spec_head z x)).

Lemma masked_after_hitting m c : hitting (observe (masked_after m c)) (masked_after_heads m c).
Proof.
  unfold masked_after, masked_after_heads.
  eapply (stable_hitting_prob (FI := FI) (FO := FO) (MX := MX))
    with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros [b|[b h]] _.
    + apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := MX)).
    + apply (stable_hitting_vis (FI := FI) (FO := FO) (MX := MX)).
Qed.
Lemma spec_after_hitting z c : hitting (observe (mixed_after z c)) (spec_after_heads z c).
Proof.
  unfold mixed_after, spec_after_heads.
  eapply (stable_hitting_prob (FI := FI) (FO := FO) (MX := MX))
    with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros [b|[b j]] _.
    + apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := MX)).
    + apply (stable_hitting_vis (FI := FI) (FO := FO) (MX := MX)).
Qed.

(** Only roots and replies belong to the invariant. The reply obligation
    carries BOTH the old bridge and the new bridge supplied by the joint. *)
Definition mixed_protocol_sim (s1 s2 : state) : Prop :=
  (exists m z, bridge m z /\
    s1 = observe (masked_impl m) /\ s2 = observe (mixed_spec z)) \/
  (exists m z h j b, bridge m z /\ bridge h j /\
    s1 = observe (Vis (Reply b) (fun ack =>
      masked_impl (if response_value ack then h else m))) /\
    s2 = observe (Vis (Reply b) (fun ack =>
      mixed_spec (if response_value ack then j else z)))).
Lemma MPSRoot m z : bridge m z ->
  mixed_protocol_sim (observe (masked_impl m)) (observe (mixed_spec z)).
Proof. intro H. left. exists m, z. auto. Qed.

Lemma mixed_protocol_sim_postfixed : forall s1 s2, mixed_protocol_sim s1 s2 ->
  progress (upto mixed_protocol_sim) s1 s2.
Proof.
  intros s1 s2 [[m [z [Hmz [-> ->]]]]|[m [z [h [j [b [Hmz [Hhj [-> ->]]]]]]]]].
  - rewrite masked_impl_unfold mixed_spec_unfold.
    apply stable_hitting_match_vis. intro answer.
    eapply prob_upto_closure_sample.
    + exact (mixed_samples_lift (response_value answer)).
    + intros [b|[b h]] [b'|[b' j]] H; simpl in H; try contradiction.
      * subst b'. right. apply peutt_ret. reflexivity.
      * destruct H as [<- Hhj]. left. right.
        exists m, z, h, j, b. auto.
  - apply stable_hitting_match_vis. intro ack.
    apply prob_upto_closure_includes, MPSRoot.
    exact (bridge_next (response_value ack) Hmz Hhj).
Qed.

Theorem mixed_head_bridge m z :
  bridge m z -> masked_impl m ≈ₚ mixed_spec z.
Proof.
  intro H. eapply peutt_coinduction_upto_prob
    with (sim := mixed_protocol_sim); try typeclasses eauto.
  - exact mixed_protocol_sim_postfixed.
  - exact (MPSRoot H).
Qed.

(** L1 relates to both abstract states; no second coinduction is needed. *)
Lemma mixed_spec_states_equivalent z z' : mixed_spec z ≈ₚ mixed_spec z'.
Proof.
  transitivity (masked_impl L1).
  - symmetry. apply mixed_head_bridge. exact I.
  - apply mixed_head_bridge. exact I.
Qed.
Theorem masked_protocol_equivalent m : masked_impl m ≈ₚ canonical_spec.
Proof.
  transitivity (mixed_spec (match m with L2 => true | _ => false end)).
  - apply mixed_head_bridge. destruct m; simpl; auto.
  - apply mixed_spec_states_equivalent.
Qed.

(** The Challenge case is a totality default: after-challenge witnesses
    contain only returns and Reply events, as the following proof shows. *)
Definition stable_outcome (h : mixed_head) : mixed_outcome :=
  match h with
  | FHRet b => Stop b
  | @FHVis _ _ _ X e _ =>
      match e with Challenge => Stop false | Reply b => Continue b end
  end.
Definition sample_outcome {H} (x : bool + bool * H) : mixed_outcome :=
  match x with inl b => Stop b | inr (b,_) => Continue b end.
Lemma masked_head_outcome m x : stable_outcome (masked_head m x) = sample_outcome x.
Proof. destruct x as [b|[b h]]; reflexivity. Qed.
Definition masked_outcome_observation c : SubEnumQ mixed_outcome :=
  subenumQ_bind (mixed_samples uniform3 c) (fun x => subenumQ_ret (sample_outcome x)).

(** Analysis boundary: erase hidden state, recovering the same four masses. *)
Lemma masked_after_heads_denote_four m c :
  @free_omega_denotes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    mixed_head mixed_outcome stable_outcome (masked_after_heads m c) (mixed_outcomes c).
Proof.
  exists (masked_outcome_observation c). split.
  - unfold masked_after_heads, masked_outcome_observation.
    apply (FOOObserveSample (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)). intro x.
    rewrite <- (masked_head_outcome m x). constructor.
  - change (enumQ_meas_eq (subenumQ_raw (masked_outcome_observation c)) (mixed_outcomes_raw c)).
    apply enumQ_meas_eq_of_eqenum. intros [b|b]; destruct c,b;
      apply val_inj; vm_compute; reflexivity.
Qed.

(** Connect the observable distribution to an actual complete-hitting
    witness of the implementation, not merely a standalone measure. *)
Theorem masked_after_stable_hitting m c :
  exists out : MF mixed_head,
    hitting (observe (masked_after m c)) out /\
    @free_omega_denotes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
      mixed_head mixed_outcome stable_outcome out (mixed_outcomes c).
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
Definition spec_true_reply_query c : MF bool :=
  @sem_bind MF FI mixed_head bool (spec_after_heads false c) (fun h =>
    @sem_ret MF FI bool (observe_stable_head (fun _ => false) (@accepts_true_reply) h)).
Definition spec_true_reply_observation c : SubEnumQ bool :=
  subenumQ_bind (mixed_outcomes c) (fun o =>
    subenumQ_ret (match o with Stop _ => false | Continue b => b end)).

Lemma spec_after_true_reply_query c :
  @next_event_query mixedE SubEnumQ MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool (@accepts_true_reply) (mixed_after false c) (spec_true_reply_query c).
Proof.
  exists (spec_after_heads false c). split; [exact (spec_after_hitting false c)|apply sem_eq_refl].
Qed.
Lemma true_reply_selector_accepts :
  @selector_accept mixedE (@select_true_reply) = @accepts_true_reply.
Proof.
  apply functional_extensionality_dep. intro X.
  apply functional_extensionality. intro e. destruct e; [reflexivity|].
  destruct b; reflexivity.
Qed.
Lemma spec_challenge_true_reply_query c :
  @finite_interaction_query mixedE SubEnumQ MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool (challenge_true_reply_trace c)
    canonical_spec (spec_true_reply_query c).
Proof.
  unfold challenge_true_reply_trace.
  change (@finite_interaction_query mixedE SubEnumQ MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (cons (@select_challenge c) (cons (@select_true_reply) nil))
    (Vis Challenge (fun answer => mixed_after false (response_value answer))) (spec_true_reply_query c)).
  eapply finite_interaction_query_vis_match.
  - reflexivity.
  - apply (proj2 (finite_interaction_query_singleton_iff_next_event_query
      (@select_true_reply) (mixed_after false c) (spec_true_reply_query c))).
    rewrite true_reply_selector_accepts. exact (spec_after_true_reply_query c).
Qed.
Lemma spec_true_reply_query_denotes c :
  @free_omega_denotes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    bool bool id (spec_true_reply_query c) (spec_true_reply_observation c).
Proof.
  exists (subenumQ_bind (mixed_samples uniform2 c) (fun x =>
    subenumQ_ret (match sample_outcome x with Stop _ => false | Continue b => b end))).
  split.
  - unfold spec_true_reply_query, spec_after_heads.
    cbn [free_omega_bind]. apply (FOOObserveSample (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
    intros [b|[b j]]; constructor.
  - change (enumQ_meas_eq
      (subenumQ_raw (subenumQ_bind (mixed_samples uniform2 c) (fun x =>
        subenumQ_ret (match sample_outcome x with Stop _ => false | Continue b => b end))))
      (subenumQ_raw (spec_true_reply_observation c))).
    apply enumQ_meas_eq_of_eqenum. intros []; destruct c;
      apply val_inj; vm_compute; reflexivity.
Qed.
Lemma spec_true_reply_mass c :
  enumQ_expect subenumQ_bool_indicator (subenumQ_raw (spec_true_reply_observation c)) =
    (if c then 1 / 8 else 3 / 8).
Proof. destruct c; vm_compute; reflexivity. Qed.

(** Ret mass rejects the nonempty remaining prefix; only Continue(true)
    reaches the second selected event. Challenge false gives mass 3/8,
    challenge true gives mass 1/8, independently of hidden state m. *)
Theorem masked_challenge_true_reply_probability m c :
  Prₛ[ masked_impl m | challenge_true_reply_trace c ] = (if c then 1 / 8 else 3 / 8 : rat).
Proof.
  destruct (peutt_preserves_finite_interaction_query
    (peutt_sym (masked_protocol_equivalent m))
    (spec_challenge_true_reply_query c)) as [query [Hquery Hlift]].
  eapply subenumQ_finite_interaction_probability_intro
    with (query := query) (representative := spec_true_reply_query c)
      (out := spec_true_reply_observation c).
  - exact Hquery.
  - exact Hlift.
  - exact (spec_true_reply_query_denotes c).
  - exact (spec_true_reply_mass c).
Qed.
