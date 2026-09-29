(** Case role: paper case study.
    Reading entry: mixed_head_bridge; masked_protocol_equivalent; masked_challenge_true_reply_probability.
    Scope: SubEnumQ / observable FreeOmega; mixed return/visible frontiers require the displayed invariant.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
(** Learn: heterogeneous up-to-bind matches a branching Boolean sampler to
    a one-shot specification. The same non-functional 3-to-2 coupling
    abstracts both return payloads and recursive hidden continuations.
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
From PTree.Eq Require Import PEutt Bind.
From PTree.Prob.FreeOmega Require Import BindOrder.
From PTree.Eq.Backend Require Import ProbabilisticTraceSubEnumQ.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ PTree.Prob.Backend.EnumQ.Map IndexedCoupling PTree.Prob.Backend.EnumQ.Coupling GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope subenumQ_probability_scope.

(** The event universe is invariant in PTree. This two-response wrapper
    lifts an ordinary Boolean to that universe without changing its choices.
    This concrete case needs only one event universe: leave it inferred,
    rather than making the event family and each finite lemma polymorphic. *)
Variant mixed_response : Type := Response (response_bit : bool).
Definition response_value (r : mixed_response) : bool :=
  match r with Response b => b end.
Variant mixedE : Type -> Type :=
| Challenge : mixedE mixed_response
| Reply (b : bool) : mixedE mixed_response.

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

(** The implementation uses Boolean coins, not a primitive ternary draw. *)
Definition coin_third_raw : EnumQ bool.
Proof.
  refine (enumQ_of_list (mu := [:: (1 / 3, true); (2 / 3, false)]) _).
  intros p x [He|[He|[]]]; inversion He; subst; by vm_compute.
Defined.
Lemma coin_third_bound : enumQ_subprob coin_third_raw.
Proof. by vm_compute. Qed.
Definition coin_third := enumQ_as_subprob coin_third_bound.
Definition coin_three_quarters_raw : EnumQ bool.
Proof.
  refine (enumQ_of_list (mu := [:: (3 / 4, true); (1 / 4, false)]) _).
  intros p x [He|[He|[]]]; inversion He; subst; by vm_compute.
Defined.
Lemma coin_three_quarters_bound : enumQ_subprob coin_three_quarters_raw.
Proof. by vm_compute. Qed.
Definition coin_three_quarters := enumQ_as_subprob coin_three_quarters_bound.

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

Lemma coupling32_lift :
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

(** The same abstraction relates return payloads and recursive hidden states.
    The public bit is preserved; the payload relation is deliberately not a
    function (L1 relates to both abstract values). *)
Definition impl_return := (bool * hidden3)%type.
Definition spec_return := (bool * bool)%type.
Definition return_rel (x : impl_return) (y : spec_return) : Prop :=
  fst x = fst y /\ bridge (snd x) (snd y).

Example return_abstraction_boundary b :
  return_rel (b,L1) (b,false) /\ return_rel (b,L1) (b,true) /\
  ~ return_rel (b,L0) (b,true) /\ ~ return_rel (b,L1) (negb b,false).
Proof. destruct b; unfold return_rel, bridge; simpl; intuition discriminate. Qed.

(** Program-facing kernel: both Stop and Continue sample the same payload.
    Native bind describes the flattened finite law; the main up-to-bind
    proof consumes the sampler relation, without expanding lists. *)
Definition mixed_samples {H} (hidden : SubEnumQ H) c : SubEnumQ (bool * H + bool * H) :=
  sem_bind (mixed_outcomes c) (fun o =>
    sem_bind hidden (fun h => sem_ret
      (match o with Stop b => inl (b,h) | Continue b => inr (b,h) end))).
Definition mixed_sample_rel (x : impl_return + impl_return)
    (y : spec_return + spec_return) : Prop :=
  match x, y with
  | inl r, inl u | inr r, inr u => return_rel r u
  | _, _ => False
  end.
Lemma mixed_samples_lift c :
  @sem_lift SubEnumQ SubEnumQ_SemanticMeasure _ _ mixed_sample_rel
    (mixed_samples uniform3 c) (mixed_samples uniform2 c).
Proof.
  unfold mixed_samples. eapply sem_lift_bind with (R := eq).
  - apply sem_lift_refl. congruence.
  - intros o o' <-. eapply sem_lift_bind; [exact coupling32_lift|].
    intros h j Hhj. apply sem_lift_ret.
    destruct o; split; [reflexivity|exact Hhj|reflexivity|exact Hhj].
Qed.

Definition tri_distribution : SubEnumQ hidden3 :=
  sem_bind coin_third (fun x => if x then sem_ret L0 else
    sem_bind uniform2 (fun y => sem_ret (if y then L1 else L2))).
Definition draw_distribution c : SubEnumQ (impl_return + impl_return) :=
  sem_bind coin_three_quarters (fun s =>
    sem_bind uniform2 (fun q =>
      sem_bind coin_third (fun x =>
        if x then sem_ret (if q then inr (xorb c s,L0) else inl (xorb c s,L0))
        else sem_bind uniform2 (fun y =>
          sem_ret (if q then inr (xorb c s,if y then L1 else L2)
                        else inl (xorb c s,if y then L1 else L2)))))).
Lemma tri_distribution_uniform : sem_eq tri_distribution uniform3.
Proof.
  apply enumQ_meas_eq_of_eqenum. intros []; apply val_inj; vm_compute; reflexivity.
Qed.
Lemma draw_distribution_mixed c : sem_eq (draw_distribution c) (mixed_samples uniform3 c).
Proof.
  change (enumQ_meas_eq (subenumQ_raw (draw_distribution c))
    (subenumQ_raw (mixed_samples uniform3 c))).
  apply (@enumQ_meas_eq_of_eqenum
    (@Equality.Pack (impl_return + impl_return)%type (Equality.on (impl_return + impl_return)%type))).
  intros [[b h]|[b h]]; destruct c,b,h;
    apply val_inj; vm_compute; reflexivity.
Qed.

Set Universe Polymorphism.

Local Notation tree := (ptree mixedE SubEnumQ).
Local Notation state A := (ptree' mixedE SubEnumQ A).
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation mixed_head A := (stable_head mixedE SubEnumQ A).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation MX := (@FreeOmegaMixedMeasure SubEnumQ).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation kernel A := (@ptree_primitive_kernel mixedE SubEnumQ MF FI MX A).
Local Notation hitting A := (@ptree_stable_hitting mixedE SubEnumQ MF FI MX FO A).
(** Fix the observable interpretation once, exactly as in FactoryController;
    this is notation for raw peutt, not an additional relation. *)
Local Notation W := (PEutt.peutt (E := mixedE) (MN := SubEnumQ)
  (MF := MF) (FI := FI) (FC := FC) (MX := MX) (FO := FO)).
Local Notation "t ≈ₚ u" := (W eq t u)
  (at level 70, no associativity) : type_scope.
Local Notation "t ≈ₚ[ RR ] u" := (W RR t u)
  (at level 70, RR at next level, no associativity) : type_scope.
Local Notation upto := (bind_upto_closure
  (FI := FI) (FC := FC) (MX := MX) (FO := FO) return_rel).
Local Notation progress := (stable_hitting_match (FI := FI) (FO := FO)
  (kernel impl_return) (kernel spec_return)
  (@ptree_stable_head_rel mixedE SubEnumQ impl_return spec_return return_rel)).

Definition tri_sample : tree hidden3 :=
  Prob coin_third (fun x => if x then Ret L0 else
    Prob uniform2 (fun y => Ret (if y then L1 else L2))).
Definition impl_draw c : tree (impl_return + impl_return) :=
  Prob coin_three_quarters (fun s =>
    Prob uniform2 (fun q =>
      PTree.bind tri_sample (fun h =>
        Ret (if q then inr (xorb c s, h) else inl (xorb c s, h))))).
Definition spec_draw c : tree (spec_return + spec_return) :=
  Prob (mixed_samples uniform2 c) (fun x => Ret x).

(** Compile only the finite sampler, supplying all witnesses explicitly.
    No choice of recursive frontiers or analysis of qlift derivations. *)
Lemma tri_sample_hitting : hitting hidden3 (observe tri_sample)
  (FOSample uniform3 (fun h => FORet (FHRet h))).
Proof.
  eapply stable_hitting_output_transport with
    (out := FOSample tri_distribution (fun h => FORet (FHRet h))).
  - unfold tri_sample, tri_distribution. apply stable_hitting_native_sample. intros [].
    + apply stable_hitting_native_ret.
    + apply stable_hitting_native_sample. intro y. apply stable_hitting_native_ret.
  - eapply FOQLSample; [exact tri_distribution_uniform|].
    intros h h' ->. apply free_omega_qlift_refl. intro a. reflexivity.
Qed.

Theorem tri_sample_uniform : tri_sample ≈ₚ Prob uniform3 (fun h => Ret h).
Proof.
  eapply peutt_of_hitting_lift.
  - exact tri_sample_hitting.
  - eapply (stable_hitting_prob (FI := FI) (FO := FO) (MX := MX))
      with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros h _. apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := MX)).
  - eapply FOQLSample with (T := eq); [apply sem_lift_refl; congruence|].
    intros h h' ->. apply FOQLStructural. constructor. constructor. reflexivity.
Qed.

Lemma impl_draw_hitting c : hitting (impl_return + impl_return) (observe (impl_draw c))
  (FOSample (mixed_samples uniform3 c) (fun x => FORet (FHRet x))).
Proof.
  eapply stable_hitting_output_transport with
    (out := FOSample (draw_distribution c) (fun x => FORet (FHRet x))).
  - unfold impl_draw, draw_distribution. apply stable_hitting_native_sample. intro s.
    apply stable_hitting_native_sample. intro q.
    rewrite observe_bind. cbn [tri_sample observe].
    apply stable_hitting_native_sample. intros [].
    + apply stable_hitting_native_ret.
    + rewrite observe_bind. cbn [observe].
      apply stable_hitting_native_sample. intro y. apply stable_hitting_native_ret.
  - eapply FOQLSample; [exact (draw_distribution_mixed c)|].
    intros x y ->. apply free_omega_qlift_refl. intro a. reflexivity.
Qed.

Lemma spec_draw_hitting c : hitting (spec_return + spec_return) (observe (spec_draw c))
  (FOSample (mixed_samples uniform2 c) (fun x => FORet (FHRet x))).
Proof.
  unfold spec_draw. eapply (stable_hitting_prob (FI := FI) (FO := FO) (MX := MX))
    with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros x _. apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := MX)).
Qed.

Theorem impl_draw_related c : impl_draw c ≈ₚ[mixed_sample_rel] spec_draw c.
Proof.
  eapply peutt_of_hitting_lift.
  - exact (impl_draw_hitting c).
  - exact (spec_draw_hitting c).
  - eapply FOQLSample; [exact (mixed_samples_lift c)|].
    intros x y H. apply FOQLStructural. constructor. constructor. exact H.
Qed.

(** The implementation performs three or four Boolean draws per round;
    the specification samples its complete round in one shot. Binding the
    finite prefix is accepted by the ordinary corecursion guard checker.
    Only Challenge/Reply, never internal sampling, guard the bisimulation. *)
CoFixpoint masked_impl (m : hidden3) : tree impl_return :=
  Vis Challenge (fun answer =>
    PTree.bind (impl_draw (response_value answer)) (fun x =>
      match x with
      | inl b => Ret b
      | inr (b,h) => Vis (Reply b) (fun ack =>
          masked_impl (if response_value ack then h else m))
      end)).
CoFixpoint mixed_spec (z : bool) : tree spec_return :=
  Vis Challenge (fun answer =>
    PTree.bind (spec_draw (response_value answer)) (fun x =>
      match x with
      | inl b => Ret b
      | inr (b,j) => Vis (Reply b) (fun ack =>
          mixed_spec (if response_value ack then j else z))
      end)).
(** Only initialization chooses a related state; this is not a deterministic
    transport of the uniform3 sampling distribution (which is impossible). *)
Definition abstract_state m := match m with L2 => true | _ => false end.
Definition canonical_spec m := mixed_spec (abstract_state m).
Definition masked_branch m (x : impl_return + impl_return) : tree impl_return :=
  match x with
  | inl b => Ret b
  | inr (b,h) => Vis (Reply b) (fun ack =>
      masked_impl (if response_value ack then h else m))
  end.
Definition spec_branch z (x : spec_return + spec_return) : tree spec_return :=
  match x with
  | inl b => Ret b
  | inr (b,j) => Vis (Reply b) (fun ack =>
      mixed_spec (if response_value ack then j else z))
  end.
Definition masked_after m c := PTree.bind (impl_draw c) (masked_branch m).
Definition mixed_after z c := PTree.bind (spec_draw c) (spec_branch z).
Lemma masked_impl_unfold m : observe (masked_impl m) = VisF Challenge (fun answer => masked_after m (response_value answer)).
Proof. reflexivity. Qed.
Lemma mixed_spec_unfold z : observe (mixed_spec z) = VisF Challenge (fun answer => mixed_after z (response_value answer)).
Proof. reflexivity. Qed.

Example masked_impl_probabilistic m : probabilistic_ptree (masked_impl m).
Proof. apply probabilistic_ptree_intrinsic. Qed.
Example mixed_spec_probabilistic z : probabilistic_ptree (mixed_spec z).
Proof. apply probabilistic_ptree_intrinsic. Qed.

Definition masked_head m (x : impl_return + impl_return) : mixed_head impl_return :=
  match x with
  | inl b => FHRet b
  | inr (b,h) => FHVis (Reply b) (fun ack =>
      masked_impl (if response_value ack then h else m))
  end.
Definition spec_head z (x : spec_return + spec_return) : mixed_head spec_return :=
  match x with
  | inl b => FHRet b
  | inr (b,j) => FHVis (Reply b) (fun ack =>
      mixed_spec (if response_value ack then j else z))
  end.
Definition masked_after_heads m c : MF (mixed_head impl_return) :=
  FOSample (mixed_samples uniform3 c) (fun x => FORet (masked_head m x)).
Definition spec_after_heads z c : MF (mixed_head spec_return) :=
  FOSample (mixed_samples uniform2 c) (fun x => FORet (spec_head z x)).

Lemma masked_after_hitting m c : hitting impl_return (observe (masked_after m c)) (masked_after_heads m c).
Proof.
  unfold masked_after, masked_after_heads.
  eapply stable_hitting_bind_ret_only with
    (hs := FOSample (mixed_samples uniform3 c) (fun x => FORet (FHRet x)))
    (front := fun x => FORet (masked_head m x)).
  - eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros x _. constructor. exact I.
  - exact (impl_draw_hitting c).
  - intros [b|[b h]].
    + apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := MX)).
    + apply (stable_hitting_vis (FI := FI) (FO := FO) (MX := MX)).
Qed.
Lemma spec_after_hitting z c : hitting spec_return (observe (mixed_after z c)) (spec_after_heads z c).
Proof.
  unfold mixed_after, spec_after_heads.
  eapply stable_hitting_bind_ret_only with
    (hs := FOSample (mixed_samples uniform2 c) (fun x => FORet (FHRet x)))
    (front := fun x => FORet (spec_head z x)).
  - eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros x _. constructor. exact I.
  - exact (spec_draw_hitting c).
  - intros [b|[b j]].
    + apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := MX)).
    + apply (stable_hitting_vis (FI := FI) (FO := FO) (MX := MX)).
Qed.

(** Only roots and replies belong to the invariant. The reply obligation
    carries BOTH the old bridge and the new bridge supplied by the joint. *)
Definition mixed_protocol_sim (s1 : state impl_return) (s2 : state spec_return) : Prop :=
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
    eapply bind_upto_closure_bind.
    + exact (impl_draw_related (response_value answer)).
    + intros [r|[b h]] [u|[b' j]] H; simpl in H; try contradiction.
      * right. apply peutt_ret. exact H.
      * destruct H as [Hbit Hhj]. simpl in Hbit, Hhj. subst b'. left. right.
        exists m, z, h, j, b. auto.
  - apply stable_hitting_match_vis. intro ack.
    apply bind_upto_closure_includes, MPSRoot.
    exact (bridge_next (response_value ack) Hmz Hhj).
Qed.

Theorem mixed_head_bridge m z :
  bridge m z -> masked_impl m ≈ₚ[return_rel] mixed_spec z.
Proof.
  intro H. eapply peutt_coinduction_upto_bind
    with (sim := mixed_protocol_sim); try typeclasses eauto.
  - intros. apply ptree_bind_cofinal_all.
  - exact mixed_protocol_sim_postfixed.
  - exact (MPSRoot H).
Qed.

(** A related initialization suffices; no invalid symmetry/transitivity
    step treats the heterogeneous return relation as equality. *)
Theorem masked_protocol_equivalent m : masked_impl m ≈ₚ[return_rel] canonical_spec m.
Proof.
  apply mixed_head_bridge. destruct m; simpl; auto.
Qed.

(** Erasing the abstracted payload recovers ordinary Boolean equivalence,
    using the library's heterogeneous bind law, not a second coinduction. *)
Theorem masked_public_protocol_equivalent m :
  PTree.bind (masked_impl m) (fun r => Ret (fst r)) ≈ₚ
  PTree.bind (canonical_spec m) (fun u => Ret (fst u)).
Proof.
  eapply peutt_bind with (RR := return_rel).
  - apply masked_protocol_equivalent.
  - intros r u [Hbit _]. apply peutt_ret. exact Hbit.
Qed.

(** The Challenge case is a totality default: after-challenge witnesses
    contain only returns and Reply events, as the following proof shows. *)
Definition stable_outcome {H} (h : mixed_head (bool * H)) : mixed_outcome :=
  match h with
  | FHRet r => Stop (fst r)
  | @FHVis _ _ _ X e _ =>
      match e with Challenge => Stop false | Reply b => Continue b end
  end.
Definition sample_outcome {H} (x : bool * H + bool * H) : mixed_outcome :=
  match x with inl (b,_) => Stop b | inr (b,_) => Continue b end.
Lemma masked_head_outcome m x : stable_outcome (masked_head m x) = sample_outcome x.
Proof. destruct x as [[b h]|[b h]]; reflexivity. Qed.
Definition masked_outcome_observation c : SubEnumQ mixed_outcome :=
  subenumQ_bind (mixed_samples uniform3 c) (fun x => subenumQ_ret (sample_outcome x)).

(** Analysis boundary: erase hidden state, recovering the same four masses. *)
Lemma masked_after_heads_denote_four m c :
  @free_omega_denotes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    (mixed_head impl_return) mixed_outcome stable_outcome (masked_after_heads m c) (mixed_outcomes c).
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
  exists out : MF (mixed_head impl_return),
    hitting impl_return (observe (masked_after m c)) out /\
    @free_omega_denotes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
      (mixed_head impl_return) mixed_outcome stable_outcome out (mixed_outcomes c).
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
Definition spec_true_reply_query z c : MF bool :=
  @sem_bind MF FI (mixed_head spec_return) bool (spec_after_heads z c) (fun h =>
    @sem_ret MF FI bool (observe_stable_head (fun _ => false) (@accepts_true_reply) h)).
Definition spec_true_reply_observation c : SubEnumQ bool :=
  subenumQ_bind (mixed_outcomes c) (fun o =>
    subenumQ_ret (match o with Stop _ => false | Continue b => b end)).

Lemma spec_after_true_reply_query z c :
  @next_event_query mixedE SubEnumQ MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega spec_return (@accepts_true_reply) (mixed_after z c) (spec_true_reply_query z c).
Proof.
  exists (spec_after_heads z c). split; [exact (spec_after_hitting z c)|apply sem_eq_refl].
Qed.
Lemma true_reply_selector_accepts :
  @selector_accept mixedE (@select_true_reply) = @accepts_true_reply.
Proof.
  apply functional_extensionality_dep. intro X.
  apply functional_extensionality. intro e. destruct e; [reflexivity|].
  destruct b; reflexivity.
Qed.
Lemma spec_challenge_true_reply_query m c :
  @finite_interaction_query mixedE SubEnumQ MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega spec_return (challenge_true_reply_trace c)
    (canonical_spec m) (spec_true_reply_query (abstract_state m) c).
Proof.
  unfold challenge_true_reply_trace.
  change (@finite_interaction_query mixedE SubEnumQ MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega spec_return
    (cons (@select_challenge c) (cons (@select_true_reply) nil))
    (Vis Challenge (fun answer => mixed_after (abstract_state m) (response_value answer)))
    (spec_true_reply_query (abstract_state m) c)).
  eapply finite_interaction_query_vis_match.
  - reflexivity.
  - apply (proj2 (finite_interaction_query_singleton_iff_next_event_query
      (@select_true_reply) (mixed_after (abstract_state m) c) (spec_true_reply_query (abstract_state m) c))).
    rewrite true_reply_selector_accepts. exact (spec_after_true_reply_query (abstract_state m) c).
Qed.
Lemma spec_true_reply_query_denotes z c :
  @free_omega_denotes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    bool bool id (spec_true_reply_query z c) (spec_true_reply_observation c).
Proof.
  exists (subenumQ_bind (mixed_samples uniform2 c) (fun x =>
    subenumQ_ret (match sample_outcome x with Stop _ => false | Continue b => b end))).
  split.
  - unfold spec_true_reply_query, spec_after_heads.
    cbn [free_omega_bind]. apply (FOOObserveSample (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
    intros [[b j]|[b j]]; constructor.
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
  destruct (finite_interaction_query_exists (FI := FI) (FO := FO) (MX := MX)
    (challenge_true_reply_trace c) (masked_impl m)) as [query Hquery].
  eapply subenumQ_finite_interaction_probability_intro
    with (query := query) (representative := spec_true_reply_query (abstract_state m) c)
      (out := spec_true_reply_observation c).
  - exact Hquery.
  - eapply sem_lift_mono; [|apply sem_lift_sym;
      exact (finite_interaction_query_related (masked_protocol_equivalent m)
        Hquery (spec_challenge_true_reply_query m c))].
    intros x y ->. reflexivity.
  - exact (spec_true_reply_query_denotes (abstract_state m) c).
  - exact (spec_true_reply_mass c).
Qed.
