(** * MixedHead: different samplers, related recursive protocols

    Case role: paper case study. Native/frontier: SubEnumQ / observable
    FreeOmega. The implementation uses several Boolean draws; the
    specification samples one complete outcome. One 3-to-2 joint relates
    BOTH heterogeneous return payloads and recursive visible continuations.

    Reading path (four layers in this one file):
    - Preparation: protocol types, native coins, observable backend profile.
    - Programs: the complete [masked_impl] and [mixed_spec].
    - Lemma preparation: finite couplings, frontier/query analysis, invariant.
    - Main theorem: [masked_protocol_equivalent], with the composition proof in place.
    - Consequences: [masked_public_protocol_equivalent] and
      [masked_challenge_true_reply_probability].

    This is a bisimulation example, not a pure rewrite proof or an execution
    demo. The finite analysis can be skipped on a first reading. See
    docs/CASE_STUDIES.md and docs/CASE_STUDY_STANDARD.md. *)
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
From PTree.Prob.Backend.EnumQ Require Import
  Representation Bind Map Coupling IndexedCoupling FrontierLift Iteration.
From PTree.Prob.Interface Require Import Measure Subprobability AE Coupling Omega Mixed.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import
  Approximation Observation StructuralMeasure SupportLift Quotient Measure.
From PTree.Eq Require Import
  Shallow UnifiedFrontier PrimitiveStableHitting PTreeKernel ProbabilisticTrace.
From PTree.Eq.FreeOmega Require Import Base Hitting Relation Bind Algebra Iter.
From PTree.Eq Require Import PEutt Bind.
From PTree.Prob.FreeOmega Require Import BindOrder.
From PTree.Eq.Backend Require Import ProbabilisticTraceSubEnumQ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ PTree.Prob.Backend.EnumQ.Map IndexedCoupling
  PTree.Prob.Backend.EnumQ.Coupling GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.
Local Open Scope subenumQ_probability_scope.

(** * 1. Preparation *)

(** ** Protocol types and return abstraction *)

(** The environment supplies an ordinary Boolean challenge and acknowledgement. *)
Variant mixedE : Type -> Type :=
| Challenge : mixedE bool
| Reply (b : bool) : mixedE bool.

Variant mixed_outcome := Stop (b : bool) | Continue (b : bool).
Scheme Equality for mixed_outcome.

Lemma mixed_outcome_eqP : Equality.axiom mixed_outcome_beq.
Proof. intros [[]|[]] [[]|[]]; constructor; congruence. Qed.

HB.instance Definition _ := hasDecEq.Build mixed_outcome mixed_outcome_eqP.

Variant hidden3 := L0 | L1 | L2.
Scheme Equality for hidden3.

Lemma hidden3_eqP : Equality.axiom hidden3_beq.
Proof. intros [] []; constructor; congruence. Qed.

HB.instance Definition _ := hasDecEq.Build hidden3 hidden3_eqP.

(** Allowed pairs in the 3-to-2 abstraction: L0 ~ false, L1 ~ false/true,
    L2 ~ true. This is a relation, not a deterministic map or a coupling:
    [coupling32] below supplies the joint weights supported on these pairs. *)
Definition bridge m z : Prop :=
  match m with L0 => z = false | L1 => True | L2 => z = true end.

(** A shared Reply acknowledgement preserves the abstraction: false keeps
    the related old states (m,z); true installs the related fresh states
    (h,j). This closes the recursive continuation after either response. *)
Lemma bridge_next m z h j (a : bool) :
  bridge m z -> bridge h j ->
  bridge (if a then h else m) (if a then j else z).
Proof. destruct a; auto. Qed.

(** The same abstraction relates return payloads and recursive hidden states.
    The public bit is preserved; the payload relation is deliberately not a
    function (L1 relates to both abstract values). *)
Definition impl_return := (bool * hidden3)%type.

Definition spec_return := (bool * bool)%type.

Definition return_rel (x : impl_return) (y : spec_return) : Prop :=
  fst x = fst y /\ bridge (snd x) (snd y).

(** ** Native coins and the specification kernel

    This is the SubEnumQ construction boundary. The programs below consume
    only the named coins and the abstract [sem_ret]/[sem_bind] interface. *)

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

(** Public b = c xor s, with s biased 3/4; Stop/Continue is fair.
    Combine these independent draws into their four-outcome kernel. *)
Definition mixed_eighth : rat := 1 / 8.

Definition mixed_three_eighths : rat := 3 / 8.

Definition mixed_outcomes_raw (c : bool) : EnumQ mixed_outcome.
Proof.
  refine (enumQ_of_list (mu :=
    let w0 := if c then mixed_three_eighths else mixed_eighth in
    let w1 := if c then mixed_eighth else mixed_three_eighths in
    [:: (w0, Stop false); (w1, Stop true);
        (w0, Continue false); (w1, Continue true)]) _).
  intros p x [He|[He|[He|[He|[]]]]]; inversion He; subst; destruct c; by vm_compute.
Defined.

Lemma mixed_outcomes_bound c : enumQ_subprob (mixed_outcomes_raw c).
Proof. destruct c; by vm_compute. Qed.

Definition mixed_outcomes c := enumQ_as_subprob (mixed_outcomes_bound c).

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

(** ** Observable backend profile

    Fix it once; the program and main theorem use only the short names below. *)
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
Local Notation hitting A := (@ptree_stable_hitting mixedE SubEnumQ MF FI MX FO A).

(** Fix the observable interpretation once, exactly as in FactoryController;
    this is notation for raw peutt, not an additional relation. *)
Local Notation W := (PEutt.peutt (E := mixedE) (MN := SubEnumQ)
  (MF := MF) (FI := FI) (FC := FC) (MX := MX) (FO := FO)).
Local Notation "t ≈ₚ u" := (W eq t u)
  (at level 70, no associativity) : type_scope.
Local Notation "t ≈ₚ[ RR ] u" := (W RR t u)
  (at level 70, RR at next level, no associativity) : type_scope.

(** * 2. The complete programs

    No named intermediate program is needed. The implementation draws a
    mask, a Stop/Continue choice, then a ternary payload using one or two
    Boolean draws. The specification samples the complete outcome at once.
    Both expose Challenge, then either return or offer Reply and recurse. *)

CoFixpoint masked_impl (m : hidden3) : tree impl_return :=
  Vis Challenge (fun c =>
    PTree.bind
      (Prob coin_three_quarters (fun mask =>
        Prob uniform2 (fun continue =>
          PTree.bind
            (Prob coin_third (fun first =>
              if first then Ret L0
              else Prob uniform2 (fun second => Ret (if second then L1 else L2))))
            (fun payload =>
              let bit := xorb c mask in
              Ret (if continue then inr (bit, payload) else inl (bit, payload))))))
      (fun x => match x with
        | inl result => Ret result
        | inr (b,h) => Vis (Reply b) (fun ack =>
            masked_impl (if ack then h else m))
        end)).

CoFixpoint mixed_spec (z : bool) : tree spec_return :=
  Vis Challenge (fun c =>
    PTree.bind (Prob (mixed_samples uniform2 c) (fun x => Ret x))
      (fun x => match x with
        | inl result => Ret result
        | inr (b,j) => Vis (Reply b) (fun ack =>
            mixed_spec (if ack then j else z))
        end)).

(** Initialization only; not a deterministic transport of uniform3. *)
Definition abstract_state m := match m with L2 => true | _ => false end.

Definition canonical_spec m := mixed_spec (abstract_state m).

(** * 3. Lemma preparation

    Only distribution calculations, observable measures and the recursive
    relation are prepared here. Program-level facts are proved at their use. *)

(** ** Finite distributions and the 3-to-2 joint

    The matrix below is the only coupling construction. Its middle row
    splits between both columns. Finite representation calculations end at
    [draw_distribution_mixed] and [mixed_samples_lift]. Actual program
    frontiers are constructed locally in the proofs that consume them. *)

Unset Universe Polymorphism.

Definition coupling32_raw : EnumQ (hidden3 * bool).
Proof.
  refine (enumQ_of_list (mu :=
    [:: (1/3, (L0,false)); (1/6, (L1,false));
        (1/6, (L1,true)); (1/3, (L2,true))]) _).
  intros p x [He|[He|[He|[He|[]]]]]; inversion He; subst; by vm_compute.
Defined.

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

Example return_abstraction_boundary b :
  return_rel (b,L1) (b,false) /\ return_rel (b,L1) (b,true) /\
  ~ return_rel (b,L0) (b,true) /\ ~ return_rel (b,L1) (negb b,false).
Proof. destruct b; unfold return_rel, bridge; simpl; intuition discriminate. Qed.

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

Definition draw_distribution c : SubEnumQ (impl_return + impl_return) :=
  sem_bind coin_three_quarters (fun s =>
    sem_bind uniform2 (fun q =>
      sem_bind coin_third (fun x =>
        if x then sem_ret (if q then inr (xorb c s,L0) else inl (xorb c s,L0))
        else sem_bind uniform2 (fun y =>
          sem_ret (if q then inr (xorb c s,if y then L1 else L2)
                        else inl (xorb c s,if y then L1 else L2)))))).

Lemma draw_distribution_mixed c : sem_eq (draw_distribution c) (mixed_samples uniform3 c).
Proof.
  change (enumQ_meas_eq (subenumQ_raw (draw_distribution c))
    (subenumQ_raw (mixed_samples uniform3 c))).
  apply (@enumQ_meas_eq_of_eqenum
    (@Equality.Pack (impl_return + impl_return)%type
      (Equality.on (impl_return + impl_return)%type))).
  intros [[b h]|[b h]]; destruct c,b,h;
    apply val_inj; vm_compute; reflexivity.
Qed.

Set Universe Polymorphism.

(** ** Complete frontiers and finite observations

    First retain an explicit complete frontier for each after-Challenge
    program. Then compute the two-event query on the simpler specification
    (the final theorem will transport this query to the implementation). *)

Definition masked_head m (x : impl_return + impl_return) : mixed_head impl_return :=
  match x with
  | inl b => FHRet b
  | inr (b,h) => FHVis (Reply b) (fun ack =>
      masked_impl (if ack then h else m))
  end.

Definition spec_head z (x : spec_return + spec_return) : mixed_head spec_return :=
  match x with
  | inl b => FHRet b
  | inr (b,j) => FHVis (Reply b) (fun ack =>
      mixed_spec (if ack then j else z))
  end.

Definition masked_after_heads m c : MF (mixed_head impl_return) :=
  FOSample (mixed_samples uniform3 c) (fun x => FORet (masked_head m x)).

Definition spec_after_heads z c : MF (mixed_head spec_return) :=
  FOSample (mixed_samples uniform2 c) (fun x => FORet (spec_head z x)).

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
    (mixed_head impl_return) mixed_outcome stable_outcome
    (masked_after_heads m c) (mixed_outcomes c).
Proof.
  exists (masked_outcome_observation c). split.
  - unfold masked_after_heads, masked_outcome_observation.
    apply (FOOObserveSample
      (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
    intro x.
    rewrite <- (masked_head_outcome m x). constructor.
  - change (enumQ_meas_eq (subenumQ_raw (masked_outcome_observation c)) (mixed_outcomes_raw c)).
    apply enumQ_meas_eq_of_eqenum. intros [b|b]; destruct c,b;
      apply val_inj; vm_compute; reflexivity.
Qed.

Definition select_challenge (c : bool) {X} (e : mixedE X) : option X :=
  match e in mixedE X0 return option X0 with
  | Challenge => Some c
  | Reply _ => None
  end.

Definition select_true_reply {X} (e : mixedE X) : option X :=
  match e in mixedE X0 return option X0 with
  | Challenge => None
  | Reply b => if b then Some true else None
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

Lemma true_reply_selector_accepts :
  @selector_accept mixedE (@select_true_reply) = @accepts_true_reply.
Proof.
  apply functional_extensionality_dep. intro X.
  apply functional_extensionality. intro e. destruct e; [reflexivity|].
  destruct b; reflexivity.
Qed.

Lemma spec_true_reply_query_denotes z c :
  @free_omega_denotes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    bool bool id (spec_true_reply_query z c) (spec_true_reply_observation c).
Proof.
  exists (subenumQ_bind (mixed_samples uniform2 c) (fun x =>
    subenumQ_ret (match sample_outcome x with Stop _ => false | Continue b => b end))).
  split.
  - unfold spec_true_reply_query, spec_after_heads.
    cbn [free_omega_bind].
    apply (FOOObserveSample
      (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
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

(** ** Recursive invariant: roots and replies

    The main proof composes the finite sampler relation without adding
    states for internal draws. Reply pairs carry both the old
    bridge and the fresh bridge supplied by the joint. *)

(** Only roots and replies belong to the invariant. The reply obligation
    carries BOTH the old bridge and the new bridge supplied by the joint. *)
Definition mixed_protocol_sim (s1 : state impl_return) (s2 : state spec_return) : Prop :=
  (exists m z, bridge m z /\
    s1 = observe (masked_impl m) /\ s2 = observe (mixed_spec z)) \/
  (exists m z h j b, bridge m z /\ bridge h j /\
    s1 = observe (Vis (Reply b) (fun ack =>
      masked_impl (if ack then h else m))) /\
    s2 = observe (Vis (Reply b) (fun ack =>
      mixed_spec (if ack then j else z)))).

(** * 4. Final theorems

    Main behavioral claim, public-result corollary, and quantitative endpoints.
    The complete program proof is below: unfold, compose prefixes with bind,
    discharge returns, then close the recursive visible continuations. *)

(** No caller-supplied bridge proof: [abstract_state] chooses a related
    initial specification state. The invariant below still records both
    the old and newly sampled state relations during recursive reasoning. *)
Theorem masked_protocol_equivalent m : masked_impl m ≈ₚ[return_rel] canonical_spec m.
Proof.
  (* Expose one round, then compose its prefix and continuation proofs. *)
  unfold canonical_spec.
  eapply peutt_coinduction_upto_bind
    with (sim := mixed_protocol_sim); try typeclasses eauto.
  - intros. apply ptree_bind_cofinal_all.
  - intros s1 s2 [(old & z & Hold & -> & ->) |
      (old & z & h & j & b & Hold & Hfresh & -> & ->)].
    + cbn [masked_impl mixed_spec observe].
      apply stable_hitting_match_vis. intro answer.
      eapply bind_upto_closure_bind with (RR := mixed_sample_rel).
      * (* Analyze this finite prefix here, not via a pre-proved program relation. *)
        eapply peutt_of_hitting_lift with
          (out1 := FOSample (draw_distribution answer) (fun x => FORet (FHRet x)))
          (out2 := FOSample (mixed_samples uniform2 answer) (fun x => FORet (FHRet x))).
        -- unfold draw_distribution.
           apply stable_hitting_native_sample. intro mask.
           apply stable_hitting_native_sample. intro continue.
           rewrite observe_bind. cbn [observe].
           apply stable_hitting_native_sample. intros [].
           ++ apply stable_hitting_native_ret.
           ++ rewrite observe_bind. cbn [observe].
              apply stable_hitting_native_sample. intro second.
              apply stable_hitting_native_ret.
        -- eapply (stable_hitting_prob (FI := FI) (FO := FO) (MX := MX))
             with (Good := fun _ => True).
           ++ apply sem_ae_true.
           ++ intros x _. apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := MX)).
        -- eapply FOQLSample with (T := mixed_sample_rel).
           ++ eapply sem_lift_proper_l; [apply sem_eq_sym, draw_distribution_mixed|].
              exact (mixed_samples_lift answer).
           ++ intros x y H. apply FOQLStructural. constructor. constructor. exact H.
      * intros [r|[b h]] [u|[b' j]] H; simpl in H; try contradiction.
        -- (* Stop: abstract the returned payload, preserving the public bit. *)
           right. apply peutt_ret. exact H.
        -- (* Continue: compose the fresh coupling with the Reply context. *)
           destruct H as [Hbit Hfresh]. simpl in Hbit, Hfresh. subst b'.
           left. right. exists old, z, h, j, b. auto.
    + (* After Reply, keep or refresh both states and re-enter the loop. *)
      apply stable_hitting_match_vis. intro ack.
      apply bind_upto_closure_includes. left.
      eexists _, _. split; [exact (bridge_next ack Hold Hfresh)|].
      split; reflexivity.
  - (* Initialization discharges the invariant internally. *)
    left. exists m, (abstract_state m). split.
    + destruct m; simpl; auto.
    + split; reflexivity.
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

(** Connect the observable distribution to an actual complete-hitting
    witness of the implementation, not merely a standalone measure. *)
Theorem masked_after_stable_hitting m c :
  exists (k : bool -> tree impl_return) (out : MF (mixed_head impl_return)),
    observe (masked_impl m) = VisF Challenge k /\
    hitting impl_return (observe (k c)) out /\
    @free_omega_denotes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
      (mixed_head impl_return) mixed_outcome stable_outcome out (mixed_outcomes c).
Proof.
  exists (fun c =>
    PTree.bind
      (Prob coin_three_quarters (fun mask =>
        Prob uniform2 (fun continue =>
          PTree.bind
            (Prob coin_third (fun first =>
              if first then Ret L0
              else Prob uniform2 (fun second => Ret (if second then L1 else L2))))
            (fun payload =>
              let bit := xorb c mask in
              Ret (if continue then inr (bit, payload) else inl (bit, payload))))))
      (fun x => match x with
        | inl result => Ret result
        | inr (b,h) => Vis (Reply b) (fun ack =>
            masked_impl (if ack then h else m))
        end)), (masked_after_heads m c).
  split; [reflexivity|]. split.
  - unfold masked_after_heads.
    eapply stable_hitting_bind_ret_only with
      (hs := FOSample (mixed_samples uniform3 c) (fun x => FORet (FHRet x)))
      (front := fun x => FORet (masked_head m x)).
    + eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
      intros x _. constructor. exact I.
    + eapply stable_hitting_output_transport with
        (out := FOSample (draw_distribution c) (fun x => FORet (FHRet x))).
      * unfold draw_distribution.
        apply stable_hitting_native_sample. intro mask.
        apply stable_hitting_native_sample. intro continue.
        rewrite observe_bind. cbn [observe].
        apply stable_hitting_native_sample. intros [].
        -- apply stable_hitting_native_ret.
        -- rewrite observe_bind. cbn [observe].
           apply stable_hitting_native_sample. intro second.
           apply stable_hitting_native_ret.
      * eapply FOQLSample; [exact (draw_distribution_mixed c)|].
        intros x y ->. apply free_omega_qlift_refl. intro a. reflexivity.
    + intros [result|[b h]].
      * apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := MX)).
      * apply (stable_hitting_vis (FI := FI) (FO := FO) (MX := MX)).
  - exact (masked_after_heads_denote_four m c).
Qed.

(** Ret mass rejects the nonempty remaining prefix; only Continue(true)
    reaches the second selected event. Challenge false gives mass 3/8,
    challenge true gives mass 1/8, independently of hidden state m. *)
Theorem masked_challenge_true_reply_probability m c :
  Prₛ[ masked_impl m | challenge_true_reply_trace c ] = (if c then 1 / 8 else 3 / 8 : rat).
Proof.
  assert (Hspec :
    @finite_interaction_query mixedE SubEnumQ MF FI MX FO spec_return
      (challenge_true_reply_trace c) (canonical_spec m)
      (spec_true_reply_query (abstract_state m) c)).
  {
    unfold canonical_spec, challenge_true_reply_trace.
    change (@finite_interaction_query mixedE SubEnumQ MF FI MX FO spec_return
      (cons (@select_challenge c) (cons (@select_true_reply) nil))
      (Vis Challenge (fun answer =>
        PTree.bind (Prob (mixed_samples uniform2 answer) (fun x => Ret x))
          (fun x => match x with
            | inl result => Ret result
            | inr (b,j) => Vis (Reply b) (fun ack =>
                mixed_spec (if ack then j else abstract_state m))
            end)))
      (spec_true_reply_query (abstract_state m) c)).
    eapply finite_interaction_query_vis_match; [reflexivity|].
    apply (proj2 (finite_interaction_query_singleton_iff_next_event_query _ _ _)).
    rewrite true_reply_selector_accepts.
    exists (spec_after_heads (abstract_state m) c). split; [|apply sem_eq_refl].
    unfold spec_after_heads.
    eapply stable_hitting_bind_ret_only with
      (hs := FOSample (mixed_samples uniform2 c) (fun x => FORet (FHRet x)))
      (front := fun x => FORet (spec_head (abstract_state m) x)).
    - eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
      intros x _. constructor. exact I.
    - eapply (stable_hitting_prob (FI := FI) (FO := FO) (MX := MX))
        with (Good := fun _ => True).
      + apply sem_ae_true.
      + intros x _. apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := MX)).
    - intros [result|[b j]].
      + apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := MX)).
      + apply (stable_hitting_vis (FI := FI) (FO := FO) (MX := MX)).
  }
  destruct (finite_interaction_query_exists (FI := FI) (FO := FO) (MX := MX)
    (challenge_true_reply_trace c) (masked_impl m)) as [query Hquery].
  eapply subenumQ_finite_interaction_probability_intro
    with (query := query) (representative := spec_true_reply_query (abstract_state m) c)
      (out := spec_true_reply_observation c).
  - exact Hquery.
  - eapply sem_lift_mono; [|apply sem_lift_sym;
      exact (finite_interaction_query_related (masked_protocol_equivalent m)
        Hquery Hspec)].
    intros x y ->. reflexivity.
  - exact (spec_true_reply_query_denotes (abstract_state m) c).
  - exact (spec_true_reply_mass c).
Qed.
