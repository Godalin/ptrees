(** * MixedHead: different samplers, related recursive protocols

    Case role: paper case study. Native/frontier: SubEnumQ / observable
    FreeOmega. The implementation uses several Boolean draws; the
    specification samples one complete outcome. One 3-to-2 joint relates
    BOTH heterogeneous return payloads and recursive visible continuations.

    Reading path in this one file:
    - Preparation: protocol types, native coins, observable backend profile.
    - Programs: the complete [masked_impl] and [mixed_spec].
    - Lemma preparation: finite distribution analysis and observations.
    - Main theorem: [masked_protocol_equivalent], with the composition proof in place.
    - Consequences: [masked_public_protocol_equivalent] and
      [masked_challenge_true_reply_probability].

    This is a bisimulation example, not a pure rewrite proof or an execution
    demo. The finite analysis can be skipped on a first reading. See
    docs/CASE_STUDIES.md and docs/CASE_STUDY_STANDARD.md. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.
Local Unset Universe Minimization ToSet.

From PTree.Eq Require Import StableHittingRelation.
From PTree.Eq Require Import UpToBind.
From Coq.Program Require Import Equality.
From ITree.Basics Require Import Monad.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order rat.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Backend.Common Require Import FiniteSubdist.
From PTree.Eq Require Import WellFormedness.
From PTree.Prob.Backend.EnumQ Require Import
  Representation Bind Map Coupling IndexedCoupling FrontierLift SemanticCoupling Iteration.
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
Import PTree MonadNotation.
Local Open Scope monad_scope.
Import SemanticMeasureNotations.
Local Open Scope semantic_measure_scope.
Local Open Scope freeomega_scope.

(** * 1. Preparation *)

(** ** Protocol types and return abstraction *)

(** The environment supplies an ordinary Boolean challenge and acknowledgement. *)
Variant mixedE : Type → Type :=
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
    [coupling32_lift] below supplies a joint supported on these pairs. *)
Definition bridge m z : Prop :=
  match m with L0 => z = false | L1 => True | L2 => z = true end.

(** The same abstraction relates return payloads and recursive hidden states.
    The public bit is preserved; the payload relation is deliberately not a
    function (L1 relates to both abstract values). *)
Definition impl_return := (bool * hidden3)%type.

Definition spec_return := (bool * bool)%type.

Definition return_rel (x : impl_return) (y : spec_return) : Prop :=
  fst x = fst y ∧ bridge (snd x) (snd y).

(** ** Native coins and the specification kernel

    Construct bounded distributions directly, with nonnegativity and mass
    checked locally; no separate raw distributions are exposed here.
    This is the SubEnumQ construction boundary. The programs below consume
    only the named coins and the abstract [ηₘ]/[>>=ₘ] measure algebra. *)

Definition uniform3 : SubEnumQ hidden3.
Proof.
  finite_distribution [:: (1/3, L0); (1/3, L1); (1/3, L2)].
Defined.

Definition uniform2 : SubEnumQ bool.
Proof.
  finite_distribution [:: (1/2, false); (1/2, true)].
Defined.

(** The implementation uses Boolean coins, not a primitive ternary draw. *)
Definition coin_third : SubEnumQ bool.
Proof.
  finite_distribution [:: (1/3, true); (2/3, false)].
Defined.

Definition coin_three_quarters : SubEnumQ bool.
Proof.
  finite_distribution [:: (3/4, true); (1/4, false)].
Defined.

(** Public b = c xor s, with s biased 3/4; Stop/Continue is fair.
    Combine these independent draws into their four-outcome kernel. *)
Definition mixed_outcomes (c : bool) : SubEnumQ mixed_outcome.
Proof.
  finite_distribution
    (let w0 := if c then 3/8 else 1/8 in
     let w1 := if c then 1/8 else 3/8 in
     [:: (w0, Stop false); (w1, Stop true);
         (w0, Continue false); (w1, Continue true)]);
    destruct c; by vm_compute.
Defined.

(** Program-facing kernel: both Stop and Continue sample the same payload.
    Native bind describes the flattened finite law; the main up-to-bind
    proof consumes the sampler relation, without expanding lists. *)
Definition mixed_samples {H} (hidden : SubEnumQ H) c : SubEnumQ (bool * H + bool * H) :=
  mixed_outcomes c >>=ₘ (λ o,
    hidden >>=ₘ (λ h,
      ηₘ (match o with Stop b => inl (b,h) | Continue b => inr (b,h) end))).

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
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation MX := (@FreeOmegaMixedMeasure SubEnumQ).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

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

(** [trigger]/[sample] are the public atomic combinators. The explicit
    Reply [Vis] guards the recursive call; replacing every event by bind
    of [trigger] would hide that guard from Rocq. No extra Tau is added. *)
CoFixpoint masked_impl (m : hidden3) : tree impl_return :=
  c <- trigger Challenge;;
  x <- (mask <- sample coin_three_quarters;;
        continue <- sample uniform2;;
        payload <- (first <- sample coin_third;;
                    if first then Ret L0
                    else second <- sample uniform2;; Ret (if second then L1 else L2));;
        let bit := xorb c mask in
        Ret (if continue then inr (bit, payload) else inl (bit, payload)));;
  match x with
  | inl result => Ret result
  | inr (b,h) => Vis (Reply b) (λ ack, masked_impl (if ack then h else m))
  end.

CoFixpoint mixed_spec (z : bool) : tree spec_return :=
  c <- trigger Challenge;;
  x <- sample (mixed_samples uniform2 c);;
  match x with
  | inl result => Ret result
  | inr (b,j) => Vis (Reply b) (λ ack, mixed_spec (if ack then j else z))
  end.

(** Initialization only; not a deterministic transport of uniform3. *)
Definition abstract_state m := match m with L2 => true | _ => false end.

(** * 3. Lemma preparation

    Only distribution calculations and observable measures are prepared
    here. Program-level facts are proved at their use. *)

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

Lemma coupling32_lift :
  uniform3 ≈[bridge]ₘ uniform2.
Proof.
  eapply indexed_coupling_raw with
    (mu := subenumQ_raw uniform3) (nu := subenumQ_raw uniform2);
    [reflexivity|reflexivity|].
  apply indexed_coupling_of_coupling. exists coupling32_raw.
  - (* Left marginal: uniform on the three hidden states. *)
    intros []; vm_compute; reflexivity.
  - (* Right marginal: the fair Boolean distribution. *)
    intros []; vm_compute; reflexivity.
  - (* Every supported pair satisfies the state relation. *)
    intros m z. unfold bridge. destruct m,z; try (intros _; reflexivity);
      try (intros _; exact I); vm_compute; discriminate.
Qed.

(** Stronger than merely displaying a split joint: no deterministic map
    from these three equiprobable atoms has the required fair marginal. *)
Lemma uniform3_no_deterministic_fair (f : hidden3 → bool) :
  ¬ ((uniform3 >>=ₘ (λ x, ηₘ (f x))) ≈ₘ uniform2).
Proof.
  intro H. apply enumQ_sem_lift_to_coupling in H.
  apply coupling_eq_enumQ_eq in H. specialize (H true). cbn in H.
  destruct (f L0), (f L1), (f L2); vm_compute in H; discriminate.
Qed.

Example return_abstraction_boundary b :
  return_rel (b,L1) (b,false) ∧ return_rel (b,L1) (b,true) ∧
  ¬ return_rel (b,L0) (b,true) ∧ ¬ return_rel (b,L1) (negb b,false).
Proof. destruct b; unfold return_rel, bridge; simpl; intuition discriminate. Qed.

Lemma mixed_samples_lift c :
  mixed_samples uniform3 c ≈[mixed_sample_rel]ₘ mixed_samples uniform2 c.
Proof.
  unfold mixed_samples. eapply sem_lift_bind with (R := eq).
  - apply sem_lift_refl. congruence.
  - intros o o' <-. eapply sem_lift_bind; [exact coupling32_lift|].
    intros h j Hhj. apply sem_lift_ret.
    destruct o; split; [reflexivity|exact Hhj|reflexivity|exact Hhj].
Qed.

Definition draw_distribution c : SubEnumQ (impl_return + impl_return) :=
  coin_three_quarters >>=ₘ (λ s,
    uniform2 >>=ₘ (λ q,
      coin_third >>=ₘ (λ x,
        if x then ηₘ (if q then inr (xorb c s,L0) else inl (xorb c s,L0))
        else uniform2 >>=ₘ (λ y,
          ηₘ (if q then inr (xorb c s,if y then L1 else L2)
                        else inl (xorb c s,if y then L1 else L2)))))).

Lemma draw_distribution_mixed c : draw_distribution c ≈ₘ mixed_samples uniform3 c.
Proof.
  apply (@enumQ_meas_eq_of_eqenum
    (@Equality.Pack (impl_return + impl_return)%type
      (Equality.on (impl_return + impl_return)%type))).
  intros [[b h]|[b h]]; destruct c,b,h;
    apply val_inj; vm_compute; reflexivity.
Qed.

Set Universe Polymorphism.

(** ** Finite observations

    Only the observation functions and finite probability calculations are
    prepared here. The final proofs construct their complete frontiers and
    query witnesses locally, as they analyze the actual programs. *)

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

Definition spec_true_reply_observation c : SubEnumQ bool :=
  mixed_outcomes c >>=ₘ (λ o,
    ηₘ (match o with Stop _ => false | Continue b => b end)).

(** * 4. Final theorems

    Main behavioral claim, public-result corollary, and quantitative endpoints.
    The complete program proof is below: unfold, compose prefixes with bind,
    discharge returns, then close the recursive visible continuations. *)

(** No caller-supplied bridge proof or specification wrapper: [abstract_state]
    chooses a related initial state. The local invariant contains only loop
    entries; the Reply context is composed below, not enumerated as a state. *)
Theorem masked_protocol_equivalent m :
  masked_impl m ≈ₚ[return_rel] mixed_spec (abstract_state m).
Proof.
  (* Expose one round, then compose its prefix and continuation proofs. *)
  eapply peutt_coinduction_upto_bind_vis with
    (sim := λ s1 s2, exists old z, bridge old z ∧
      s1 = observe (masked_impl old) ∧ s2 = observe (mixed_spec z));
    try typeclasses eauto.
  - intros s1 s2 (old & z & Hold & -> & ->).
    apply stable_hitting_match_vis. intro answer.
    rewrite !(observe_bind (Ret answer)).
    eapply bind_upto_closure_bind with (RR := mixed_sample_rel).
    + (* Analyze this finite prefix here, not via a pre-proved program relation. *)
      eapply peutt_of_hitting_lift with
        (out1 := x ←ω draw_distribution answer ;; ηω (FHRet x))
        (out2 := x ←ω mixed_samples uniform2 answer ;; ηω (FHRet x)).
      * unfold draw_distribution.
        apply stable_hitting_native_sample. intro mask.
        apply stable_hitting_native_sample. intro continue.
        rewrite observe_bind.
        apply stable_hitting_native_sample. intros [].
        -- apply stable_hitting_native_ret.
        -- rewrite observe_bind.
           apply stable_hitting_native_sample. intro second.
           apply stable_hitting_native_ret.
      * eapply (stable_hitting_prob (FO := FO) (MX := MX)) with (Good := λ _, True).
        -- apply sem_ae_true.
        -- intros x _. apply (stable_hitting_ret (FO := FO) (MX := MX)).
      * eapply FOQLSample with (T := mixed_sample_rel).
        -- eapply sem_lift_proper_l; [apply sem_eq_sym, draw_distribution_mixed|].
           exact (mixed_samples_lift answer).
        -- intros x y H. apply FOQLStructural. constructor. constructor. exact H.
    + intros [r|[b h]] [u|[b' j]] H; simpl in H; try contradiction.
      * (* Stop: abstract the returned payload, preserving the public bit. *)
        right. apply peutt_ret. exact H.
      * (* Continue: compose the fresh coupling with the Reply context. *)
        destruct H as [Hbit Hfresh]. simpl in Hbit, Hfresh. subst b'.
        left. apply vis_upto_closure_vis. intro ack.
        (* True installs the freshly related states; false keeps the old pair. *)
        exists (if ack then h else old), (if ack then j else z).
        split; [destruct ack; assumption|].
        split; reflexivity.
  - (* Initialization discharges the invariant internally. *)
    exists m, (abstract_state m). split.
    + destruct m; simpl; auto.
    + split; reflexivity.
Qed.

(** Erasing the abstracted payload recovers ordinary Boolean equivalence,
    using the library's heterogeneous bind law, not a second coinduction. *)
Theorem masked_public_protocol_equivalent m :
  PTree.bind (masked_impl m) (λ r, Ret (fst r)) ≈ₚ
  PTree.bind (mixed_spec (abstract_state m)) (λ u, Ret (fst u)).
Proof.
  eapply peutt_bind with (RR := return_rel).
  - apply masked_protocol_equivalent.
  - intros r u [Hbit _]. apply peutt_ret. exact Hbit.
Qed.

(** Ret mass rejects the nonempty remaining prefix; only Continue(true)
    reaches the second selected event. Challenge false gives mass 3/8,
    challenge true gives mass 1/8, independently of hidden state m. *)
Theorem masked_challenge_true_reply_probability m c :
  Prₛ[ masked_impl m | challenge_true_reply_trace c ] = (if c then 1 / 8 else 3 / 8 : rat).
Proof.
  (* Construct the specification's query and its projection together. *)
  assert (Hspec : exists query : MF bool,
    finite_interaction_query (MX := MX) (FO := FO)
      (challenge_true_reply_trace c) (mixed_spec (abstract_state m)) query ∧
    free_omega_denotes id query (spec_true_reply_observation c)).
  {
    eexists. split.
    - unfold challenge_true_reply_trace.
      eapply finite_interaction_query_vis_match; [reflexivity|].
      apply (proj2 (finite_interaction_query_singleton_iff_next_event_query _ _ _)).
      eexists. split.
      + rewrite (observe_bind (Ret c)).
        rewrite observe_bind.
        (* Infer each head, including Reply's continuation, from its branch. *)
        eapply (stable_hitting_prob (FO := FO) (MX := MX)) with
          (Good := λ _, True)
          (front := λ x, match x with inl result => _ | inr (b,j) => _ end).
        * apply sem_ae_true.
        * intros [result|[b j]] _; rewrite observe_bind.
          -- apply (stable_hitting_ret (FO := FO) (MX := MX)).
          -- apply (stable_hitting_vis (FO := FO) (MX := MX)).
      + apply sem_eq_refl.
    - (* Infer the native Boolean outcomes from those observed heads. *)
      eexists. split.
      + eapply FOOObserveSample with
          (front := λ x, match x with inl result => _ | inr (b,j) => _ end).
        intros [[b j]|[b j]]; constructor.
      + apply enumQ_meas_eq_of_eqenum. intros []; destruct c;
          apply val_inj; vm_compute; reflexivity.
  }
  destruct Hspec as [spec_query [Hspec Hdenotes]].
  destruct (finite_interaction_query_exists (FO := FO) (MX := MX)
    (challenge_true_reply_trace c) (masked_impl m)) as [query Hquery].
  eapply subenumQ_finite_interaction_probability_intro.
  - exact Hquery.
  - eapply sem_lift_mono; [|apply sem_lift_sym;
      exact (finite_interaction_query_related (masked_protocol_equivalent m)
        Hquery Hspec)].
    intros x y ->. reflexivity.
  - exact Hdenotes.
  - destruct c; vm_compute; reflexivity.
Qed.
