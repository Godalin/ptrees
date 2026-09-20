Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
(** Keep the zero query in the behavior carrier's universe, rather than
    minimizing its otherwise unconstrained [FOZero] representation to Set. *)
Local Unset Universe Minimization ToSet.

From Coq Require Import Program.Equality.
From mathcomp Require Import ssreflect ssrbool ssrnat seq ssralg ssrnum rat reals.
From mathcomp.analysis Require Import ereal.
From mathcomp.reals_stdlib Require Import Rstruct.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import DiscreteMC FrontierLiftEnum MeasureIterationEnum
  TwoLevelMeasure TwoLevelMeasureEnum FreeOmegaMeasure
  FreeOmegaUpperExpectationEnum FreeOmegaUpperQuotientEnum.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier
  PTreeKernel PEutt ProbabilisticTrace.
From PTree.Regression.Backend Require Import EnumMeasureRegression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Native samples remain Enum. Complete heads belong to FreeOmega Enum,
    not to the same monomorphic native Enum universe. In particular these
    missing-mass tests must coexist with arbitrary sampled continuations. *)
Local Notation MF := (FreeOmega Enum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := Enum_SemanticMeasure) (NC := Enum_SemanticMeasureCoreLaws)
  (NO := Enum_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega)).
Local Notation K := (@ptree_primitive_kernel regE Enum MF FI
  FreeOmegaMixedMeasure bool).
Local Notation hits t out := (@stable_hitting MF FI FO _ _ K (observe t) out).
Local Notation W := (@peutt regE Enum MF FI FC
  FreeOmegaMixedMeasure FO bool bool eq).
Local Notation scalar := (@Real.Pack Rdefinitions.R (Real.on Rdefinitions.R)).

CoFixpoint canonical_spin : ptree regE Enum bool := Tau canonical_spin.

Lemma observe_canonical_spin :
  observe canonical_spin = TauF canonical_spin.
Proof. reflexivity. Qed.

Definition half_return_half_diverge : ptree regE Enum bool :=
  Prob reg_fair (fun b => if b then Ret true else canonical_spin).

Definition half_return_heads : MF (stable_head regE Enum bool) :=
  FOSample reg_fair (fun b => if b then FORet (FHRet true) else FOZero).

Lemma canonical_spin_target_approx_zero fuel :
  @stable_target_approx MF FI FO _ _ K fuel
    (SHInternal (observe canonical_spin)) = FOZero.
Proof.
  induction fuel as [|fuel IH]; [reflexivity|].
  change (@stable_target_approx MF FI FO _ _ K fuel
    (SHInternal (observe canonical_spin)) = FOZero).
  exact IH.
Qed.

Lemma canonical_spin_hitting_approx_zero fuel :
  @stable_hitting_approx MF FI FO _ _ K fuel
    (observe canonical_spin) = FOZero.
Proof. exact (canonical_spin_target_approx_zero fuel). Qed.

Lemma canonical_spin_stable_hitting_zero : hits canonical_spin FOZero.
Proof.
  unfold stable_hitting.
  eapply (sem_lub_chain_proper (SI := FI) (SO := FO))
    with (chain := fun _ => FOZero).
  - intro n. rewrite canonical_spin_hitting_approx_zero.
    apply sem_eq_refl.
  - apply sem_lub_constant.
Qed.

Definition impossible_trace_step {X} (e : regE X) : option X :=
  match e with end.
Definition divergent_one_event_trace : @finite_interaction_pattern regE :=
  cons (@impossible_trace_step) nil.
Definition divergent_trace_query : MF bool := FOZero.

Lemma canonical_spin_nonempty_trace_query_zero :
  @finite_interaction_query regE Enum MF FI FreeOmegaMixedMeasure FO bool
    divergent_one_event_trace canonical_spin divergent_trace_query.
Proof.
  exists FOZero, (fun _ : stable_head regE Enum bool => FOZero).
  repeat split.
  - exact canonical_spin_stable_hitting_zero.
  - apply FOAEZero.
  - apply free_omega_qlift_refl. intro b. reflexivity.
Qed.

Lemma divergent_trace_query_mass_zero :
  exists out : Enum bool,
    @free_omega_observes Enum Enum_SemanticMeasure Enum_SemanticOmega
      bool bool (fun b => b) divergent_trace_query out /\
    enum_expect (fun _ : bool => (1 : rat)) out = 0.
Proof. exists [::]. split; [constructor|reflexivity]. Qed.

Lemma divergent_trace_query_not_rejection_mass :
  ~ @sem_same_mass MF FI bool bool divergent_trace_query (FORet false).
Proof.
  intro Hmass.
  pose proof ((proj1 (free_omega_qlift_support Hmass)) (fun _ => False)
    (FOAEZero _)) as Hbad.
  dependent destruction Hbad.
  destruct H as [x [_ Hfalse]]. exact Hfalse.
Qed.

Lemma enum_ret_true_stable_hitting : hits (Ret true) (FORet (FHRet true)).
Proof. apply (stable_hitting_ret (FI := FI) (FO := FO)). Qed.

Lemma half_return_half_diverge_stable_hitting :
  hits half_return_half_diverge half_return_heads.
Proof.
  unfold half_return_half_diverge, half_return_heads.
  apply (stable_hitting_prob (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros [] _; [exact enum_ret_true_stable_hitting|exact canonical_spin_stable_hitting_zero].
Qed.

(** Scalar soundness of the observable quotient separates mass 1/2 from
    mass 1. This is the proved backend model, not a new mass/reflection axiom.
    The standard-real instance is the same one used by native recovery. *)
Lemma half_return_heads_not_same_mass_ret :
  ~ @sem_same_mass MF FI
      (stable_head regE Enum bool) (stable_head regE Enum bool)
      half_return_heads (FORet (FHRet true)).
Proof.
  intro Hmass.
  have Hweight := free_omega_qlift_extended_upper_mass scalar Hmass.
  change (enum_extended_expect (R := scalar)
    (fun b : bool => if b then 1 else 0) reg_fair = 1)%E in Hweight.
  cbn [enum_extended_expect reg_fair] in Hweight.
  rewrite !reg_half_val mule0 mule1 !adde0 in Hweight.
  have Hone : (1 : \bar scalar)%E = (ratr (1 : rat) : scalar)%:E by rewrite rmorph1.
  rewrite Hone in Hweight. injection Hweight as Hrat.
  rewrite add0r in Hrat.
  have Hbad := fmorph_inj (ratr : {rmorphism rat -> scalar}) Hrat.
  move: Hbad. native_compute. discriminate.
Qed.

Theorem half_return_half_diverge_not_peutt_ret :
  ~ W half_return_half_diverge (Ret true).
Proof.
  intro Hrel.
  have Hlift := peutt_hitting_lift (FI := FI) (FC := FC) (FO := FO)
    (FOL := FreeOmegaObservableSemanticOmegaLaws
      (NC := Enum_SemanticMeasureCoreLaws)) Hrel
    half_return_half_diverge_stable_hitting enum_ret_true_stable_hitting.
  apply half_return_heads_not_same_mass_ret.
  exact (sem_lift_same_mass Hlift).
Qed.
