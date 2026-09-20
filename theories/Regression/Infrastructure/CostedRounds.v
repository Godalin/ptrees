Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum FreeOmegaMeasure FreeOmegaNative.
From PTree.Eq Require Import FiniteInternal FiniteInternalPlan UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Eq.FreeOmega Require Import FiniteInternalNative FiniteInternalRound
  CostedKernel FiniteInternalCostedProjection FiniteInternalCostedCoinduction.
From PTree.Regression.Infrastructure Require Import FiniteInternalPlan.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Alternate compression policies on every internal successor of a
    countdown.  The
    hidden boolean changes the cut even for the SAME projected tree.
    Consequently the round's projected kernel does not factor through
    that tree, unlike a unary-policy projection proof. *)
Section AlternatingRounds.
Context {E MN : Type -> Type} `{NI : SemanticMeasure MN} {R : Type} (r : R).
Local Notation tree := (ptree E MN R).
Local Notation head := (stable_head E MN R).
Local Notation State := (nat * bool)%type.

Definition countdown (n : nat) : tree := tau_prefix n (Ret r).
Definition one_countdown_plan n : finite_internal_plan (countdown n) :=
  match n with
  | 0 => FIPStop (Ret r)
  | S m => FIPTau (FIPStop (countdown m))
  end.
Definition alternating_plan (s : State) : finite_internal_plan (countdown (fst s)) :=
  if snd s then one_countdown_plan (fst s) else FIPStop (countdown (fst s)).
Definition alternating_paths s := native_sample_type (internal_plan_round_native (alternating_plan s)).
Definition alternating_measure s := native_sample_measure (internal_plan_round_native (alternating_plan s)).
Definition alternating_target s (_ : alternating_paths s) : stable_target State head :=
  match s with
  | (0, _) | (1, true) => SHStable (FHRet r)
  | (S n, false) => SHInternal (n, true)
  | (S (S n), true) => SHInternal (n, false)
  end.
Definition alternating_cost s (x : alternating_paths s) := internal_round_steps (alternating_plan s) x.
Arguments alternating_target s x : clear implicits.
Arguments alternating_cost s x : clear implicits.

Context `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

Lemma alternating_native_marginal s :
  sem_lift
    (costed_round_path_rel (state_tree := fun s => countdown (fst s))
      (plan := alternating_plan) (s := s)
      (fun h : head => h) alternating_target alternating_cost)
    (alternating_measure s)
    (native_sample_measure (internal_plan_round_native (alternating_plan s))).
Proof.
  apply sem_lift_refl. intro x. split; [reflexivity|].
  destruct s as [n b]. destruct b; destruct n as [|n]; try reflexivity.
  all: destruct n; reflexivity.
Qed.

Theorem alternating_rounds_complete_hitting n b out rounds_out :
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R (observe (countdown n)) out ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega State head
    (costed_kernel alternating_measure alternating_target) (n,b) rounds_out ->
  free_omega_qlift eq out (free_omega_bind rounds_out (fun h => FORet h)).
Proof.
  apply costed_round_stable_hitting with
    (state_tree := fun s => countdown (fst s)) (plan := alternating_plan)
    (cost := alternating_cost) (s := (n,b)).
  intro s. eapply FOQLSample; [apply alternating_native_marginal|].
  intros x y Hxy. apply FOQLStructural, FOLRet. exact Hxy.
Qed.
End AlternatingRounds.

(** Same projected tree, but different projected round targets. *)
Example alternating_round_is_not_unary :
  costed_round_projection (fun s => @countdown planE SubEnum bool true (fst s))
    (fun h : stable_head planE SubEnum bool => h)
    (@alternating_target planE SubEnum SubEnum_SemanticMeasure bool true
      (1, false) (existT _ tt tt)) <>
  costed_round_projection (fun s => @countdown planE SubEnum bool true (fst s))
    (fun h : stable_head planE SubEnum bool => h)
    (@alternating_target planE SubEnum SubEnum_SemanticMeasure bool true
      (1, true) (existT _ tt tt)).
Proof. discriminate. Qed.

Section UnboundedCosts.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}.
Variable mu : MN nat.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

(** The sampled natural number IS its cost.  There is no uniform bound
    over paths and no total-mass or finite-support premise on mu. *)
Example unbounded_cost_limit :
  free_omega_qlift eq
    (FOLub (fun n => @stable_hitting_approx (FreeOmega MN) FI
      FreeOmegaObservableSemanticOmega unit nat
      (costed_kernel (fun _ : unit => mu) (fun _ x => SHStable x)) n tt))
    (FOLub (fun n => costed_hitting_approx (fun _ : unit => mu)
      (fun _ x => SHStable x) (fun _ x => x) n n tt)).
Proof. apply costed_hitting_limit; assumption. Qed.
End UnboundedCosts.

(** Exercise the full coinduction endpoint, not just its hitting lemma.
    The trees may interact forever, sample, or diverge.  The right side
    starts with two additional silent steps, hence the marginal costs
    differ.  After an internal successor the correlated state drops that
    initial padding; visible continuations re-enter the same candidate. *)
Section PaddingCoinduction.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI} {R : Type}.
Local Notation tree := (ptree E MN R).
Local Notation head := (stable_head E MN R).
Local Notation State := (tree * bool)%type.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

Definition padded_tree (s : State) : tree :=
  if snd s then Tau (Tau (fst s)) else fst s.
Definition padding_left_plan (s : State) := FIPStop (fst s).
Definition padding_right_plan (s : State) : finite_internal_plan (padded_tree s) :=
  match snd s as b return finite_internal_plan (if b then Tau (Tau (fst s)) else fst s) with
  | true => FIPTau (FIPTau (FIPStop (fst s)))
  | false => FIPStop (fst s)
  end.
Definition padding_paths s := native_sample_type (internal_plan_round_native (padding_left_plan s)).
Definition padding_measure s := native_sample_measure (internal_plan_round_native (padding_left_plan s)).
Definition padding_target s (x : padding_paths s) : stable_target State head :=
  match native_sample_value (internal_plan_round_native (padding_left_plan s)) x with
  | SHStable h => SHStable h
  | SHInternal t => SHInternal (t, false)
  end.
Definition padding_left_cost s (x : padding_paths s) := internal_round_steps (padding_left_plan s) x.
Definition padding_right_cost s (x : padding_paths s) :=
  if snd s then 2 + padding_left_cost x else padding_left_cost x.
Definition padding_rel (t u : tree) := exists s : State, fst s = t /\ padded_tree s = u.

Lemma padding_project_target (z : stable_target tree head) :
  (match (match z with SHStable h => SHStable h | SHInternal t => SHInternal (t, false) end)
    with SHStable h => SHStable h | SHInternal s => SHInternal (padded_tree s) end) = z.
Proof. destruct z; reflexivity. Qed.

Lemma padding_left_marginal s :
  free_omega_qlift
    (costed_round_path_rel (state_tree := @fst tree bool) (plan := padding_left_plan)
      (s := s) (fun h : head => h) padding_target padding_left_cost)
    (FOSample (padding_measure s) (fun x => FORet x))
    (FOSample (native_sample_measure (internal_plan_round_native (padding_left_plan s)))
      (fun x => FORet x)).
Proof.
  eapply FOQLSample with (T := eq); [apply sem_lift_refl; intro x; reflexivity|].
  intros x y ->. apply FOQLStructural, FOLRet. split; [reflexivity|].
  unfold costed_round_projection, padding_target.
  destruct (native_sample_value (internal_plan_round_native (padding_left_plan s)) y);
    reflexivity.
Qed.

Lemma padding_right_marginal s :
  free_omega_qlift
    (costed_round_path_rel (state_tree := padded_tree) (plan := padding_right_plan)
      (s := s) (fun h : head => h) padding_target padding_right_cost)
    (FOSample (padding_measure s) (fun x => FORet x))
    (FOSample (native_sample_measure (internal_plan_round_native (padding_right_plan s)))
      (fun x => FORet x)).
Proof.
  destruct s as [t b]. destruct b.
  all: eapply FOQLSample with (T := eq); [apply sem_lift_refl; intro x; reflexivity|].
  all: intros x y ->; apply FOQLStructural, FOLRet; split; try reflexivity.
  all: unfold costed_round_projection, padding_target;
    cbn [padding_right_plan padding_left_plan internal_plan_round_native
      free_omega_native_bind free_omega_native internal_plan_native
      native_sample_value internal_plan_residual fst snd] in *.
  all: apply padding_project_target.
Qed.

Theorem padding_via_costed_coinduction (t : tree) :
  @peutt E MN MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega R R eq t (Tau (Tau t)).
Proof.
  eapply peutt_coinduction_costed_rounds with
    (sim := padding_rel) (left_tree := @fst tree bool) (right_tree := padded_tree)
    (left_head := fun h : head => h) (right_head := fun h : head => h)
    (left_plan := padding_left_plan) (right_plan := padding_right_plan)
    (measure := padding_measure) (target := padding_target)
    (left_cost := padding_left_cost) (right_cost := padding_right_cost).
  - apply padding_left_marginal.
  - apply padding_right_marginal.
  - intro s. eapply sem_ae_mono; [|apply sem_ae_true].
    intros x _. destruct (padding_target x) as [h|next]; [|exact I].
    destruct h as [r|Y e k]; constructor; [reflexivity|].
    intro y. exists (k y, false). split; reflexivity.
  - intros x y Hxy. exact Hxy.
  - exists (t, true). split; reflexivity.
Qed.
End PaddingCoinduction.
