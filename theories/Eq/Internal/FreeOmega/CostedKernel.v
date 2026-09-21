(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Arith Require Import PeanoNat Wf_nat.
From Coq Require Import Lia.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import PrimitiveStableHitting.
From PTree.Eq.Internal.FreeOmega Require Import KernelContinuity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A native kernel whose paths carry finite, nonuniform internal costs.
    The state may contain a correlated pair and its history.  No cost bound,
    totality, AST, or restriction to a unary compression policy is imposed.
    Both indices below are observation budgets, not program-equivalence indices. *)
Section CostedKernel.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI} {State Out : Type}.
Variable X : State -> Type.
Variable measure : forall s, MN (X s).
Variable target : forall s, X s -> stable_target State Out.
Variable cost : forall s, X s -> nat.
Arguments target s _ : clear implicits.
Arguments cost s _ : clear implicits.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation hit :=
  (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega State Out).

Definition costed_kernel s : MF (stable_target State Out) :=
  FOSample (measure s) (fun x => FORet (target s x)).

Definition costed_kernel_cut cap s : MF (stable_target State Out) :=
  FOSample (measure s) (fun x =>
    if Nat.leb (cost s x) cap then FORet (target s x) else FOZero).

Fixpoint costed_hitting_approx rounds fuel s : MF Out :=
  FOSample (measure s) (fun x =>
    if Nat.leb (cost s x) fuel then
      match target s x with
      | SHStable o => FORet o
      | SHInternal u =>
          match rounds with
          | 0 => FOZero
          | S r => costed_hitting_approx r (fuel - cost s x) u
          end
      end
    else FOZero).

Lemma costed_hitting_mono rounds rounds' fuel fuel' s :
  rounds <= rounds' -> fuel <= fuel' ->
  free_omega_approx eq (costed_hitting_approx rounds fuel s)
    (costed_hitting_approx rounds' fuel' s).
Proof.
  induction rounds as [|rounds IH] in rounds', fuel, fuel', s |- *;
    destruct rounds' as [|rounds']; intros Hr Hf; try lia;
    cbn [costed_hitting_approx]; eapply FOApproxSample with (S := eq);
    try solve [apply sem_lift_refl; intro x; reflexivity]; intros x y ->;
    destruct (Nat.leb (cost s y) fuel) eqn:Hc;
    destruct (Nat.leb (cost s y) fuel') eqn:Hc';
    try solve [apply FOApproxZero];
    try solve [apply Nat.leb_le in Hc; apply Nat.leb_gt in Hc'; lia];
    destruct (target s y); try solve [apply FOApproxRet; reflexivity];
    try solve [apply FOApproxZero].
  apply IH; lia.
Qed.

Lemma costed_kernel_cut_mono n m s :
  n <= m -> free_omega_approx eq (costed_kernel_cut n s) (costed_kernel_cut m s).
Proof.
  intro Hnm. unfold costed_kernel_cut. eapply FOApproxSample with (S := eq).
  - apply sem_lift_refl. intro x. reflexivity.
  - intros x y ->. destruct (Nat.leb (cost s y) n) eqn:Hn;
      destruct (Nat.leb (cost s y) m) eqn:Hm;
      try solve [apply FOApproxZero | apply FOApproxRet; reflexivity].
    apply Nat.leb_le in Hn. apply Nat.leb_gt in Hm. lia.
Qed.

(** If the total budget is below a per-round cutoff, every admitted
    weighted path is also admitted by that cutoff kernel. *)
Lemma costed_hitting_below_cut rounds fuel cap s :
  fuel <= cap -> free_omega_approx eq
    (costed_hitting_approx rounds fuel s) (hit (costed_kernel_cut cap) rounds s).
Proof.
  induction rounds as [|rounds IH] in fuel, s |- *; intro Hfc;
    cbn [costed_hitting_approx stable_hitting_approx costed_kernel_cut
      sem_bind free_omega_bind]; eapply FOApproxSample with (S := eq);
    try solve [apply sem_lift_refl; intro x; reflexivity]; intros x y ->;
    destruct (Nat.leb (cost s y) fuel) eqn:Hf;
    destruct (Nat.leb (cost s y) cap) eqn:Hc;
    try solve [apply FOApproxZero];
    try solve [apply Nat.leb_le in Hf; apply Nat.leb_gt in Hc; lia];
    cbn [free_omega_bind]; destruct (target s y);
    cbn [stable_target_approx sem_ret sem_zero];
    try solve [apply FOApproxRet; reflexivity | apply FOApproxZero].
  apply IH. lia.
Qed.

(** Conversely, r+1 rounds of per-round cost at most cap spend at most
    (r+1)*cap in total.  No uniform bound on the original kernel is used. *)
Lemma cut_hitting_below_costed rounds fuel cap s :
  (S rounds) * cap <= fuel -> free_omega_approx eq
    (hit (costed_kernel_cut cap) rounds s) (costed_hitting_approx rounds fuel s).
Proof.
  induction rounds as [|rounds IH] in fuel, s |- *; intro Hbudget;
    cbn [costed_hitting_approx stable_hitting_approx costed_kernel_cut
      sem_bind free_omega_bind]; eapply FOApproxSample with (S := eq);
    try solve [apply sem_lift_refl; intro x; reflexivity]; intros x y ->;
    destruct (Nat.leb (cost s y) cap) eqn:Hc;
    destruct (Nat.leb (cost s y) fuel) eqn:Hf;
    cbn [free_omega_bind]; try solve [apply FOApproxZero];
    try solve [apply Nat.leb_le in Hc; apply Nat.leb_gt in Hf; nia];
    destruct (target s y); cbn [stable_target_approx sem_ret sem_zero];
    try solve [apply FOApproxRet; reflexivity | apply FOApproxZero].
  apply IH. apply Nat.leb_le in Hc. nia.
Qed.

Lemma costed_cut_target_limit s x :
  free_omega_qlift eq (FORet (target s x))
    (FOLub (fun n => if Nat.leb (cost s x) (S n)
      then FORet (target s x) else FOZero)).
Proof.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := FOLub (fun _ => FORet (target s x))).
  - apply FOQLLubConstantR, FOQLStructural, FOLRet. reflexivity.
  - apply FOQLCofinal.
    + intro n. apply FOApproxRet. reflexivity.
    + intro n. destruct (Nat.leb (cost s x) (S n)) eqn:Hn;
        destruct (Nat.leb (cost s x) (S (S n))) eqn:Hsn;
        try solve [apply FOApproxZero | apply FOApproxRet; reflexivity].
      apply Nat.leb_le in Hn. apply Nat.leb_gt in Hsn. lia.
    + split.
      * intro n. exists (cost s x).
        assert (Hc : Nat.leb (cost s x) (S (cost s x)) = true)
          by (apply Nat.leb_le; lia).
        rewrite Hc. apply FOApproxRet. reflexivity.
      * intro n. exists 0. destruct (Nat.leb (cost s x) (S n));
          [apply FOApproxRet; reflexivity | apply FOApproxZero].
  - intros x' z [y [-> ->]]. reflexivity.
Qed.

Lemma costed_kernel_limit s :
  free_omega_qlift eq (costed_kernel s)
    (FOLub (fun n => costed_kernel_cut (S n) s)).
Proof.
  unfold costed_kernel, costed_kernel_cut.
  apply FOQLSampleLub with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros x _ n. destruct (Nat.leb (cost s x) (S n)) eqn:Hn;
      destruct (Nat.leb (cost s x) (S (S n))) eqn:Hsn;
      try solve [apply FOApproxZero | apply FOApproxRet; reflexivity].
    apply Nat.leb_le in Hn. apply Nat.leb_gt in Hsn. lia.
  - intros x _. apply costed_cut_target_limit.
Qed.

Lemma costed_cut_diagonal_increasing n s :
  free_omega_approx eq (hit (costed_kernel_cut (S n)) n s)
    (hit (costed_kernel_cut (S (S n))) (S n) s).
Proof.
  eapply free_omega_approx_trans with
    (nu := hit (costed_kernel_cut (S (S n))) n s).
  - apply kernel_hitting_approx_mono. intro u. apply costed_kernel_cut_mono. lia.
  - exact (@stable_hitting_increasing MF FI FreeOmegaObservableSemanticOmega
      FreeOmegaObservableSemanticMeasureOrderLaws State Out
      (costed_kernel_cut (S (S n))) s n).
Qed.

Theorem costed_hitting_cofinal s :
  free_omega_chains_cofinal eq
    (fun n => hit (costed_kernel_cut (S n)) n s)
    (fun n => costed_hitting_approx n n s).
Proof.
  split.
  - intro n. exists ((S n) * (S n)).
    eapply free_omega_approx_trans.
    + apply cut_hitting_below_costed. reflexivity.
    + apply costed_hitting_mono; nia.
  - intro n. exists n. eapply free_omega_approx_mono with (R := eq).
    + intros x y ->. reflexivity.
    + apply costed_hitting_below_cut. lia.
Qed.

Context `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}.

(** Counting macro rounds or counting their real internal cost yields
    the same COMPLETE hitting distribution.  Finite observations need
    not agree.  In particular this theorem does not assert equality of
    prefix-state masses, which can fail for subprobability kernels. *)
Theorem costed_hitting_limit s :
  free_omega_qlift eq (FOLub (fun n => hit costed_kernel n s))
    (FOLub (fun n => costed_hitting_approx n n s)).
Proof.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := FOLub (fun n => hit (costed_kernel_cut (S n)) n s)).
  - apply kernel_hitting_limit_diagonal.
    + intros n u. apply costed_kernel_cut_mono. lia.
    + apply costed_kernel_limit.
    + exact NCAE.
    + exact NCountAE.
  - apply FOQLCofinal.
    + intro n. apply costed_cut_diagonal_increasing.
    + intro n. apply costed_hitting_mono; lia.
    + apply costed_hitting_cofinal.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

Theorem costed_stable_hitting s out :
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega State Out costed_kernel s out ->
  free_omega_qlift eq out (FOLub (fun n => costed_hitting_approx n n s)).
Proof.
  intro Hhit. eapply FOQLComp with (T := eq) (U := eq).
  - exact Hhit.
  - apply costed_hitting_limit.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

Section ReferenceAdequacy.
Context {RefOut : Type}.
Variable project : Out -> RefOut.
Variable reference : nat -> State -> MF RefOut.

(** These are finite, local premises.  [reference_round] describes the
    original observation budget through ONE sampled round; it neither
    assumes equality of complete limits nor of repeated execution. *)
Definition costed_internal_progress s x :=
  forall u, target s x = SHInternal u -> 0 < cost s x.
Arguments costed_internal_progress s x : clear implicits.
Hypothesis internal_progress : forall s,
  sem_ae (measure s) (costed_internal_progress s).
Hypothesis reference_round : forall fuel s,
  free_omega_qlift eq (reference fuel s)
    (FOSample (measure s) (fun x =>
      if Nat.leb (cost s x) fuel then
        match target s x with
        | SHStable o => FORet (project o)
        | SHInternal u => reference (fuel - cost s x) u
        end
      else FOZero)).

Lemma costed_progress_coupling s :
  sem_lift (fun x y => x = y /\ costed_internal_progress s x)
    (measure s) (measure s).
Proof.
  eapply sem_lift_mono with
    (R := fun x y => x = y /\ costed_internal_progress s x /\ True).
  - intros x y [Hxy [Hx _]]. split; assumption.
  - apply sem_lift_ae_restrict.
    + apply sem_lift_refl. intro x. reflexivity.
    + apply internal_progress.
    + apply sem_ae_true.
Qed.

Theorem costed_hitting_reference fuel : forall rounds s,
  fuel <= rounds -> free_omega_qlift eq (reference fuel s)
    (free_omega_bind (costed_hitting_approx rounds fuel s)
      (fun o => FORet (project o))).
Proof.
  induction fuel as [fuel IH] using lt_wf_ind.
  intros rounds s Hrounds.
  eapply FOQLComp with (T := eq) (U := eq); [apply reference_round| |].
  - destruct rounds as [|rounds]; cbn [costed_hitting_approx free_omega_bind];
      eapply FOQLSample with (T := fun x y => x = y /\ costed_internal_progress s x);
      try solve [apply costed_progress_coupling]; intros x y [-> Hprogress];
      destruct (Nat.leb (cost s y) fuel) eqn:Hcost;
      try solve [apply FOQLStructural, FOLZero];
      destruct (target s y) as [o|u] eqn:Htarget;
      cbn [free_omega_bind];
      try solve [apply FOQLStructural, FOLRet; reflexivity].
    + pose proof (Hprogress u Htarget). apply Nat.leb_le in Hcost. lia.
    + apply IH.
      * pose proof (Hprogress u Htarget). apply Nat.leb_le in Hcost. lia.
      * pose proof (Hprogress u Htarget). lia.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

(** A finite-budget round decomposition and positive internal progress
    suffice for full multiround adequacy.  The reference may depend on
    the entire correlated state, as may its costs and sampled round. *)
Theorem costed_hitting_reference_limit s :
  free_omega_qlift eq (FOLub (fun n => reference n s))
    (free_omega_bind (FOLub (fun n => hit costed_kernel n s))
      (fun o => FORet (project o))).
Proof.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := free_omega_bind (FOLub (fun n => costed_hitting_approx n n s))
      (fun o => FORet (project o))).
  - cbn [free_omega_bind]. apply FOQLLub. intro n.
    apply costed_hitting_reference. reflexivity.
  - apply FOQLMono with (T := fun x y => y = x).
    + apply FOQLSym. eapply FOQLBind with (T := eq).
      * apply costed_hitting_limit.
      * intros x y ->. apply FOQLStructural, FOLRet. reflexivity.
    + intros x y Hyx. symmetry. exact Hyx.
  - intros x z [y [-> ->]]. reflexivity.
Qed.
End ReferenceAdequacy.
End CostedKernel.
