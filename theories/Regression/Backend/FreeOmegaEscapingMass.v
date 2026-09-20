(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Lia.
From Coq.Program Require Import Equality.
From Coq.Arith Require Import PeanoNat.
From mathcomp Require Import ssreflect ssralg ssrnum rat.
From PTree.Prob.Backend Require Import RatSubTypes DiscreteMC.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.Backend Require Import TwoLevelMeasureSubEnum MeasureIterationEnum.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Regression.Backend Require Import EnumMeasureRegression SubEnumRegression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum RatSubTypes GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Module EscapingMass.
Local Notation MF := (FreeOmega SubEnum).
Local Notation observe_unit := (@free_omega_observes SubEnum SubEnum_SemanticMeasure
  SubEnum_SemanticOmega unit unit (fun x => x)).
Lemma qsym (mu nu : MF unit) : free_omega_qlift eq mu nu -> free_omega_qlift eq nu mu.
Proof.
  intro H. eapply FOQLMono; [apply FOQLSym; exact H|].
  intros x y Hyx. symmetry. exact Hyx.
Qed.
Definition big : MF unit := FOSample subenum_fair (fun _ => FORet tt).
Definition small : MF unit := FOSample subenum_fair (fun b : bool => if b then FORet tt else FOZero).
Definition big_out := subenum_bind subenum_fair (fun _ => subenum_ret tt).
Definition small_out := subenum_bind subenum_fair
  (fun b : bool => if b then subenum_ret tt else subenum_zero).

Lemma big_observes : observe_unit big big_out.
Proof.
  eapply (@FOOObserveSample SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
  intro b. apply (@FOOObserveRet SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
Qed.
Lemma small_observes : observe_unit small small_out.
Proof.
  eapply (@FOOObserveSample SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
  intros [].
  - apply (@FOOObserveRet SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
  - apply (@FOOObserveZero SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
Qed.
Lemma big_small_masses_differ : enum_mass (subenum_raw big_out) <> enum_mass (subenum_raw small_out).
Proof. vm_compute. discriminate. Qed.
Lemma big_mass_one : enum_mass (subenum_raw big_out) = 1.
Proof. vm_compute. reflexivity. Qed.
Lemma small_mass_half : enum_mass (subenum_raw small_out) = 1 / 2.
Proof. vm_compute. reflexivity. Qed.

Lemma fair_true_ae P : sem_ae subenum_fair P -> P true.
Proof.
  intro H. apply (H reg_half true).
  - right. left. reflexivity.
  - intro Hz. apply (f_equal Qval) in Hz. vm_compute in Hz. discriminate.
Qed.

Lemma big_ae P : free_omega_ae P big <-> P tt.
Proof.
  split.
  - intro H. apply free_omega_ae_sample_inv in H.
    pose proof (fair_true_ae H) as HP. inversion HP. assumption.
  - intro H. apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros b _. apply FOAERet. exact H.
Qed.
Lemma small_ae P : free_omega_ae P small <-> P tt.
Proof.
  split.
  - intro H. apply free_omega_ae_sample_inv in H.
    pose proof (fair_true_ae H) as HP. inversion HP. assumption.
  - intro H. apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros [] _; [apply FOAERet; exact H|apply FOAEZero].
Qed.
Lemma unit_support (mu nu : MF unit)
    (Hmu : forall P, free_omega_ae P mu <-> P tt)
    (Hnu : forall P, free_omega_ae P nu <-> P tt) : free_omega_support_lift eq mu nu.
Proof.
  split; intros P HP.
  - apply Hnu. exists tt. split; [reflexivity|apply Hmu; exact HP].
  - apply Hmu. exists tt. split; [reflexivity|apply Hnu; exact HP].
Qed.
Lemma lub_unit_ae (chain : nat -> MF unit)
    (Hchain : forall n P, free_omega_ae P (chain n) <-> P tt) P :
    free_omega_ae P (FOLub chain) <-> P tt.
Proof.
  split.
  - intro H. dependent destruction H. apply (Hchain O P), H.
  - intro H. apply FOAELub. intro n. apply Hchain. exact H.
Qed.

(** The former unrestricted observation rule is a LOCAL HYPOTHESIS, not
    an axiom of the repaired backend.  The conditional theorem below
    demonstrates the consequence of reintroducing that rule. *)
Section FormerObservationRule.
Hypothesis unrestricted_observe_lub : forall (chain : nat -> MF unit) outs out,
  (forall n, observe_unit (chain n) (outs n)) ->
  subenum_sem_lub outs out -> observe_unit (FOLub chain) out.

Lemma eventually_observed_constant (chain : nat -> MF unit) outs mu out N
    (Hrows : forall n, observe_unit (chain n) (outs n))
    (Hmu : observe_unit mu out)
    (Heventual : forall n, (N <= n)%nat -> outs n = out)
    (Hsupport : free_omega_support_lift eq (FOLub chain) mu) :
  free_omega_qlift eq (FOLub chain) mu.
Proof.
  eapply FOQLObserve with (obsA := fun x : unit => x) (obsB := fun x : unit => x)
    (outA := out) (outB := out) (S := eq).
  - eapply unrestricted_observe_lub; [exact Hrows|].
    intros P eps Heps. exists N. intros n Hn. rewrite (Heventual n Hn).
    rewrite subrr normr0. exact Heps.
  - exact Hmu.
  - apply sem_lift_refl. intro x. reflexivity.
  - intros x y Hxy. exact Hxy.
  - exact Hsupport.
Qed.

Definition kernel (x n : nat) : MF unit := if Nat.leb x n then big else small.
Definition kernel_out (x n : nat) := if Nat.leb x n then big_out else small_out.
Lemma kernel_observes x n : observe_unit (kernel x n) (kernel_out x n).
Proof. unfold kernel, kernel_out. destruct (Nat.leb x n); [apply big_observes|apply small_observes]. Qed.
Lemma kernel_ae x n P : free_omega_ae P (kernel x n) <-> P tt.
Proof. unfold kernel. destruct (Nat.leb x n); [apply big_ae|apply small_ae]. Qed.
Lemma small_below_big : free_omega_approx eq small big.
Proof.
  apply FOApproxSample with (S := eq); [apply sem_lift_refl; intro b; reflexivity|].
  intros [] y <-; [apply FOApproxRet; reflexivity|apply FOApproxZero].
Qed.
Lemma kernel_increasing x n : free_omega_approx eq (kernel x n) (kernel x (S n)).
Proof.
  unfold kernel. destruct (Nat.leb x n) eqn:Hn, (Nat.leb x (S n)) eqn:HS.
  - apply free_omega_approx_refl. intro z. reflexivity.
  - apply Nat.leb_le in Hn. apply Nat.leb_gt in HS. lia.
  - apply small_below_big.
  - apply free_omega_approx_refl. intro z. reflexivity.
Qed.
Lemma kernel_limit x : free_omega_qlift eq big (FOLub (kernel x)).
Proof.
  apply qsym. eapply eventually_observed_constant with (outs := kernel_out x) (N := x).
  - apply kernel_observes.
  - apply big_observes.
  - intros n Hn. unfold kernel_out. apply Nat.leb_le in Hn. rewrite Hn. reflexivity.
  - apply unit_support; [intros P; apply lub_unit_ae; intros; apply kernel_ae|apply big_ae].
Qed.
Lemma escaped_row_limit n : free_omega_qlift eq (FOLub (fun x => kernel x n)) small.
Proof.
  eapply eventually_observed_constant with (outs := fun x => kernel_out x n) (N := S n).
  - intro x. apply kernel_observes.
  - apply small_observes.
  - intros x Hx. unfold kernel_out. assert (H : Nat.leb x n = false) by (apply Nat.leb_gt; lia).
    rewrite H. reflexivity.
  - apply unit_support; [intros P; apply lub_unit_ae; intros; apply kernel_ae|apply small_ae].
Qed.

(** The source itself is not an increasing distribution chain.  Placing
    its formal Lub inside a CONSTANT outer source chain passes the
    existing local monotonicity premise of FOQLBindLub. *)
Definition escaping : MF nat := FOLub (fun n => FORet n).
Definition diagonal : MF unit := FOLub (fun n => free_omega_bind escaping (fun x => kernel x n)).

Lemma escaping_bind_diagonal : free_omega_qlift eq
    (free_omega_bind escaping (fun _ => big)) diagonal.
Proof.
  eapply FOQLBindLub with (source := fun _ => escaping) (kernels := kernel).
  - intro n. apply free_omega_approx_refl. intro x. reflexivity.
  - exact kernel_increasing.
  - apply FOQLLubConstantR, free_omega_qlift_refl. intro x. reflexivity.
  - exact kernel_limit.
  - apply unit_support.
    + intros P. apply lub_unit_ae. intros n Q. apply big_ae.
    + intros P. apply lub_unit_ae. intros n Q. apply lub_unit_ae. intros x T. apply kernel_ae.
Qed.

(** Conditional audit: the hypothesis of this section is exactly the old
    observation rule, which the repaired backend does NOT provide. *)
Theorem unrestricted_observation_collapses_mass : free_omega_qlift eq big small.
Proof.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := free_omega_bind escaping (fun _ => big)).
  - change (free_omega_qlift eq big (FOLub (fun _ => big))).
    apply FOQLLubConstantR, free_omega_qlift_refl. intro x. reflexivity.
  - eapply FOQLComp with (T := eq) (U := eq); [apply escaping_bind_diagonal| |].
    + eapply FOQLComp with (T := eq) (U := eq) (mid := FOLub (fun _ => small)).
      * apply FOQLLub. intro n. apply escaped_row_limit.
      * apply qsym, FOQLLubConstantR, free_omega_qlift_refl. intro x. reflexivity.
      * intros x z [y [-> ->]]. reflexivity.
    + intros x z [y [-> ->]]. reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.
End FormerObservationRule.

(** The increasing direction of the same grid remains observable without
    the former rule.  Only the decreasing, escaping direction is rejected. *)
Theorem increasing_kernel_observable x :
  observe_unit (FOLub (kernel x)) big_out.
Proof.
  eapply FOOObserveLub with (outs := kernel_out x).
  - apply kernel_observes.
  - intros P eps Heps. exists x. intros n Hn. unfold kernel_out.
    apply Nat.leb_le in Hn. rewrite Hn. rewrite subrr normr0. exact Heps.
  - apply kernel_increasing.
Qed.

Lemma fair_false_ae P : sem_ae subenum_fair P -> P false.
Proof.
  intro H. apply (H reg_half false).
  - left. reflexivity.
  - intro Hz. apply (f_equal Qval) in Hz. vm_compute in Hz. discriminate.
Qed.

Lemma big_not_below_small : ~ free_omega_approx eq big small.
Proof.
  intro H. unfold big, small in H. dependent destruction H.
  pose proof (sem_lift_ae_transport_r H (sem_ae_true subenum_fair)) as Hsupport.
  destruct (fair_false_ae Hsupport) as [x [Hxy _]].
  specialize (H0 x false Hxy). dependent destruction H0.
Qed.

Lemma escaped_rows_not_increasing n :
  ~ (forall i, free_omega_approx eq (kernel i n) (kernel (S i) n)).
Proof.
  intro H. specialize (H n). unfold kernel in H.
  rewrite Nat.leb_refl in H.
  assert (Hnext : Nat.leb (S n) n = false) by (apply Nat.leb_gt; lia).
  rewrite Hnext in H. exact (big_not_below_small H).
Qed.

(** After the repair, no observation of the offending row can be
    constructed, even though its native observable sequence converges. *)
Theorem escaped_row_not_observable n out :
  ~ observe_unit (FOLub (fun x => kernel x n)) out.
Proof.
  intro H. dependent destruction H. exact (escaped_rows_not_increasing H1).
Qed.

Theorem unrestricted_observation_rule_rejected :
  ~ (forall (chain : nat -> MF unit) outs out,
    (forall n, observe_unit (chain n) (outs n)) ->
    subenum_sem_lub outs out -> observe_unit (FOLub chain) out).
Proof.
  intro Hrule. apply (@escaped_row_not_observable O small_out).
  eapply Hrule with (outs := fun x => kernel_out x O).
  - intro x. apply kernel_observes.
  - intros P eps Heps. exists 1%nat. intros [|x] Hx; [lia|].
    cbn [kernel_out Nat.leb]. rewrite subrr normr0. exact Heps.
Qed.
End EscapingMass.
