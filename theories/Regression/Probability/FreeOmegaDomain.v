(** Role: DS2 admissibility/soundness boundary tests. In particular, a raw
    alternating FOLub is rejected, while null-probability bad branches are
    permitted. This file does not test or assume DS3 quotient soundness. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List Arith.PeanoNat FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From PTree.Prob.Domain Require Import Expectation.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Backend.Common Require Import RatSubTypes.
From PTree.Prob.Backend.Enum Require Import Representation.
From PTree.Prob.Backend.SubEnum Require Import Measure Domain.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation.
From PTree.Prob.Backend.SubEnum.FreeOmega Require Import
  UpperExpectation Admissibility DomainSoundness.

Fail Check PTree.Prob.Domain.MeasureModel.oval_probability.
Fail Check PTree.Core.PTreeDefinition.ptree.
Fail Check PTree.Eq.PEutt.peutt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import RatSubTypes GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Definition alternating_bool : FreeOmega SubEnum bool :=
  FOLub (fun n => FORet (if Nat.even n then false else true)).

Definition null_weight_node : SubEnum bool.
Proof.
  refine {| subenum_raw := [((1 : nnQ), true); (nnQ_0, false)] |}.
  by vm_compute.
Defined.

Definition nullable_kernel (b : bool) : FreeOmega SubEnum bool :=
  if b then FORet true else alternating_bool.

Definition domain_half : nnQ.
Proof. refine (mknnQ (1/2) _); by vm_compute. Defined.
Definition domain_fair : SubEnum bool.
Proof.
  refine {| subenum_raw := [(domain_half,true); (domain_half,false)] |}.
  by vm_compute.
Defined.
Fixpoint retry_approx (n : nat) : FreeOmega SubEnum bool :=
  match n with
  | O => FOZero
  | S m => FOSample domain_fair (fun b => if b then FORet true else retry_approx m)
  end.

Section DomainTests.
Variable R : realType.

Lemma alternating_upper_test (f : bool -> R) witness :
  oval_test f -> f witness = 1 -> free_omega_upper alternating_bool f = 1.
Proof.
  intros Hf Hw; apply/eqP; rewrite eq_le; apply/andP; split.
  - exact (proj2 (free_omega_upper_bounds alternating_bool Hf)).
  - rewrite -Hw; unfold alternating_bool; cbn [free_omega_upper].
    destruct witness.
    + exact (@countable_upper_ge R
        (fun n => f (if Nat.even n then false else true)) 1 1%nat
        (fun n => proj2 (Hf _))).
    + exact (@countable_upper_ge R
        (fun n => f (if Nat.even n then false else true)) 1 0%nat
        (fun n => proj2 (Hf _))).
Qed.

Theorem alternating_bool_not_admissible : ~ free_omega_admissible R alternating_bool.
Proof.
  intro H.
  pose f := fun b : bool => if b then (1 : R) else 0.
  pose g := fun b : bool => if b then (0 : R) else 1.
  have Hf : oval_test f by intros []; split; try exact: lexx; exact: ler01.
  have Hg : oval_test g by intros []; split; try exact: lexx; exact: ler01.
  have Hfg : forall b, f b + g b <= 1 by intros []; rewrite /f /g ?addr0 ?add0r.
  have Hsum : oval_test (fun b => f b + g b) := oval_test_add Hf Hg Hfg.
  have Hbad := oval_add H Hf Hg Hfg.
  rewrite (@alternating_upper_test f true Hf (Logic.eq_refl _))
    (@alternating_upper_test g false Hg (Logic.eq_refl _))
    (@alternating_upper_test (fun b => f b + g b) true Hsum (addr0 1)) in Hbad.
  have Hlt : (1 : R) < 1 + 1 by rewrite ltrDr ltr01.
  by rewrite -Hbad ltxx in Hlt.
Qed.

Example alternating_has_no_domain_model :
  ~ exists L : OmegaVal R bool, free_omega_domain_denotes alternating_bool L.
Proof.
  intro H; apply alternating_bool_not_admissible.
  exact (proj2 (free_omega_admissible_iff_denotes R alternating_bool) H).
Qed.

Lemma nullable_kernel_ae :
  sem_ae null_weight_node (fun b => free_omega_admissible R (nullable_kernel b)).
Proof.
  change (forall p b, List.In (p,b) [((1 : nnQ),true); (nnQ_0,false)] ->
    p <> nnQ_0 -> free_omega_admissible R (nullable_kernel b)).
  intros p b [H|[H|[]]] Hnz; inversion H; subst.
  - exact: admissible_ret.
  - exfalso; apply Hnz; reflexivity.
Qed.

Example null_weight_bad_branch_admissible :
  free_omega_admissible R (FOSample null_weight_node nullable_kernel).
Proof. apply admissible_sample_ae; exact nullable_kernel_ae. Qed.

Example null_weight_bad_branch_bind_admissible :
  free_omega_admissible R
    (free_omega_bind (FOSample null_weight_node (fun b => FORet b)) nullable_kernel).
Proof.
  apply admissible_bind_ae.
  - apply admissible_sample=> b; exact: admissible_ret.
  - eapply FOAESample; [exact nullable_kernel_ae|].
    intros b H; exact (FOAERet H).
Qed.

Example null_weight_branch_really_invalid :
  ~ free_omega_admissible R (nullable_kernel false).
Proof. exact alternating_bool_not_admissible. Qed.

Example null_weight_sample_denotes :
  free_omega_domain_denotes (FOSample null_weight_node nullable_kernel)
    (oval_bind (subenum_domain R null_weight_node) (fun _ => oval_ret R true)).
Proof.
  apply free_omega_denote_sample_ae.
  change (forall p b, List.In (p,b) [((1 : nnQ),true); (nnQ_0,false)] ->
    p <> nnQ_0 -> free_omega_domain_denotes (nullable_kernel b) (oval_ret R true)).
  intros p b [H|[H|[]]] Hnz; inversion H; subst.
  - exact: free_omega_denote_ret.
  - exfalso; apply Hnz; reflexivity.
Qed.

Example positive_bad_branch_not_admissible :
  ~ free_omega_admissible R (FOSample (subenum_ret false) nullable_kernel).
Proof.
  intro H; apply alternating_bool_not_admissible.
  eapply free_omega_admissible_ext; [exact H|].
  intros f Hf; cbn [free_omega_upper subenum_ret subenum_raw
    Enum.ret_Enum enum_real_expect nullable_kernel].
  by rewrite rmorph1 mul1r addr0.
Qed.

Definition delayed (n : nat) : FreeOmega SubEnum bool :=
  match n with O => FOZero | S _ => FORet true end.
Lemma delayed_valid n : free_omega_admissible R (delayed n).
Proof. destruct n; [exact: admissible_zero|exact: admissible_ret]. Qed.
Lemma delayed_approx n : free_omega_approx eq (delayed n) (delayed (S n)).
Proof. destruct n; constructor; reflexivity. Qed.

Example increasing_lub_admissible : free_omega_admissible R (FOLub delayed).
Proof. apply admissible_lub_approx; [exact delayed_valid|exact delayed_approx]. Qed.

Example increasing_lub_denotes :
  free_omega_domain_denotes (FOLub delayed)
    (oval_lub (free_omega_domain_increasing_of_approx delayed_valid delayed_approx)).
Proof. apply free_omega_denote_lub=> n; exact: free_omega_domain_spec. Qed.

Example approximation_denotes_order :
  oval_le (free_omega_domain (delayed_valid 0%nat))
    (free_omega_domain (delayed_valid 1%nat)).
Proof.
  eapply free_omega_denote_approx; try exact: free_omega_domain_spec.
  exact: delayed_approx.
Qed.

Example native_bind_denotes {A B} (mu : SubEnum A) (k : A -> SubEnum B) :
  free_omega_domain_denotes
    (free_omega_bind (FOSample mu (fun x => FORet x))
      (fun x => FOSample (k x) (fun y => FORet y)))
    (oval_bind (subenum_domain R mu) (fun x => subenum_domain R (k x))).
Proof. apply free_omega_denote_bind; [exact: free_omega_denote_native|].
  intro x; exact: free_omega_denote_native. Qed.

(** A genuinely unbounded retry construction, not only an eventually
    constant chain. No AST/mass-one result is assumed to prove validity. *)
Lemma retry_approx_valid n : free_omega_admissible R (retry_approx n).
Proof.
  induction n; first exact: admissible_zero.
  apply admissible_sample; intros []; [exact: admissible_ret|exact IHn].
Qed.
Lemma retry_approx_increasing n :
  free_omega_approx eq (retry_approx n) (retry_approx (S n)).
Proof.
  induction n; first constructor.
  eapply FOApproxSample with (S := eq).
  - apply sem_lift_refl; intro x; reflexivity.
  - intros x y ->; destruct y; [constructor; reflexivity|exact IHn].
Qed.
Example unbounded_retry_admissible :
  free_omega_admissible R (FOLub retry_approx).
Proof. apply admissible_lub_approx; [exact retry_approx_valid|exact retry_approx_increasing]. Qed.
Example unbounded_retry_denotes_lub :
  free_omega_domain_denotes (FOLub retry_approx)
    (oval_lub (free_omega_domain_increasing_of_approx
      retry_approx_valid retry_approx_increasing)).
Proof. apply free_omega_denote_lub=> n; exact: free_omega_domain_spec. Qed.
End DomainTests.
