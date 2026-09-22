(** Private shared samples and geometric retry fixture. No final soundness regression dependency. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List Arith.PeanoNat FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From PTree.Prob.Domain Require Import Expectation Countable.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
From PTree.Prob.Backend.EnumQ Require Import Representation.
From PTree.Prob.Backend.SubEnumQ Require Import Measure Domain.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import
  UpperExpectation Admissibility DomainSoundness.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

From mathcomp Require Import choice ssrnat.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import CountableSupport.
Definition alternating_bool : FreeOmega SubEnumQ bool :=
  FOLub (fun n => FORet (if Nat.even n then false else true)).

Definition null_weight_node : SubEnumQ bool.
Proof.
  refine (@subenumQ_of_list bool [(1,true); (0,false)] _ _).
  - intros p x [He|[He|[]]]; inversion He; subst; by vm_compute.
  - by vm_compute.
Defined.

Definition nullable_kernel (b : bool) : FreeOmega SubEnumQ bool :=
  if b then FORet true else alternating_bool.

Definition domain_half : rat := 1/2.
Definition domain_fair : SubEnumQ bool.
Proof.
  refine (@subenumQ_of_list bool [(domain_half,true); (domain_half,false)] _ _).
  - intros p x [He|[He|[]]]; inversion He; subst; by vm_compute.
  - by vm_compute.
Defined.
Fixpoint retry_approx (n : nat) : FreeOmega SubEnumQ bool :=
  match n with
  | O => FOZero
  | S m => FOSample domain_fair (fun b => if b then FORet true else retry_approx m)
  end.

Definition repeated_unit n : option unit :=
  match n with O => None | _ => Some tt end.
Definition repeated_bool n : option bool :=
  match n with O => None | _ => Some true end.

Fixpoint geometric_prefix fuel start : FreeOmega SubEnumQ nat :=
  match fuel with
  | O => FOZero
  | S n => FOSample domain_fair
      (fun b => if b then FORet start else geometric_prefix n (S start))
  end.
Definition geometric := FOLub (fun n => geometric_prefix n O).

Lemma geometric_prefix_increasing fuel start :
  free_omega_approx eq (geometric_prefix fuel start) (geometric_prefix (S fuel) start).
Proof.
  induction fuel in start |- *; first apply FOApproxZero.
  cbn [geometric_prefix]; apply FOApproxSample with (S := eq).
  - apply sem_lift_refl; intro b; reflexivity.
  - intros b c ->; destruct c; [apply FOApproxRet; reflexivity|apply IHfuel].
Qed.

Lemma geometric_prefix_enumerates n start :
  exists i, free_omega_enumerate (geometric_prefix (S n) start) i = Some (Nat.add start n).
Proof.
  induction n in start |- *.
  - exists (pickle (O,O)); cbn [geometric_prefix free_omega_enumerate].
    rewrite pickleK; cbn; by rewrite Nat.add_0_r.
  - destruct (IHn (S start)) as [i Hi]; exists (pickle (1%nat,i)).
    cbn [geometric_prefix free_omega_enumerate]; rewrite pickleK.
    change (free_omega_enumerate (geometric_prefix (S n) (S start)) i = Some (Nat.add start (S n))).
    rewrite Hi; by rewrite Nat.add_succ_r Nat.add_succ_l.
Qed.

Example geometric_enumerates_all n : oval_enumerated (free_omega_enumerate geometric) n.
Proof.
  destruct (geometric_prefix_enumerates n O) as [i Hi].
  exists (pickle (S n,i)); cbn [geometric free_omega_enumerate]; rewrite pickleK; exact Hi.
Qed.

Section GeometricValidity.
Variable R : realType.
Lemma geometric_valid : free_omega_admissible R geometric.
Proof.
  apply admissible_lub_approx; last by intro n; apply geometric_prefix_increasing.
  intro n; generalize O as start; induction n=> start; first apply admissible_zero.
  cbn [geometric_prefix]; apply admissible_sample.
  intro b; destruct b; [apply admissible_ret|apply IHn].
Qed.

End GeometricValidity.
