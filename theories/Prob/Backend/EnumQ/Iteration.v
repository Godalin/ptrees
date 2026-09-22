(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Require Import List.

From mathcomp Require Import ssreflect ssrbool seq ssralg ssrnum order rat.
Require Import PTree.Prob.Backend.EnumQ.Representation.
From PTree.Prob.Interface Require Import FrontierLift.
Require Import PTree.Prob.Backend.EnumQ.FrontierLift.
Require Import PTree.Prob.Interface.Iteration.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.
Import GRing.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

(** Weak convergence tested by all rational-valued observables.  This is a
    relational limit: a chain may converge mathematically while its limit is
    not representable by a finite rational [EnumQ]. *)
Definition enumQ_converges {A} (chain : nat -> EnumQ A) (mu : EnumQ A) : Prop :=
  forall P : A -> bool, forall eps : rat, 0 < eps ->
    exists N, forall n, (N <= n)%nat ->
      `|enumQ_expect (fun x => if P x then 1 else 0) (chain n) -
        enumQ_expect (fun x => if P x then 1 else 0) mu| < eps.

#[global] Instance EnumQ_MeasureOmegaInterface :
    @MeasureOmegaInterface EnumQ EnumQ_MeasureInterface := {
  meas_zero := fun A => enumQ_zero;
  meas_lub := @enumQ_converges;
  meas_total := fun A mu => enumQ_expect (fun _ : A => 1) mu = 1
}.

(** This interface intentionally has no global [MeasureOmegaLaws] instance:
    observational uniqueness of limits does not imply the current
    order-sensitive, list-shaped [EnumQ] [meas_eq]. *)
