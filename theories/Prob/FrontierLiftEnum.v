Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import List.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg order rat.
From PTree.Prob Require Import RatSubTypes DiscreteMC IndexedCoupling
  FrontierLift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum IndexedCoupling.
Import GRing.Theory.
#[local] Open Scope ring_scope.

Fixpoint enum_prune {A} (mu : Enum A) : Enum A :=
  match mu with
  | [::] => [::]
  | (p, x) :: tl =>
      if p == RatSubTypes.nnQ_0
      then enum_prune tl
      else (p, x) :: enum_prune tl
  end.

Lemma enum_prune_app {A} (mu nu : Enum A) :
  enum_prune (mu ++ nu) = enum_prune mu ++ enum_prune nu.
Proof.
  elim: mu=> [//=|[p x] mu IH] //=.
  by case: (p == RatSubTypes.nnQ_0); rewrite IH.
Qed.

Lemma enum_prune_scale_zero {A} (mu : Enum A) :
  enum_prune (scale_Enum RatSubTypes.nnQ_0 mu) = [::].
Proof.
  elim: mu=> [//=|[p x] mu IH] //=.
  have Hz : RatSubTypes.nnQ_0 * p = RatSubTypes.nnQ_0.
    apply val_inj. cbn. exact: mul0r (Qval p).
  by rewrite Hz eq_refl IH.
Qed.

(** Almost-everywhere for a finite enumeration: a property is required only
    at entries carrying non-zero mass.  This definition needs no equality on
    the sampled type. *)
Definition enum_ae {A} (mu : Enum A) (P : A -> Prop) : Prop :=
  forall p x, List.In (p, x) mu -> p <> RatSubTypes.nnQ_0 -> P x.

(** The operational instance is fully generic in its carriers.  Its
    [meas_lift] is the existing position-indexed coupling, which avoids an
    [eqType] requirement on values such as event continuations. *)
#[global] Instance Enum_MeasureInterface : MeasureInterface Enum := {
  meas_ret := @ret_Enum;
  meas_bind := @bind_Enum;
  meas_eq := fun A mu nu => enum_prune mu = enum_prune nu;
  meas_ae := @enum_ae;
  meas_lift := fun A B R mu nu =>
    indexed_coupling R (enum_prune mu) (enum_prune nu)
}.

#[global] Instance Enum_MeasureCoreLaws :
    @MeasureCoreLaws Enum Enum_MeasureInterface.
Proof.
  constructor.
  - move=> A mu P Q HPQ Hae p x Hin Hnz.
    exact: HPQ (Hae p x Hin Hnz).
  - move=> A B R S mu nu HRS Hlift.
    exact: indexed_coupling_mono HRS Hlift.
  - move=> A R mu HR.
    exact: indexed_coupling_refl HR.
Qed.

#[global] Instance Enum_MeasureLaws :
    @MeasureLaws Enum Enum_MeasureInterface Enum_MeasureCoreLaws.
Proof.
  constructor.
  - move=> A mu. reflexivity.
  - move=> A mu nu H. symmetry. exact H.
  - move=> A mu nu xi H1 H2. exact: eq_trans H1 H2.
  - move=> A mu p x Hin Hnz. exact I.
  - move=> A mu P Q HP HQ p x Hin Hnz.
    split; [exact: HP p x Hin Hnz|exact: HQ p x Hin Hnz].
  - move=> A B R mu mu' nu Hmu Hlift.
    cbn in Hmu, Hlift |- *. rewrite -Hmu. exact Hlift.
  - move=> A B R mu nu nu' Hnu Hlift.
    cbn in Hnu, Hlift |- *. rewrite -Hnu. exact Hlift.
  - move=> A B R mu nu H. exact: indexed_coupling_sym H.
  - move=> A B C R S mu nu xi H1 H2.
    exact: indexed_coupling_comp H1 H2.
Qed.
