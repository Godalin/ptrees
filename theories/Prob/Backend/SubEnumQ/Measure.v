(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Require Import List.

From mathcomp Require Import ssreflect ssrbool seq ssralg ssrnum order rat.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Bind PTree.Prob.Backend.EnumQ.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure.

From PTree.Prob.Backend.SubEnumQ Require Export Representation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.
Import GRing.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Definition subenumQ_eq {A} (mu nu : SubEnumQ A) : Prop :=
  @sem_eq EnumQ EnumQ_SemanticMeasure A
    (subenumQ_raw mu) (subenumQ_raw nu).

Definition subenumQ_ae {A} (mu : SubEnumQ A) (P : A -> Prop) : Prop :=
  @sem_ae EnumQ EnumQ_SemanticMeasure A (subenumQ_raw mu) P.

Definition subenumQ_lift {A B} (R : A -> B -> Prop)
    (mu : SubEnumQ A) (nu : SubEnumQ B) : Prop :=
  @sem_lift EnumQ EnumQ_SemanticMeasure A B R
    (subenumQ_raw mu) (subenumQ_raw nu).

#[global] Instance SubEnumQ_SemanticMeasure :
    SemanticMeasure SubEnumQ := {
  sem_ret := @subenumQ_ret;
  sem_bind := @subenumQ_bind;
  sem_eq := @subenumQ_eq;
  sem_ae := @subenumQ_ae;
  sem_lift := @subenumQ_lift
}.

#[global] Instance EnumQ_SemanticSubprobability :
    @SemanticSubprobability EnumQ EnumQ_SemanticMeasure := {
  sem_subprob := @enumQ_subprob
}.

#[global] Instance EnumQ_SemanticSubprobabilityLaws :
    @SemanticSubprobabilityLaws EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticSubprobability.
Proof.
  constructor.
  - exact @enumQ_subprob_ret.
  - exact @enumQ_subprob_bind.
  - intros A mu nu Heq. cbn in Heq |- *.
    have Hsame : @sem_same_mass EnumQ EnumQ_SemanticMeasure A A mu nu.
    { eapply sem_lift_mono; [|exact Heq]. intros x y _. exact I. }
    have Hmass := enumQ_sem_same_mass_expect_one Hsame.
    rewrite /enumQ_subprob /enumQ_mass Hmass. reflexivity.
Qed.

#[global] Instance SubEnumQ_SemanticSubprobability :
    @SemanticSubprobability SubEnumQ SubEnumQ_SemanticMeasure := {
  sem_subprob := fun A mu => enumQ_subprob (subenumQ_raw mu)
}.

#[global] Instance SubEnumQ_SemanticSubprobabilityLaws :
    @SemanticSubprobabilityLaws SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticSubprobability.
Proof.
  constructor; cbn.
  - exact @enumQ_subprob_ret.
  - intros A B mu k Hmu Hk. apply enumQ_subprob_bind; assumption.
  - intros A mu nu Heq.
    have Hsame : @sem_same_mass EnumQ EnumQ_SemanticMeasure A A
        (subenumQ_raw mu) (subenumQ_raw nu).
    { eapply sem_lift_mono; [|exact Heq]. intros x y _. exact I. }
    have Hmass := enumQ_sem_same_mass_expect_one Hsame.
    rewrite /enumQ_subprob /enumQ_mass Hmass. reflexivity.
Qed.

#[global] Instance SubEnumQ_SemanticSubprobabilityCarrierLaws :
    @SemanticSubprobabilityCarrierLaws SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticSubprobability.
Proof. constructor. exact @subenumQ_bound. Qed.

#[global] Instance SubEnumQ_SemanticMeasureCoreLaws :
    @SemanticMeasureCoreLaws SubEnumQ SubEnumQ_SemanticMeasure.
Proof.
  constructor; cbn.
  - intros A mu. exact (@sem_eq_refl EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticMeasureCoreLaws A (subenumQ_raw mu)).
  - intros A mu nu Hmn. exact (@sem_eq_sym EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticMeasureCoreLaws A _ _ Hmn).
  - intros A mu nu xi Hmn Hnx. exact (@sem_eq_trans EnumQ
      EnumQ_SemanticMeasure EnumQ_SemanticMeasureCoreLaws A _ _ _ Hmn Hnx).
  - intros A mu. exact (@sem_ae_true EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticMeasureCoreLaws A (subenumQ_raw mu)).
  - intros A mu P Q HPQ HP. exact (@sem_ae_mono EnumQ
      EnumQ_SemanticMeasure EnumQ_SemanticMeasureCoreLaws
      A (subenumQ_raw mu) P Q HPQ HP).
  - intros A mu P Q HP HQ. exact (@sem_ae_conj EnumQ
      EnumQ_SemanticMeasure EnumQ_SemanticMeasureCoreLaws
      A (subenumQ_raw mu) P Q HP HQ).
  - intros A B R T mu nu HRT Hlift. exact (@sem_lift_mono EnumQ
      EnumQ_SemanticMeasure EnumQ_SemanticMeasureCoreLaws
      A B R T (subenumQ_raw mu) (subenumQ_raw nu) HRT Hlift).
  - intros A R mu HR. exact (@sem_lift_refl EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticMeasureCoreLaws A R (subenumQ_raw mu) HR).
  - intros A B R x y Hxy. exact (@sem_lift_ret EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticMeasureCoreLaws A B R x y Hxy).
  - intros A B R mu mu' nu Heq Hlift.
    exact (@sem_lift_proper_l EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticMeasureCoreLaws A B R
      (subenumQ_raw mu) (subenumQ_raw mu') (subenumQ_raw nu) Heq Hlift).
  - intros A B R mu nu nu' Heq Hlift.
    exact (@sem_lift_proper_r EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticMeasureCoreLaws A B R
      (subenumQ_raw mu) (subenumQ_raw nu) (subenumQ_raw nu') Heq Hlift).
  - intros A B R mu nu Hlift. exact (@sem_lift_sym EnumQ
      EnumQ_SemanticMeasure EnumQ_SemanticMeasureCoreLaws
      A B R (subenumQ_raw mu) (subenumQ_raw nu) Hlift).
  - intros A B C R T mu nu xi Hmn Hnx.
    exact (@sem_lift_comp EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticMeasureCoreLaws A B C R T
      (subenumQ_raw mu) (subenumQ_raw nu) (subenumQ_raw xi) Hmn Hnx).
Qed.

#[global] Instance SubEnumQ_SemanticMeasureBindLaws :
    @SemanticMeasureBindLaws SubEnumQ SubEnumQ_SemanticMeasure.
Proof.
  constructor; cbn.
  - intros A B x k. exact (@sem_bind_ret_l EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticMeasureBindLaws A B x (fun y => subenumQ_raw (k y))).
  - intros A B C mu k h. exact (@sem_bind_assoc EnumQ
      EnumQ_SemanticMeasure EnumQ_SemanticMeasureBindLaws A B C
      (subenumQ_raw mu) (fun x => subenumQ_raw (k x))
      (fun y => subenumQ_raw (h y))).
  - intros A B mu k h Hae. exact (@sem_bind_ae_proper EnumQ
      EnumQ_SemanticMeasure EnumQ_SemanticMeasureBindLaws A B
      (subenumQ_raw mu) (fun x => subenumQ_raw (k x))
      (fun x => subenumQ_raw (h x)) Hae).
  - intros A B C D R T mu nu k h Hmn Hkh.
    exact (@sem_lift_bind EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticMeasureBindLaws A B C D R T
      (subenumQ_raw mu) (subenumQ_raw nu)
      (fun x => subenumQ_raw (k x)) (fun y => subenumQ_raw (h y)) Hmn Hkh).
Qed.

#[global] Instance SubEnumQ_SemanticMeasureAELiftLaws :
    @SemanticMeasureAELiftLaws SubEnumQ SubEnumQ_SemanticMeasure.
Proof.
  constructor. intros A mu P Hae.
  exact (@sem_lift_refl_ae EnumQ EnumQ_SemanticMeasure
    EnumQ_SemanticMeasureAELiftLaws A (subenumQ_raw mu) P Hae).
Qed.

#[global] Instance SubEnumQ_SemanticMeasureAEKleisliLaws :
    @SemanticMeasureAEKleisliLaws SubEnumQ SubEnumQ_SemanticMeasure.
Proof.
  constructor; cbn.
  - exact (@sem_ae_ret EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticMeasureAEKleisliLaws).
  - intros A B mu k P Q HP HK. exact (@sem_ae_bind EnumQ
      EnumQ_SemanticMeasure EnumQ_SemanticMeasureAEKleisliLaws
      A B (subenumQ_raw mu) (fun x => subenumQ_raw (k x)) P Q HP HK).
Qed.

#[global] Instance SubEnumQ_SemanticMeasureDiracAELaws :
    @SemanticMeasureDiracAELaws SubEnumQ SubEnumQ_SemanticMeasure.
Proof.
  constructor. exact (@sem_ae_ret_iff EnumQ EnumQ_SemanticMeasure
    EnumQ_SemanticMeasureDiracAELaws).
Qed.

#[global] Instance SubEnumQ_SemanticMeasureCountableAELaws :
    @SemanticMeasureCountableAELaws SubEnumQ SubEnumQ_SemanticMeasure.
Proof.
  constructor. intros A mu P HP. exact (@sem_ae_countable EnumQ
    EnumQ_SemanticMeasure EnumQ_SemanticMeasureCountableAELaws
    A (subenumQ_raw mu) P HP).
Qed.

#[global] Instance SubEnumQ_SemanticMeasureCouplingAELaws :
    @SemanticMeasureCouplingAELaws SubEnumQ SubEnumQ_SemanticMeasure.
Proof.
  constructor; cbn.
  - intros A B R mu nu P Hlift HP. exact
      (@sem_lift_ae_transport_r EnumQ EnumQ_SemanticMeasure
        EnumQ_SemanticMeasureCouplingAELaws A B R
        (subenumQ_raw mu) (subenumQ_raw nu) P Hlift HP).
  - intros A B R mu nu P Q Hlift HP HQ. exact
      (@sem_lift_ae_restrict EnumQ EnumQ_SemanticMeasure
        EnumQ_SemanticMeasureCouplingAELaws A B R
        (subenumQ_raw mu) (subenumQ_raw nu) P Q Hlift HP HQ).
Qed.

#[global] Instance SubEnumQ_SemanticMeasureBindAEExactLaws :
    @SemanticMeasureBindAEExactLaws SubEnumQ SubEnumQ_SemanticMeasure.
Proof.
  constructor. intros A B mu k P. exact (@sem_ae_bind_iff EnumQ
    EnumQ_SemanticMeasure EnumQ_SemanticMeasureBindAEExactLaws
    A B (subenumQ_raw mu) (fun x => subenumQ_raw (k x)) P).
Qed.

Definition subenumQ_sem_le {A} (mu nu : SubEnumQ A) : Prop :=
  enumQ_sem_le (subenumQ_raw mu) (subenumQ_raw nu).

Definition subenumQ_sem_lub {A}
    (chain : nat -> SubEnumQ A) (mu : SubEnumQ A) : Prop :=
  enumQ_converges (fun n => subenumQ_raw (chain n)) (subenumQ_raw mu).

Definition subenumQ_total {A} (mu : SubEnumQ A) : Prop :=
  enumQ_mass (subenumQ_raw mu) = 1.

#[global] Instance SubEnumQ_SemanticOmega :
    @SemanticOmega SubEnumQ SubEnumQ_SemanticMeasure := {
  sem_zero := @subenumQ_zero;
  sem_le := @subenumQ_sem_le;
  sem_lub := @subenumQ_sem_lub;
  sem_total := @subenumQ_total
}.
