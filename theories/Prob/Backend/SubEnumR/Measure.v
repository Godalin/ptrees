(** Finite-real native operations and foundational AE capabilities.
    Lifting means an actual finite joint, not a support-only or universal
    relation. Relational gluing/bind are not assumed to fill a profile. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure AE Subprobability.
From PTree.Prob.Backend.SubEnumR Require Import Representation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Section Native.
Variable R : realType.
#[global] Instance SubEnumR_SemanticMeasure : SemanticMeasure (SubEnumR R) := {
  sem_ret := @subenumR_ret R;
  sem_bind := @subenumR_bind R;
  sem_eq := @subenumR_eq R;
  sem_ae := @subenumR_ae R;
  sem_lift := @subenumR_lift R
}.
#[global] Instance SubEnumR_SemanticSubprobability : @SemanticSubprobability (SubEnumR R) SubEnumR_SemanticMeasure := {
  sem_subprob := fun A mu => subenumR_expect mu (fun _ => 1) <= 1
}.
#[global] Instance SubEnumR_SemanticSubprobabilityCarrierLaws : @SemanticSubprobabilityCarrierLaws (SubEnumR R) SubEnumR_SemanticMeasure SubEnumR_SemanticSubprobability.
Proof. constructor; intros A mu; exact (subenumR_mass_bound mu). Qed.
#[global] Instance SubEnumR_SemanticSubprobabilityLaws : @SemanticSubprobabilityLaws (SubEnumR R) SubEnumR_SemanticMeasure SubEnumR_SemanticSubprobability.
Proof.
  constructor; intros; try apply sem_subprob_all.
  split; intros; apply sem_subprob_all.
Qed.

Lemma subenumR_ae_ret_iff {A} (x : A) (P : A -> Prop) :
  subenumR_ae (subenumR_ret R x) P <-> P x.
Proof.
  split.
  - intro H; apply (H 1 x (or_introl (Logic.eq_refl _))).
    intro Hz; have Hlt : (0 : R) < 1 := ltr01; by rewrite Hz ltxx in Hlt.
  - intros H p y [He|[]] Hnz; inversion He; subst; exact H.
Qed.

Lemma subenumR_ae_bind_iff {A B} (mu : SubEnumR R A) (k : A -> SubEnumR R B) P :
  subenumR_ae (subenumR_bind mu k) P <-> subenumR_ae mu (fun x => subenumR_ae (k x) P).
Proof.
  split.
  - intros H p x Hp Hpn q y Hq Hqn.
    apply (H (p*q) y).
    + apply List.in_flat_map; exists (p,x); split; [exact Hp|].
      apply List.in_map_iff; exists (q,y); split; [reflexivity|exact Hq].
    + intro Hz; have H0 : (p == 0) || (q == 0) by rewrite -mulf_eq0 Hz eqxx.
      move/orP: H0=> [Hp0|Hq0].
      * apply Hpn; apply/eqP; exact Hp0.
      * apply Hqn; apply/eqP; exact Hq0.
  - intros H p y Hp Hpn; apply List.in_flat_map in Hp.
    destruct Hp as [[q x] [Hq Hp]]; apply List.in_map_iff in Hp.
    destruct Hp as [[r z] [He Hr]]; cbn in He; inversion He; subst.
    refine (H q x Hq _ r y Hr _).
    + intro Hz; apply Hpn; by rewrite Hz mul0r.
    + intro Hz; apply Hpn; by rewrite Hz mulr0.
Qed.

#[global] Instance SubEnumR_SemanticMeasureDiracAELaws : @SemanticMeasureDiracAELaws (SubEnumR R) SubEnumR_SemanticMeasure.
Proof. constructor; exact @subenumR_ae_ret_iff. Qed.
#[global] Instance SubEnumR_SemanticMeasureCountableAELaws : @SemanticMeasureCountableAELaws (SubEnumR R) SubEnumR_SemanticMeasure.
Proof. constructor; intros A mu P H p x Hin Hnz n; exact (H n p x Hin Hnz). Qed.
#[global] Instance SubEnumR_SemanticMeasureBindAEExactLaws : @SemanticMeasureBindAEExactLaws (SubEnumR R) SubEnumR_SemanticMeasure.
Proof. constructor; exact @subenumR_ae_bind_iff. Qed.
#[global] Instance SubEnumR_SemanticMeasureAEKleisliLaws : @SemanticMeasureAEKleisliLaws (SubEnumR R) SubEnumR_SemanticMeasure.
Proof.
  constructor.
  - intros A P x H; apply subenumR_ae_ret_iff; exact H.
  - intros A B mu k P Q Hmu Hk; apply subenumR_ae_bind_iff.
    intros p x Hin Hnz; exact (Hk x (Hmu p x Hin Hnz)).
Qed.
End Native.
