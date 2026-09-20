Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.analysis Require Import ereal.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureEnum FreeOmegaMeasure
  FreeOmegaUpperExpectationEnum FreeOmegaUpperCouplingEnum FreeOmegaUpperObservationEnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory DiscreteMC.Enum.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Internal test comparison for the raw weighted backend.  The envelopes
    use extended sup/inf, not subtraction from one: neither intermediate
    measures nor bind-generated tests need be bounded. *)
Section RelationalExtendedUpper.
Variable R : realType.
Local Notation upper := (@free_omega_extended_upper R).

Definition nonnegative_test {A} (f : A -> \bar R) := forall x, 0 <= f x.

Definition extended_fiber_upper {A} (P : A -> Prop) (f : A -> \bar R) :=
  ereal_sup (fun r => r = 0 \/ exists x, P x /\ r = f x).

Definition extended_fiber_lower {A} (P : A -> Prop) (f : A -> \bar R) :=
  ereal_inf (fun r => exists x, P x /\ r = f x).

Lemma extended_fiber_upper_le {A} (P : A -> Prop) (f : A -> \bar R) b :
  0 <= b -> (forall x, P x -> f x <= b) -> extended_fiber_upper P f <= b.
Proof.
  intros Hb Hf. apply ub_ereal_sup=> r [->|[x [HP ->]]]; [exact Hb|exact (Hf x HP)].
Qed.

Lemma extended_fiber_upper_nonnegative {A} (P : A -> Prop) (f : A -> \bar R) :
  0 <= extended_fiber_upper P f.
Proof. apply ereal_sup_ubound. by left. Qed.

Lemma extended_fiber_upper_ge {A} (P : A -> Prop) (f : A -> \bar R) x :
  P x -> f x <= extended_fiber_upper P f.
Proof. intro Hx. apply ereal_sup_ubound. right. exists x. by split. Qed.

Lemma extended_fiber_lower_nonnegative {A} (P : A -> Prop) (f : A -> \bar R) :
  nonnegative_test f -> 0 <= extended_fiber_lower P f.
Proof. intro Hf. apply lb_ereal_inf=> r [x [_ ->]]. exact (Hf x). Qed.

Lemma extended_fiber_lower_le {A} (P : A -> Prop) (f : A -> \bar R) x :
  P x -> extended_fiber_lower P f <= f x.
Proof. intro Hx. apply ereal_inf_lbound. exists x. by split. Qed.

Lemma extended_fiber_upper_lower {A B} (P : A -> Prop) (Q : B -> Prop)
    (f : A -> \bar R) (g : B -> \bar R) :
  nonnegative_test g -> (forall x y, P x -> Q y -> f x <= g y) ->
  extended_fiber_upper P f <= extended_fiber_lower Q g.
Proof.
  intros Hg Hfg. apply lb_ereal_inf=> r [y [Hy ->]].
  apply extended_fiber_upper_le; [exact (Hg y)|]. intros x Hx. exact (Hfg x y Hx Hy).
Qed.

Definition free_omega_extended_upper_rel {A B} (T : A -> B -> Prop)
    (mu : FreeOmega Enum A) (nu : FreeOmega Enum B) : Prop :=
  forall (f : A -> \bar R) (g : B -> \bar R),
    nonnegative_test f -> nonnegative_test g ->
    (forall x y, T x y -> f x <= g y) -> upper mu f <= upper nu g.

Lemma free_omega_extended_upper_rel_mono {A B} (T U : A -> B -> Prop) mu nu :
  free_omega_extended_upper_rel T mu nu ->
  (forall x y, T x y -> U x y) -> free_omega_extended_upper_rel U mu nu.
Proof. intros H HT f g Hf Hg Hfg. apply H; auto. Qed.

Lemma free_omega_extended_upper_rel_comp {A B C} (T : A -> B -> Prop)
    (U : B -> C -> Prop) mu mid nu :
  free_omega_extended_upper_rel T mu mid -> free_omega_extended_upper_rel U mid nu ->
  free_omega_extended_upper_rel (fun x z => exists y, T x y /\ U y z) mu nu.
Proof.
  intros Hl Hr f g Hf Hg Hfg.
  pose h y := extended_fiber_upper (fun x => T x y) f.
  have Hh : nonnegative_test h by intro y; apply extended_fiber_upper_nonnegative.
  eapply le_trans.
  - apply (Hl f h Hf Hh). intros x y Hxy. exact (extended_fiber_upper_ge f Hxy).
  - apply (Hr h g Hh Hg). intros y z Hyz. apply extended_fiber_upper_le.
    + exact (Hg z).
    + intros x Hxy. apply Hfg. exists y. by split.
Qed.

Theorem free_omega_observes_extended_upper_rel {A B OA OB}
    (T : A -> B -> Prop) (S : OA -> OB -> Prop)
    (obsA : A -> OA) (obsB : B -> OB) mu nu outA outB :
  @free_omega_observes Enum Enum_SemanticMeasure Enum_SemanticOmega A OA obsA mu outA ->
  @free_omega_observes Enum Enum_SemanticMeasure Enum_SemanticOmega B OB obsB nu outB ->
  sem_lift S outA outB -> (forall x y, S (obsA x) (obsB y) -> T x y) ->
  free_omega_extended_upper_rel T mu nu.
Proof.
  intros Hl Hr Hcouple HT f g Hf Hg Hfg.
  pose lo a := extended_fiber_upper (fun x => obsA x = a) f.
  pose hi b := extended_fiber_lower (fun y => obsB y = b) g.
  have Hlo : nonnegative_test lo by intro a; apply extended_fiber_upper_nonnegative.
  have Hhi : nonnegative_test hi by intro b; apply extended_fiber_lower_nonnegative.
  eapply le_trans with (y := upper mu (fun x => lo (obsA x))).
  - apply free_omega_extended_upper_mono=> x. apply extended_fiber_upper_ge. reflexivity.
  - eapply le_trans with (y := upper nu (fun y => hi (obsB y))).
    + rewrite (free_omega_observes_extended_upper Hl Hlo)
        (free_omega_observes_extended_upper Hr Hhi).
      eapply enum_lift_extended_expect; [exact Hcouple|].
      intros a b Hab. apply extended_fiber_upper_lower; [exact Hg|].
      intros x y Hx Hy. apply Hfg, HT. by rewrite Hx Hy.
    + apply free_omega_extended_upper_mono=> y. apply extended_fiber_lower_le. reflexivity.
Qed.

Lemma free_omega_extended_upper_rel_restrict {A B} (T U : A -> B -> Prop)
    mu nu (P : A -> Prop) (Q : B -> Prop) :
  free_omega_extended_upper_rel T mu nu -> free_omega_ae P mu -> free_omega_ae Q nu ->
  (forall x y, T x y /\ P x /\ Q y -> U x y) -> free_omega_extended_upper_rel U mu nu.
Proof.
  intros Hrel HP HQ HT f g Hf Hg Hfg.
  pose f' x := if pselect (P x) then f x else 0.
  pose g' y := if pselect (Q y) then g y else +oo.
  have Hf' : nonnegative_test f'.
  { intro x. rewrite /f'. destruct (pselect (P x)); [exact (Hf x)|exact: lexx]. }
  have Hg' : nonnegative_test g'.
  { intro y. rewrite /g'. destruct (pselect (Q y)); [exact (Hg y)|exact: le0y]. }
  have Hl : upper mu f = upper mu f'.
  { apply free_omega_extended_upper_ae_ext.
    eapply free_omega_ae_mono; [|exact HP]. intros x Hx.
    rewrite /f'. by case: (pselect (P x)). }
  have Hr : upper nu g = upper nu g'.
  { apply free_omega_extended_upper_ae_ext.
    eapply free_omega_ae_mono; [|exact HQ]. intros y Hy.
    rewrite /g'. by case: (pselect (Q y)). }
  rewrite Hl Hr. apply Hrel; [exact Hf'|exact Hg'|].
  intros x y Hxy. rewrite /f' /g'.
  case: (pselect (P x))=> Hx; case: (pselect (Q y))=> Hy.
  - apply Hfg, HT. by repeat split.
  - exact: leey.
  - exact (Hg y).
  - exact: le0y.
Qed.

Lemma free_omega_extended_upper_rel_bind {A B C D} (T : A -> B -> Prop)
    (U : C -> D -> Prop) mu nu (k : A -> FreeOmega Enum C) (h : B -> FreeOmega Enum D) :
  free_omega_extended_upper_rel T mu nu ->
  (forall x y, T x y -> free_omega_extended_upper_rel U (k x) (h y)) ->
  free_omega_extended_upper_rel U (free_omega_bind mu k) (free_omega_bind nu h).
Proof.
  intros Hmu Hk f g Hf Hg Hfg. rewrite !free_omega_extended_upper_bind.
  apply Hmu.
  - intro x. exact: free_omega_extended_upper_nonnegative.
  - intro y. exact: free_omega_extended_upper_nonnegative.
  - intros x y Hxy. exact (Hk x y Hxy f g Hf Hg Hfg).
Qed.

Lemma free_omega_extended_upper_rel_sample {A B C D} (T : A -> B -> Prop)
    (U : C -> D -> Prop) mu nu (k : A -> FreeOmega Enum C) (h : B -> FreeOmega Enum D) :
  sem_lift T mu nu -> (forall x y, T x y -> free_omega_extended_upper_rel U (k x) (h y)) ->
  free_omega_extended_upper_rel U (FOSample mu k) (FOSample nu h).
Proof.
  intros Hmu Hk f g Hf Hg Hfg. cbn [free_omega_extended_upper].
  eapply enum_lift_extended_expect; [exact Hmu|].
  intros x y Hxy. exact (Hk x y Hxy f g Hf Hg Hfg).
Qed.

Lemma free_omega_extended_upper_rel_lub {A B} (T : A -> B -> Prop) c d :
  (forall n, free_omega_extended_upper_rel T (c n) (d n)) ->
  free_omega_extended_upper_rel T (FOLub c) (FOLub d).
Proof.
  intros H f g Hf Hg Hfg. cbn [free_omega_extended_upper].
  apply extended_upper_mono=> n. exact (H n f g Hf Hg Hfg).
Qed.
End RelationalExtendedUpper.
