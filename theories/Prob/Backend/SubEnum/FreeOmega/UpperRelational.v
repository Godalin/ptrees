(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From mathcomp.classical Require Import boolp classical_sets.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnum.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnum.FreeOmega.UpperExpectation PTree.Prob.Backend.SubEnum.FreeOmega.UpperCoupling PTree.Prob.Backend.SubEnum.FreeOmega.UpperObservation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** Internal scalar audit of relational quotient rules.  These bounded
    test inequalities are not a new public behavioral relation, nor an
    assertion that arbitrary raw FreeOmega terms are additive measures. *)
Section RelationalUpper.
Variable R : realType.
Local Notation upper := (free_omega_upper (R := R)).

Definition bounded_test {A} (f : A -> R) := forall x, 0 <= f x /\ f x <= 1.

(** Adding zero gives an inhabited supremum even for an empty fiber. *)
Definition fiber_upper {A} (P : A -> Prop) (f : A -> R) : R :=
  sup (fun r => r = 0 \/ exists x, P x /\ r = f x).

Lemma fiber_upper_le {A} (P : A -> Prop) (f : A -> R) b :
  0 <= b -> (forall x, P x -> f x <= b) -> fiber_upper P f <= b.
Proof.
  intros Hb Hf. apply sup_le_ub.
  - exists 0. by left.
  - apply/ubP=> r [->|[x [HP ->]]]; [exact Hb|exact (Hf x HP)].
Qed.

Lemma fiber_upper_bounds {A} (P : A -> Prop) (f : A -> R) :
  bounded_test f -> 0 <= fiber_upper P f /\ fiber_upper P f <= 1.
Proof.
  intro Hf. split.
  - apply sup_ubound.
    + exists 1. apply/ubP=> r [->|[x [_ ->]]]; [exact: ler01|exact (proj2 (Hf x))].
    + by left.
  - apply fiber_upper_le; [exact: ler01|]. intros x _. exact (proj2 (Hf x)).
Qed.

Lemma fiber_upper_ge {A} (P : A -> Prop) (f : A -> R) x :
  bounded_test f -> P x -> f x <= fiber_upper P f.
Proof.
  intros Hf Hx. apply sup_ubound.
  - exists 1. apply/ubP=> r [->|[y [_ ->]]]; [exact: ler01|exact (proj2 (Hf y))].
  - right. exists x. by split.
Qed.

Lemma bounded_test_complement {A} (f : A -> R) :
  bounded_test f -> bounded_test (fun x => 1 - f x).
Proof.
  intros Hf x. split.
  - rewrite subr_ge0. exact (proj2 (Hf x)).
  - rewrite lerBlDr lerDl. exact (proj1 (Hf x)).
Qed.

Definition fiber_lower {A} (P : A -> Prop) (f : A -> R) : R :=
  1 - fiber_upper P (fun x => 1 - f x).

Lemma fiber_lower_bounds {A} (P : A -> Prop) (f : A -> R) :
  bounded_test f -> 0 <= fiber_lower P f /\ fiber_lower P f <= 1.
Proof.
  intro Hf. have Hb := fiber_upper_bounds P (bounded_test_complement Hf).
  split.
  - rewrite /fiber_lower subr_ge0. exact (proj2 Hb).
  - rewrite /fiber_lower lerBlDr lerDl. exact (proj1 Hb).
Qed.

Lemma fiber_lower_le {A} (P : A -> Prop) (f : A -> R) x :
  bounded_test f -> P x -> fiber_lower P f <= f x.
Proof.
  intros Hf Hx. rewrite /fiber_lower lerBlDr addrC -lerBlDr.
  exact (fiber_upper_ge (bounded_test_complement Hf) Hx).
Qed.

Lemma fiber_upper_lower {A B} (P : A -> Prop) (Q : B -> Prop)
    (f : A -> R) (g : B -> R) :
  bounded_test f -> bounded_test g ->
  (forall x y, P x -> Q y -> f x <= g y) ->
  fiber_upper P f <= fiber_lower Q g.
Proof.
  intros Hf Hg Hfg. apply fiber_upper_le; [exact (proj1 (fiber_lower_bounds Q Hg))|].
  intros x Hx. rewrite /fiber_lower lerBrDr addrC -lerBrDr.
  apply fiber_upper_le.
  - rewrite subr_ge0. exact (proj2 (Hf x)).
  - intros y Hy. rewrite lerD2l lerN2. exact (Hfg x y Hx Hy).
Qed.

Definition free_omega_upper_rel {A B} (T : A -> B -> Prop)
    (mu : FreeOmega SubEnum A) (nu : FreeOmega SubEnum B) : Prop :=
  forall (f : A -> R) (g : B -> R),
    bounded_test f -> bounded_test g ->
    (forall x y, T x y -> f x <= g y) -> upper mu f <= upper nu g.

Lemma free_omega_upper_rel_mono {A B} (T U : A -> B -> Prop) mu nu :
  free_omega_upper_rel T mu nu ->
  (forall x y, T x y -> U x y) -> free_omega_upper_rel U mu nu.
Proof. intros H HT f g Hf Hg Hfg. apply H; auto. Qed.

(** Composition uses a bounded envelope on the intermediate carrier,
    without assuming equivalence or selecting a joint measure. *)
Lemma free_omega_upper_rel_comp {A B C} (T : A -> B -> Prop)
    (U : B -> C -> Prop) mu mid nu :
  free_omega_upper_rel T mu mid -> free_omega_upper_rel U mid nu ->
  free_omega_upper_rel (fun x z => exists y, T x y /\ U y z) mu nu.
Proof.
  intros Hleft Hright f g Hf Hg Hfg.
  pose (h := fun y => fiber_upper (fun x => T x y) f).
  have Hh : bounded_test h by intro y; apply fiber_upper_bounds.
  eapply le_trans.
  - apply (Hleft f h Hf Hh). intros x y Hxy. exact (fiber_upper_ge Hf Hxy).
  - apply (Hright h g Hh Hg). intros y z Hyz. apply fiber_upper_le.
    + exact (proj1 (Hg z)).
    + intros x Hxy. apply Hfg. exists y. by split.
Qed.

(** The tests need not factor through the observation maps.  Upper and
    lower envelopes compare every fiber, including empty fibers. *)
Theorem free_omega_observes_upper_rel {A B OA OB}
    (T : A -> B -> Prop) (S : OA -> OB -> Prop)
    (obsA : A -> OA) (obsB : B -> OB) mu nu outA outB :
  @free_omega_observes SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
    A OA obsA mu outA ->
  @free_omega_observes SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
    B OB obsB nu outB ->
  sem_lift S outA outB ->
  (forall x y, S (obsA x) (obsB y) -> T x y) ->
  free_omega_upper_rel T mu nu.
Proof.
  intros Hleft Hright Hcouple HT f g Hf Hg Hfg.
  pose (lo := fun a => fiber_upper (fun x => obsA x = a) f).
  pose (hi := fun b => fiber_lower (fun y => obsB y = b) g).
  have Hlo : bounded_test lo by intro a; apply fiber_upper_bounds.
  have Hhi : bounded_test hi by intro b; apply fiber_lower_bounds.
  eapply le_trans with (y := upper mu (fun x => lo (obsA x))).
  - apply free_omega_upper_mono; [intro x; apply Hlo|].
    intro x. apply fiber_upper_ge; [exact Hf|reflexivity].
  - eapply le_trans with (y := upper nu (fun y => hi (obsB y))).
    + rewrite (free_omega_observes_upper Hleft Hlo)
        (free_omega_observes_upper Hright Hhi).
      eapply subenum_lift_real_expect; [exact Hcouple|].
      intros a b Hab. apply fiber_upper_lower; [exact Hf|exact Hg|].
      intros x y Hx Hy. apply Hfg, HT. by rewrite Hx Hy.
    + apply free_omega_upper_mono; [exact Hg|].
      intro y. apply fiber_lower_le; [exact Hg|reflexivity].
Qed.

Lemma free_omega_upper_rel_restrict {A B} (T U : A -> B -> Prop)
    mu nu (P : A -> Prop) (Q : B -> Prop) :
  free_omega_upper_rel T mu nu ->
  free_omega_ae P mu -> free_omega_ae Q nu ->
  (forall x y, T x y /\ P x /\ Q y -> U x y) ->
  free_omega_upper_rel U mu nu.
Proof.
  intros Hrel HP HQ HT f g Hf Hg Hfg.
  pose (f' := fun x => if pselect (P x) then f x else 0).
  pose (g' := fun y => if pselect (Q y) then g y else 1).
  have Hf' : bounded_test f'.
  { intro x. rewrite /f'. destruct (pselect (P x)) as [Hx|Hnot]; [exact (Hf x)|].
    split; [exact: lexx|exact: ler01]. }
  have Hg' : bounded_test g'.
  { intro y. rewrite /g'. destruct (pselect (Q y)) as [Hy|Hnot]; [exact (Hg y)|].
    split; [exact: ler01|exact: lexx]. }
  have Hleft : upper mu f = upper mu f'.
  { apply free_omega_upper_ae_ext; [exact Hf|exact Hf'|].
    eapply free_omega_ae_mono; [|exact HP]. intros x Hx.
    rewrite /f'. by case: (pselect (P x)). }
  have Hright : upper nu g = upper nu g'.
  { apply free_omega_upper_ae_ext; [exact Hg|exact Hg'|].
    eapply free_omega_ae_mono; [|exact HQ]. intros y Hy.
    rewrite /g'. by case: (pselect (Q y)). }
  rewrite Hleft Hright. apply Hrel; [exact Hf'|exact Hg'|].
  intros x y Hxy. rewrite /f' /g'.
  case: (pselect (P x))=> Hx; case: (pselect (Q y))=> Hy.
  - apply Hfg, HT. by repeat split.
  - exact (proj2 (Hf x)).
  - exact (proj1 (Hg y)).
  - exact: ler01.
Qed.

Lemma free_omega_upper_rel_bind {A B C D} (T : A -> B -> Prop)
    (U : C -> D -> Prop) mu nu (k : A -> FreeOmega SubEnum C)
    (h : B -> FreeOmega SubEnum D) :
  free_omega_upper_rel T mu nu ->
  (forall x y, T x y -> free_omega_upper_rel U (k x) (h y)) ->
  free_omega_upper_rel U (free_omega_bind mu k) (free_omega_bind nu h).
Proof.
  intros Hmu Hk f g Hf Hg Hfg. rewrite !free_omega_upper_bind.
  apply Hmu.
  - intro x. exact (free_omega_upper_bounds (k x) Hf).
  - intro y. exact (free_omega_upper_bounds (h y) Hg).
  - intros x y Hxy. exact (Hk x y Hxy f g Hf Hg Hfg).
Qed.

Lemma free_omega_upper_rel_sample {A B C D} (T : A -> B -> Prop)
    (U : C -> D -> Prop) mu nu (k : A -> FreeOmega SubEnum C)
    (h : B -> FreeOmega SubEnum D) :
  sem_lift T mu nu ->
  (forall x y, T x y -> free_omega_upper_rel U (k x) (h y)) ->
  free_omega_upper_rel U (FOSample mu k) (FOSample nu h).
Proof.
  intros Hmu Hk f g Hf Hg Hfg. cbn [free_omega_upper].
  eapply subenum_lift_real_expect; [exact Hmu|].
  intros x y Hxy. exact (Hk x y Hxy f g Hf Hg Hfg).
Qed.

Lemma free_omega_upper_rel_lub {A B} (T : A -> B -> Prop) c d :
  (forall n, free_omega_upper_rel T (c n) (d n)) ->
  free_omega_upper_rel T (FOLub c) (FOLub d).
Proof.
  intros H f g Hf Hg Hfg. cbn [free_omega_upper].
  apply countable_upper_le=> n. eapply le_trans; [exact (H n f g Hf Hg Hfg)|].
  exact (@countable_upper_ge R (fun i => upper (d i) g) 1 n
    (fun i => proj2 (free_omega_upper_bounds (d i) Hg))).
Qed.
End RelationalUpper.
