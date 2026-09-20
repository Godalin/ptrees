(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From mathcomp.analysis Require Import ereal.
From PTree.Prob.Backend Require Import DiscreteMC.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.Backend Require Import TwoLevelMeasureEnum.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Prob.Backend.FreeOmega Require Import FreeOmegaUpperExpectationEnum FreeOmegaUpperCouplingEnum FreeOmegaUpperContinuityEnum FreeOmegaUpperRelationalEnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Import DiscreteMC.Enum.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Both directions are carried by the induction: symmetry is not obtained
    by complementing an upper expectation, which need not be additive. *)
Section QuotientAudit.
Variable F : realType.
Local Notation upper := (free_omega_extended_upper (R := F)).
Local Notation test := (nonnegative_test (R := F)).
Local Notation directed := (free_omega_extended_upper_rel F).

Definition free_omega_extended_upper_birel {A B} (T : A -> B -> Prop) mu nu :=
  directed T mu nu /\ directed (fun y x => T x y) nu mu.
Local Notation related := free_omega_extended_upper_birel.

Lemma extended_upper_birel_mono {A B} (T U : A -> B -> Prop) mu nu :
  related T mu nu -> (forall x y, T x y -> U x y) -> related U mu nu.
Proof.
  intros [Hl Hr] HT. split; eapply free_omega_extended_upper_rel_mono; eauto.
Qed.

Lemma extended_upper_birel_ext {A B} (T : A -> B -> Prop) mu nu mu' nu' :
  (forall f, test f -> upper mu f = upper mu' f) ->
  (forall g, test g -> upper nu g = upper nu' g) ->
  related T mu' nu' -> related T mu nu.
Proof.
  intros Hmu Hnu [Hl Hr]. split; intros f g Hf Hg Hfg.
  - rewrite (Hmu f Hf) (Hnu g Hg). exact (Hl f g Hf Hg Hfg).
  - rewrite (Hnu f Hf) (Hmu g Hg). exact (Hr f g Hf Hg Hfg).
Qed.

Lemma extended_upper_birel_comp {A B C} (T : A -> B -> Prop) (U : B -> C -> Prop)
    (V : A -> C -> Prop) mu mid nu :
  related T mu mid -> related U mid nu ->
  (forall x z, (exists y, T x y /\ U y z) -> V x z) -> related V mu nu.
Proof.
  intros [Hl1 Hr1] [Hl2 Hr2] HV. split.
  - eapply free_omega_extended_upper_rel_mono; [eapply free_omega_extended_upper_rel_comp; eassumption|exact HV].
  - eapply free_omega_extended_upper_rel_mono; [eapply free_omega_extended_upper_rel_comp; eassumption|].
    intros z x [y [Hy Hx]]. apply HV. exists y. by split.
Qed.

Lemma extended_upper_birel_bind {A B C D} (T : A -> B -> Prop) (U : C -> D -> Prop)
    mu nu (k : A -> FreeOmega Enum C) (h : B -> FreeOmega Enum D) :
  related T mu nu -> (forall x y, T x y -> related U (k x) (h y)) ->
  related U (free_omega_bind mu k) (free_omega_bind nu h).
Proof.
  intros [Hl Hr] Hk. split.
  - eapply free_omega_extended_upper_rel_bind; [exact Hl|]. intros x y Hxy. exact (proj1 (Hk x y Hxy)).
  - eapply free_omega_extended_upper_rel_bind; [exact Hr|]. intros y x Hxy. exact (proj2 (Hk x y Hxy)).
Qed.

Lemma extended_upper_birel_sample {A B C D} (T : A -> B -> Prop) (U : C -> D -> Prop)
    mu nu (k : A -> FreeOmega Enum C) (h : B -> FreeOmega Enum D) :
  sem_lift T mu nu -> (forall x y, T x y -> related U (k x) (h y)) ->
  related U (FOSample mu k) (FOSample nu h).
Proof.
  intros Hmu Hk. split.
  - eapply free_omega_extended_upper_rel_sample; [exact Hmu|]. intros x y Hxy. exact (proj1 (Hk x y Hxy)).
  - eapply free_omega_extended_upper_rel_sample; [apply sem_lift_sym; exact Hmu|].
    intros y x Hxy. exact (proj2 (Hk x y Hxy)).
Qed.

Lemma extended_upper_birel_lub {A B} (T : A -> B -> Prop) c d :
  (forall n, related T (c n) (d n)) -> related T (FOLub c) (FOLub d).
Proof.
  intro H. split; apply free_omega_extended_upper_rel_lub; intro n;
    [exact (proj1 (H n))|exact (proj2 (H n))].
Qed.

Lemma extended_upper_birel_sample_ae {A B C} (T : A -> B -> Prop) (mu : Enum C)
    (Good : C -> Prop) (k : C -> FreeOmega Enum A) (h : C -> FreeOmega Enum B) :
  sem_ae mu Good -> (forall x, Good x -> related T (k x) (h x)) ->
  related T (FOSample mu k) (FOSample mu h).
Proof.
  intros HGood Hk. split; intros f g Hf Hg Hfg; cbn [free_omega_extended_upper];
    apply enum_extended_expect_ae_mono.
  - change (sem_ae mu (fun x => upper (k x) f <= upper (h x) g)).
    eapply sem_ae_mono; [|exact HGood]. intros x Hx. exact (proj1 (Hk x Hx) f g Hf Hg Hfg).
  - change (sem_ae mu (fun x => upper (h x) f <= upper (k x) g)).
    eapply sem_ae_mono; [|exact HGood]. intros x Hx. exact (proj2 (Hk x Hx) f g Hf Hg Hfg).
Qed.

Lemma extended_upper_sample_product {A X Y} (mu : Enum X) (nu : Enum Y)
    (k : X -> Y -> FreeOmega Enum A) f :
  test f ->
  upper (FOSample (semantic_product mu nu) (fun p => k (fst p) (snd p))) f =
  upper (FOSample mu (fun x => FOSample nu (k x))) f.
Proof.
  intro Hf.
  change (enum_extended_expect
    (fun p => upper (k (fst p) (snd p)) f)
    (Enum.bind_Enum mu (fun x =>
      Enum.bind_Enum nu (fun y => Enum.ret_Enum (x,y)))) =
    enum_extended_expect (fun x => enum_extended_expect (fun y => upper (k x y) f)
      nu) mu).
  rewrite enum_extended_expect_bind; last by intros [x y]; apply free_omega_extended_upper_nonnegative.
  f_equal. apply functional_extensionality=> x.
  rewrite enum_extended_expect_bind; last by intros [a b]; apply free_omega_extended_upper_nonnegative.
  f_equal. apply functional_extensionality=> y.
  change ((ratr (1 : rat))%:E * upper (k x y) f + 0 = upper (k x y) f).
  by rewrite rmorph1 mul1e adde0.
Qed.

Lemma extended_upper_zero_prefix {A} (c : nat -> FreeOmega Enum A) f :
  test f ->
  upper (FOLub (fun n => match n with O => FOZero | S n => c n end)) f =
  upper (FOLub c) f.
Proof.
  intro Hf. cbn [free_omega_extended_upper]. apply/eqP. rewrite eq_le. apply/andP. split.
  - apply extended_upper_le. intros [|n].
    + change (0 <= upper (FOLub c) f). exact: free_omega_extended_upper_nonnegative.
    + exact (@extended_upper_ge F (fun i => upper (c i) f) n).
  - apply extended_upper_le=> n.
    apply (@extended_upper_ge F
      (fun i => upper (match i with O => FOZero | S j => c j end) f) (S n)).
Qed.

Theorem free_omega_qlift_extended_upper_birel {A B} (T : A -> B -> Prop) mu nu :
  @free_omega_qlift Enum Enum_SemanticMeasure Enum_SemanticOmega
    A B T mu nu -> related T mu nu.
Proof.
  intro Hq. induction Hq.
  - split; intros f g Hf Hg Hfg.
    + exact (free_omega_structural_extended_upper H Hg Hfg).
    + exact (free_omega_structural_extended_upper (free_omega_lift_sym H) Hg Hfg).
  - split.
    + eapply free_omega_observes_extended_upper_rel; eassumption.
    + eapply free_omega_observes_extended_upper_rel; [exact H0|exact H|apply sem_lift_sym; exact H1|].
      intros y x Hxy. exact (H2 x y Hxy).
  - destruct IHHq as [Hl Hr]. split.
    + eapply free_omega_extended_upper_rel_restrict; eassumption.
    + eapply free_omega_extended_upper_rel_restrict; [exact Hr|exact H0|exact H|].
      intros y x [Hxy [Hy Hx]]. apply H1. by repeat split.
  - eapply extended_upper_birel_mono; eassumption.
  - destruct IHHq as [Hl Hr]. by split.
  - eapply extended_upper_birel_comp; eassumption.
  - eapply extended_upper_birel_bind; eassumption.
  - eapply extended_upper_birel_sample; eassumption.
  - eapply extended_upper_birel_ext with (mu' := k x) (nu' := nu); [|reflexivity|exact IHHq].
    intros f Hf. change ((ratr (1 : rat))%:E * upper (k x) f + 0 = upper (k x) f).
    by rewrite rmorph1 mul1e adde0.
  - eapply extended_upper_birel_ext with
        (mu' := FOSample (sem_bind mu h) k) (nu' := FOSample (sem_bind mu h) l).
    + intros f Hf. apply free_omega_sample_bind_extended_upper. exact Hf.
    + reflexivity.
    + eapply extended_upper_birel_sample with (T := eq).
      * apply sem_lift_refl. intro y. reflexivity.
      * intros y z ->. auto.
  - eapply extended_upper_birel_ext with
        (mu' := FOSample (semantic_product mu nu) (fun p => k (fst p) (snd p)))
        (nu' := FOSample (semantic_product nu mu) (fun p => l (fst p) (snd p))).
    + intros f Hf. symmetry. apply extended_upper_sample_product. exact Hf.
    + intros g Hg. symmetry. apply extended_upper_sample_product. exact Hg.
    + eapply extended_upper_birel_sample; [exact H|].
      intros [x y] [y' x'] Hswap. cbn in Hswap. destruct Hswap as [-> ->]. auto.
  - apply extended_upper_birel_lub. assumption.
  - eapply extended_upper_birel_ext with (mu' := FOLub c) (nu' := FOLub d).
    + exact (extended_upper_zero_prefix c).
    + reflexivity.
    + apply extended_upper_birel_lub. assumption.
  - eapply extended_upper_birel_ext with (mu' := FOLub c) (nu' := FOLub d).
    + reflexivity.
    + exact (extended_upper_zero_prefix d).
    + apply extended_upper_birel_lub. assumption.
  - eapply extended_upper_birel_ext with (mu' := FOSample mu out)
        (nu' := FOSample mu (fun x => FOLub (chain x))).
    + reflexivity.
    + intros g Hg. symmetry. apply free_omega_sample_lub_extended_upper; [|exact Hg].
      change (sem_ae mu (fun x => forall n, free_omega_approx eq (chain x n) (chain x (S n)))).
      eapply sem_ae_mono; [|exact H]. exact H0.
    + eapply extended_upper_birel_sample_ae; eassumption.
  - split; intros f g Hf Hg Hfg; cbn [free_omega_extended_upper];
      rewrite enum_extended_expect_zero; exact: lexx.
  - eapply extended_upper_birel_ext with (mu' := mu) (nu' := nu); [reflexivity| |exact IHHq].
    intros g Hg. cbn [free_omega_extended_upper]. apply extended_upper_constant.
  - eapply extended_upper_birel_ext with
        (mu' := free_omega_bind source_out kernel_out)
        (nu' := free_omega_bind (FOLub source) (fun x => FOLub (kernels x))).
    + reflexivity.
    + intros g Hg. symmetry. apply free_omega_bind_lub_extended_upper; assumption.
    + eapply extended_upper_birel_bind with (T := eq); [exact IHHq|]. intros x y ->. auto.
  - destruct HAB. cbn.
    eapply extended_upper_birel_ext with
      (mu' := FOLub (fun fuel => grid fuel fuel))
      (nu' := FOLub (fun fuel => grid fuel fuel)).
    + intros f Hf. apply free_omega_diagonal_extended_upper; assumption.
    + reflexivity.
    + split; intros f g Hf Hg Hfg; apply free_omega_extended_upper_mono;
        intro x; apply Hfg, H1.
  - destruct H1 as [Hl Hr]. split; intros f g Hf Hg Hfg;
      eapply free_omega_cofinal_extended_upper_le; eassumption.
Qed.

Corollary free_omega_qlift_extended_upper {A B} (T : A -> B -> Prop) mu nu
    (f : A -> \bar F) (g : B -> \bar F) :
  @free_omega_qlift Enum Enum_SemanticMeasure Enum_SemanticOmega
    A B T mu nu ->
  test f -> test g -> (forall x y, T x y -> f x <= g y) ->
  upper mu f <= upper nu g.
Proof. intro H. exact (proj1 (free_omega_qlift_extended_upper_birel H) f g). Qed.

Corollary free_omega_qlift_eq_extended_upper {A} (mu nu : FreeOmega Enum A) f :
  @free_omega_qlift Enum Enum_SemanticMeasure Enum_SemanticOmega
    A A eq mu nu -> test f -> upper mu f = upper nu f.
Proof.
  intros H Hf. destruct (free_omega_qlift_extended_upper_birel H) as [Hl Hr].
  apply/eqP. rewrite eq_le. apply/andP. split.
  - apply Hl; [exact Hf|exact Hf|]. intros x y ->. exact: lexx.
  - apply Hr; [exact Hf|exact Hf|]. intros x y ->. exact: lexx.
Qed.

(** Even unrelated carriers and a completely permissive relation cannot
    change mass.  This covers arbitrary combinations of quotient rules. *)
Corollary free_omega_qlift_extended_upper_mass {A B} (T : A -> B -> Prop) mu nu :
  @free_omega_qlift Enum Enum_SemanticMeasure Enum_SemanticOmega
    A B T mu nu -> upper mu (fun _ => 1) = upper nu (fun _ => 1).
Proof.
  intro H. destruct (free_omega_qlift_extended_upper_birel H) as [Hl Hr].
  have Hone : forall X : Type, test (fun _ : X => (1 : \bar F)).
  { intros X x. exact: lee01. }
  apply/eqP. rewrite eq_le. apply/andP. split.
  - apply Hl; [apply Hone|apply Hone|]. intros x y _. exact: lexx.
  - apply Hr; [apply Hone|apply Hone|]. intros x y _. exact: lexx.
Qed.
End QuotientAudit.
