(** Role: External bounded-test validation of ALL raw quotient constructors.
    Both directions are carried by induction; arbitrary raw upper evaluators
    need not be additive, so symmetry cannot be recovered by complements.
    Native interpretation obligations are explicit; none asserts a FreeOmega
    soundness result or the existence of an external joint. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals boolp classical_sets.
From PTree.Prob.Interface Require Import Measure Omega.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation
  PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient.
From PTree.Prob.FreeOmega.Validation Require Import Expectation Continuity Observation Relational.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section QuotientValidation.
Context {MN : Type -> Type} {R : realType}.
Context `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}.
Variable native : forall X, MN X -> OmegaVal R X.
Arguments native {X} _.
Hypothesis native_ae : forall X (mu : MN X) P, sem_ae mu P -> oval_ae (native mu) P.
Hypothesis native_ret : forall X (x : X), oval_eq (native (sem_ret x)) (oval_ret R x).
Hypothesis native_zero : forall X, oval_eq (native (@sem_zero MN NI NO X)) (@oval_bottom R X).
Hypothesis native_bind : forall X Y (mu : MN X) (k : X -> MN Y),
  oval_eq (native (sem_bind mu k)) (oval_bind (native mu) (fun x => native (k x))).
Hypothesis native_lift : forall X Y (T : X -> Y -> Prop) (mu : MN X) (nu : MN Y) f g,
  sem_lift T mu nu -> oval_test f -> oval_test g ->
  (forall x y, T x y -> f x <= g y) -> oval_eval (native mu) f <= oval_eval (native nu) g.
Hypothesis native_lub : forall X (c : nat -> MN X) out,
  (forall n f, oval_test f -> oval_eval (native (c n)) f <= oval_eval (native (c (S n))) f) ->
  sem_lub c out -> forall f, oval_test f ->
  oval_sup (fun n => oval_eval (native (c n)) f) = oval_eval (native out) f.
Local Notation upper := (free_omega_model_upper (@native)).


Local Notation test := (@oval_test R).
Local Notation directed := (model_upper_rel (@native)).
Definition model_upper_birel {A B} (T : A -> B -> Prop) mu nu :=
  directed T mu nu /\ directed (fun y x => T x y) nu mu.
Local Notation related := model_upper_birel.

Lemma model_birel_mono {A B} (T U : A -> B -> Prop) mu nu :
  related T mu nu -> (forall x y, T x y -> U x y) -> related U mu nu.
Proof.
  intros [Hl Hr] HT. split; eapply model_upper_rel_mono; eauto.
Qed.

Lemma model_birel_ext {A B} (T : A -> B -> Prop) mu nu mu' nu' :
  (forall f, test f -> upper mu f = upper mu' f) ->
  (forall g, test g -> upper nu g = upper nu' g) ->
  related T mu' nu' -> related T mu nu.
Proof.
  intros Hmu Hnu [Hl Hr]. split; intros f g Hf Hg Hfg.
  - rewrite (Hmu f Hf) (Hnu g Hg). exact (Hl f g Hf Hg Hfg).
  - rewrite (Hnu f Hf) (Hmu g Hg). exact (Hr f g Hf Hg Hfg).
Qed.

Lemma model_birel_comp {A B C} (T : A -> B -> Prop) (U : B -> C -> Prop)
    (V : A -> C -> Prop) mu mid nu :
  related T mu mid -> related U mid nu ->
  (forall x z, (exists y, T x y /\ U y z) -> V x z) -> related V mu nu.
Proof.
  intros [Hl1 Hr1] [Hl2 Hr2] HV. split.
  - eapply model_upper_rel_mono; [eapply model_upper_rel_comp; eassumption|exact HV].
  - eapply model_upper_rel_mono; [eapply model_upper_rel_comp; eassumption|].
    intros z x [y [Hy Hx]]. apply HV. exists y. by split.
Qed.

Lemma model_birel_bind {A B C D} (T : A -> B -> Prop) (U : C -> D -> Prop)
    mu nu (k : A -> FreeOmega MN C) (h : B -> FreeOmega MN D) :
  related T mu nu -> (forall x y, T x y -> related U (k x) (h y)) ->
  related U (free_omega_bind mu k) (free_omega_bind nu h).
Proof.
  intros [Hl Hr] Hk. split.
  - eapply model_upper_rel_bind; [exact Hl|]. intros x y Hxy. exact (proj1 (Hk x y Hxy)).
  - eapply model_upper_rel_bind; [exact Hr|]. intros y x Hxy. exact (proj2 (Hk x y Hxy)).
Qed.

Lemma model_birel_sample {A B C D} (T : A -> B -> Prop) (U : C -> D -> Prop)
    mu nu (k : A -> FreeOmega MN C) (h : B -> FreeOmega MN D) :
  sem_lift T mu nu -> (forall x y, T x y -> related U (k x) (h y)) ->
  related U (FOSample mu k) (FOSample nu h).
Proof.
  intros Hmu Hk. split.
  - eapply model_upper_rel_sample; [exact native_lift|exact Hmu|]. intros x y Hxy. exact (proj1 (Hk x y Hxy)).
  - eapply model_upper_rel_sample; [exact native_lift|apply sem_lift_sym; exact Hmu|].
    intros y x Hxy. exact (proj2 (Hk x y Hxy)).
Qed.

Lemma model_birel_lub {A B} (T : A -> B -> Prop) c d :
  (forall n, related T (c n) (d n)) -> related T (FOLub c) (FOLub d).
Proof.
  intro H. split; apply model_upper_rel_lub; intro n;
    [exact (proj1 (H n))|exact (proj2 (H n))].
Qed.

Lemma model_birel_sample_ae {A B C} (T : A -> B -> Prop) (mu : MN C)
    (Good : C -> Prop) (k : C -> FreeOmega MN A) (h : C -> FreeOmega MN B) :
  sem_ae mu Good -> (forall x, Good x -> related T (k x) (h x)) ->
  related T (FOSample mu k) (FOSample mu h).
Proof.
  intros HGood Hk. split; intros f g Hf Hg Hfg; cbn [free_omega_model_upper].
  - apply (oval_ae_le (native_ae HGood)).
    + intro x; exact (model_upper_bounds (@native) (k x) Hf).
    + intro x; exact (model_upper_bounds (@native) (h x) Hg).
    + intros x Hx; exact (proj1 (Hk x Hx) f g Hf Hg Hfg).
  - apply (oval_ae_le (native_ae HGood)).
    + intro x; exact (model_upper_bounds (@native) (h x) Hf).
    + intro x; exact (model_upper_bounds (@native) (k x) Hg).
    + intros x Hx; exact (proj2 (Hk x Hx) f g Hf Hg Hfg).
Qed.

Lemma upper_sample_product {A X Y} (mu : MN X) (nu : MN Y)
    (k : X -> Y -> FreeOmega MN A) f :
  test f -> upper (FOSample (semantic_product mu nu) (fun p => k (fst p) (snd p))) f =
  upper (FOSample mu (fun x => FOSample nu (k x))) f.
Proof.
  intro Hf; cbn [free_omega_model_upper]; unfold semantic_product.
  rewrite (native_bind mu _ (fun p => model_upper_bounds (@native) (k (fst p) (snd p)) Hf)).
  change (oval_eval (native mu) (fun x => oval_eval (native (sem_bind nu (fun y => sem_ret (x,y))))
    (fun p => upper (k (fst p) (snd p)) f)) =
    oval_eval (native mu) (fun x => oval_eval (native nu) (fun y => upper (k x y) f))).
  apply oval_eval_ext=> x.
  rewrite (native_bind nu _ (fun p => model_upper_bounds (@native) (k (fst p) (snd p)) Hf)).
  change (oval_eval (native nu) (fun y => oval_eval (native (sem_ret (x,y)))
    (fun p => upper (k (fst p) (snd p)) f)) =
    oval_eval (native nu) (fun y => upper (k x y) f)).
  apply oval_eval_ext=> y.
  exact (native_ret (x,y) (fun p => model_upper_bounds (@native) (k (fst p) (snd p)) Hf)).
Qed.

Lemma upper_zero_prefix {A} (c : nat -> FreeOmega MN A) f :
  test f ->
  upper (FOLub (fun n => match n with O => FOZero | S n => c n end)) f =
  upper (FOLub c) f.
Proof.
  intro Hf. cbn [free_omega_model_upper]. apply/eqP. rewrite eq_le. apply/andP. split.
  - apply oval_sup_le. intros [|n].
    + change (0 <= upper (FOLub c) f). exact (proj1 (model_upper_bounds (@native) _ Hf)).
    + exact (@oval_sup_ge R (fun i => upper (c i) f) 1 n
        (fun i => proj2 (model_upper_bounds (@native) _ Hf))).
  - apply oval_sup_le=> n.
    apply (@oval_sup_ge R
      (fun i => upper (match i with O => FOZero | S j => c j end) f) 1 (S n)).
    intros [|i]; [exact: ler01|exact (proj2 (model_upper_bounds (@native) _ Hf))].
Qed.

Lemma model_cofinal_upper_le {A B} (T : A -> B -> Prop)
    (c : nat -> FreeOmega MN A) (d : nat -> FreeOmega MN B) f g :
  (forall n, exists m, free_omega_approx T (c n) (d m)) ->
  test f -> test g -> (forall x y, T x y -> f x <= g y) ->
  upper (FOLub c) f <= upper (FOLub d) g.
Proof.
  intros H Hf Hg Hfg; apply oval_sup_le=> n; destruct (H n) as [m Hm].
  eapply le_trans.
  - eapply model_upper_approx; [exact native_lift|exact Hm|exact Hf|exact Hg|exact Hfg].
  - exact (oval_sup_ge m (fun i => proj2 (model_upper_bounds (@native) (d i) Hg))).
Qed.

Theorem model_qlift_bidual_raw {A B} (T : A -> B -> Prop) mu nu :
  @free_omega_qlift MN NI NO
    A B T mu nu -> related T mu nu.
Proof.
  intro Hq. induction Hq.
  - split; intros f g Hf Hg Hfg.
    + eapply model_upper_approx; [exact native_lift|exact (free_omega_lift_to_approx H)|exact Hf|exact Hg|exact Hfg].
    + eapply model_upper_approx; [exact native_lift|exact (free_omega_lift_to_approx (free_omega_lift_sym H))|exact Hf|exact Hg|exact Hfg].
  - split.
    + eapply model_observes_upper_rel; eassumption.
    + eapply model_observes_upper_rel; [exact native_ret|exact native_zero|exact native_bind|exact native_lift|exact native_lub|exact H0|exact H|apply sem_lift_sym; exact H1|].
      intros y x Hxy. exact (H2 x y Hxy).
  - destruct IHHq as [Hl Hr]. split.
    + eapply model_upper_rel_restrict; eassumption.
    + eapply model_upper_rel_restrict; [exact native_ae|exact Hr|exact H0|exact H|].
      intros y x [Hxy [Hy Hx]]. apply H1. by repeat split.
  - eapply model_birel_mono; eassumption.
  - destruct IHHq as [Hl Hr]. by split.
  - eapply model_birel_comp; eassumption.
  - eapply model_birel_bind; eassumption.
  - eapply model_birel_sample; eassumption.
  - eapply model_birel_ext with (mu' := k x) (nu' := nu); [|reflexivity|exact IHHq].
    intros f Hf; exact (native_ret x (fun y => model_upper_bounds (@native) (k y) Hf)).
  - eapply model_birel_ext with
        (mu' := FOSample (sem_bind mu h) k) (nu' := FOSample (sem_bind mu h) l).
    + intros f Hf; symmetry; exact (native_bind mu h (fun y => model_upper_bounds (@native) (k y) Hf)).
    + reflexivity.
    + eapply model_birel_sample with (T := eq).
      * apply sem_lift_refl. intro y. reflexivity.
      * intros y z ->. auto.
  - eapply model_birel_ext with
        (mu' := FOSample (semantic_product mu nu) (fun p => k (fst p) (snd p)))
        (nu' := FOSample (semantic_product nu mu) (fun p => l (fst p) (snd p))).
    + intros f Hf. symmetry. apply upper_sample_product; assumption.
    + intros g Hg. symmetry. apply upper_sample_product; assumption.
    + eapply model_birel_sample; [exact H|].
      intros [x y] [y' x'] Hswap. cbn in Hswap. destruct Hswap as [-> ->]. auto.
  - apply model_birel_lub. assumption.
  - eapply model_birel_ext with (mu' := FOLub c) (nu' := FOLub d).
    + exact (upper_zero_prefix c).
    + reflexivity.
    + apply model_birel_lub. assumption.
  - eapply model_birel_ext with (mu' := FOLub c) (nu' := FOLub d).
    + reflexivity.
    + exact (upper_zero_prefix d).
    + apply model_birel_lub. assumption.
  - eapply model_birel_ext with (mu' := FOSample mu out)
        (nu' := FOSample mu (fun x => FOLub (chain x))).
    + reflexivity.
    + intros g Hg. symmetry. eapply model_sample_lub; [exact native_ae|exact native_lift| |exact Hg].
      change (sem_ae mu (fun x => forall n, free_omega_approx eq (chain x n) (chain x (S n)))).
      eapply sem_ae_mono; [|exact H]. exact H0.
    + eapply model_birel_sample_ae; eassumption.
  - split; intros f g Hf Hg Hfg; cbn [free_omega_model_upper];
      rewrite (oval_zero (oval_laws (native mu))); exact: lexx.
  - eapply model_birel_ext with (mu' := mu) (nu' := nu); [reflexivity| |exact IHHq].
    intros g Hg. cbn [free_omega_model_upper]. apply oval_sup_const.
  - eapply model_birel_ext with
        (mu' := free_omega_bind source_out kernel_out)
        (nu' := free_omega_bind (FOLub source) (fun x => FOLub (kernels x))).
    + reflexivity.
    + intros g Hg. symmetry. eapply model_bind_lub; eassumption.
    + eapply model_birel_bind with (T := eq); [exact IHHq|]. intros x y ->. auto.
  - destruct HAB. cbn.
    eapply model_birel_ext with
      (mu' := FOLub (fun fuel => grid fuel fuel))
      (nu' := FOLub (fun fuel => grid fuel fuel)).
    + intros f Hf. eapply model_diagonal_upper; eassumption.
    + reflexivity.
    + split; intros f g Hf Hg Hfg; apply model_upper_mono; [exact Hf|exact Hg| |exact Hf|exact Hg|];
        intro x; apply Hfg, H1.
  - destruct H1 as [Hl Hr]. split; intros f g Hf Hg Hfg;
      eapply model_cofinal_upper_le; eassumption.
Qed.

Corollary model_qlift_upper {A B} (T : A -> B -> Prop) mu nu
    (f : A -> R) (g : B -> R) :
  @free_omega_qlift MN NI NO
    A B T mu nu ->
  test f -> test g -> (forall x y, T x y -> f x <= g y) ->
  upper mu f <= upper nu g.
Proof. intro H. exact (proj1 (model_qlift_bidual_raw H) f g). Qed.

Corollary model_qlift_eq_upper {A} (mu nu : FreeOmega MN A) f :
  @free_omega_qlift MN NI NO
    A A eq mu nu -> test f -> upper mu f = upper nu f.
Proof.
  intros H Hf. destruct (model_qlift_bidual_raw H) as [Hl Hr].
  apply/eqP. rewrite eq_le. apply/andP. split.
  - apply Hl; [exact Hf|exact Hf|]. intros x y ->. exact: lexx.
  - apply Hr; [exact Hf|exact Hf|]. intros x y ->. exact: lexx.
Qed.

(** Even unrelated carriers and a completely permissive relation cannot
    change mass.  This covers arbitrary combinations of quotient rules. *)
Corollary model_qlift_upper_mass {A B} (T : A -> B -> Prop) mu nu :
  @free_omega_qlift MN NI NO
    A B T mu nu -> upper mu (fun _ => 1) = upper nu (fun _ => 1).
Proof.
  intro H. destruct (model_qlift_bidual_raw H) as [Hl Hr].
  have Hone : forall X : Type, test (fun _ : X => (1 : R)).
  { intros X x. split; [exact: ler01|exact: lexx]. }
  apply/eqP. rewrite eq_le. apply/andP. split.
  - apply Hl; [apply Hone|apply Hone|]. intros x y _. exact: lexx.
  - apply Hr; [apply Hone|apply Hone|]. intros x y _. exact: lexx.
Qed.

(** Only the endpoints must denote probability objects. The induction
    above deliberately does not require validity of composition middles. *)
Theorem model_qlift_bidual {A B} (T : A -> B -> Prop) t u
    (Ht : free_omega_modelable (@native) t) (Hu : free_omega_modelable (@native) u) :
  free_omega_qlift T t u ->
  oval_bidual T (free_omega_model Ht) (free_omega_model Hu).
Proof. exact: model_qlift_bidual_raw. Qed.

Theorem model_qlift_eq_modelable {A} (t u : FreeOmega MN A) :
  free_omega_qlift eq t u ->
  (free_omega_modelable (@native) t <-> free_omega_modelable (@native) u).
Proof.
  intro H; split; intro Hv; eapply modelable_ext; [exact Hv| |exact Hv|];
    intros f Hf; [exact (model_qlift_eq_upper H Hf)|symmetry; exact (model_qlift_eq_upper H Hf)].
Qed.

Theorem model_qlift_eq_sound {A} (t u : FreeOmega MN A)
    (Ht : free_omega_modelable (@native) t) (Hu : free_omega_modelable (@native) u) :
  free_omega_qlift eq t u -> oval_eq (free_omega_model Ht) (free_omega_model Hu).
Proof. intros H f Hf; exact (model_qlift_eq_upper H Hf). Qed.
End QuotientValidation.
