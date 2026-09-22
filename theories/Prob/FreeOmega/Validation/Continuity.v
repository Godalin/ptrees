(** Role: One-way external validation of raw FreeOmega evaluators.
    Continuity is in bounded tests, not a claim that arbitrary raw lubs
    are additive measures. No concrete backend or joint-existence law. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals boolp.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Domain Require Import Expectation Countable.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation.
From PTree.Prob.FreeOmega.Validation Require Import Expectation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Continuity.
Context {MN : Type -> Type} {R : realType}.
Variable native : forall X, MN X -> OmegaVal R X.
Arguments native {X} _.
Local Notation upper := (free_omega_model_upper (@native)).

Lemma model_upper_mono {A} (t : FreeOmega MN A) f g :
  oval_test f -> oval_test g -> (forall x, f x <= g x) -> upper t f <= upper t g.
Proof.
  intros Hf Hg Hfg; induction t as [x| |X mu k IH|c IH]; cbn [free_omega_model_upper].
  - exact (Hfg x).
  - exact: lexx.
  - apply (oval_mono (oval_laws (native mu))).
    + intro x; exact (model_upper_bounds (@native) (k x) Hf).
    + intro x; exact (model_upper_bounds (@native) (k x) Hg).
    + exact IH.
  - apply (oval_sup_mono (b := 1)); [|exact IH].
    intro n; exact (proj2 (model_upper_bounds (@native) (c n) Hg)).
Qed.

Theorem model_upper_continuous {A} (t : FreeOmega MN A) (f : nat -> A -> R) :
  (forall n, oval_test (f n)) -> (forall n x, f n x <= f (S n) x) ->
  upper t (oval_pointwise_sup f) = oval_sup (fun n => upper t (f n)).
Proof.
  intros Hf Hi; induction t as [x| |X mu k IH|c IH]; cbn [free_omega_model_upper].
  - reflexivity.
  - symmetry; exact: oval_sup_const.
  - rewrite (functional_extensionality _ _ IH).
    apply (oval_continuous (oval_laws (native mu))).
    + intros n x; exact (model_upper_bounds (@native) (k x) (Hf n)).
    + intros n x; exact (model_upper_mono (k x) (Hf n) (Hf (S n)) (Hi n)).
  - rewrite (functional_extensionality _ _ IH).
    apply (oval_sup_swap (b := 1))=> i n.
    exact (proj2 (model_upper_bounds (@native) (c i) (Hf n))).
Qed.

(** Null branches may be non-monotone. Totalize tests outside the good
    support, use ordinary OmegaVal continuity, then transport back by AE. *)
Lemma model_native_continuous_ae {X} (L : OmegaVal R X) P (f : nat -> X -> R) :
  oval_ae L P -> (forall n, oval_test (f n)) ->
  (forall x, P x -> forall n, f n x <= f (S n) x) ->
  oval_eval L (oval_pointwise_sup f) = oval_sup (fun n => oval_eval L (f n)).
Proof.
  intros HP Hf Hi.
  pose g n x := if pselect (P x) then f n x else 0.
  have Hg : forall n, oval_test (g n).
  { intros n x; rewrite /g; case: pselect=> Hx; [exact (Hf n x)|].
    split; [exact: lexx|exact: ler01]. }
  have Hgi : forall n x, g n x <= g (S n) x.
  { intros n x; rewrite /g; case: pselect=> Hx; [exact (Hi x Hx n)|exact: lexx]. }
  have He : forall n, oval_eval L (f n) = oval_eval L (g n).
  { intro n; apply (HP _ _ (Hf n) (Hg n)); intros x Hx.
    rewrite /g; by case: pselect. }
  transitivity (oval_eval L (oval_pointwise_sup g)).
  - apply HP; [exact (oval_test_sup Hf)|exact (oval_test_sup Hg)|].
    intros x Hx; apply oval_sup_ext=> n; rewrite /g; by case: pselect.
  - rewrite (oval_continuous (oval_laws L) Hg Hgi).
    apply oval_sup_ext=> n; symmetry; exact (He n).
Qed.

Section NativeLaws.
Context `{NI : SemanticMeasure MN}.
Hypothesis native_ae : forall X (mu : MN X) P, sem_ae mu P -> oval_ae (native mu) P.
Hypothesis native_lift : forall X Y (T : X -> Y -> Prop) (mu : MN X) (nu : MN Y) f g,
  sem_lift T mu nu -> oval_test f -> oval_test g ->
  (forall x y, T x y -> f x <= g y) -> oval_eval (native mu) f <= oval_eval (native nu) g.

Lemma model_approx_mono {A} (t u : FreeOmega MN A) f :
  free_omega_approx eq t u -> oval_test f -> upper t f <= upper u f.
Proof.
  intros H Hf; eapply model_upper_approx; [exact native_lift|exact H|exact Hf|exact Hf|].
  intros x y ->; exact: lexx.
Qed.

Theorem model_sample_lub {A X} (mu : MN X) (c : X -> nat -> FreeOmega MN A) f :
  sem_ae mu (fun x => forall n, free_omega_approx eq (c x n) (c x (S n))) ->
  oval_test f ->
  upper (FOSample mu (fun x => FOLub (c x))) f =
  upper (FOLub (fun n => FOSample mu (fun x => c x n))) f.
Proof.
  intros Hi Hf; apply (model_native_continuous_ae (native_ae Hi)).
  - intros n x; exact (model_upper_bounds (@native) (c x n) Hf).
  - intros x Hx n; exact (model_approx_mono (Hx n) Hf).
Qed.

Theorem model_diagonal_upper {A} (c : nat -> nat -> FreeOmega MN A) f :
  (forall i j, free_omega_approx eq (c i j) (c i (S j))) ->
  (forall i j, free_omega_approx eq (c i j) (c (S i) j)) ->
  oval_test f -> upper (FOLub (fun i => FOLub (c i))) f =
    upper (FOLub (fun n => c n n)) f.
Proof.
  intros Hr Hc Hf; apply model_upper_lub_diagonal; [| |exact Hf].
  - intros j i g Hg; exact (model_approx_mono (Hc i j) Hg).
  - intros i j g Hg; exact (model_approx_mono (Hr i j) Hg).
Qed.

Theorem model_bind_lub {A X} (s : nat -> FreeOmega MN X)
    (k : X -> nat -> FreeOmega MN A) f :
  (forall n, free_omega_approx eq (s n) (s (S n))) ->
  (forall x n, free_omega_approx eq (k x n) (k x (S n))) ->
  oval_test f ->
  upper (free_omega_bind (FOLub s) (fun x => FOLub (k x))) f =
  upper (FOLub (fun n => free_omega_bind (s n) (fun x => k x n))) f.
Proof.
  intros Hs Hk Hf.
  have Hrow : forall i, upper (free_omega_bind (s i) (fun x => FOLub (k x))) f =
      upper (FOLub (fun n => free_omega_bind (s i) (fun x => k x n))) f.
  { intro i; rewrite model_upper_bind; cbn [free_omega_model_upper].
    rewrite (model_upper_continuous (s i) (f := fun n x => upper (k x n) f)).
    - apply oval_sup_ext=> n; symmetry; exact: model_upper_bind.
    - intros n x; exact (model_upper_bounds (@native) (k x n) Hf).
    - intros n x; exact (model_approx_mono (Hk x n) Hf). }
  change (oval_sup (fun i => upper (free_omega_bind (s i) (fun x => FOLub (k x))) f) =
    upper (FOLub (fun n => free_omega_bind (s n) (fun x => k x n))) f).
  rewrite (functional_extensionality _ _ Hrow).
  apply model_upper_lub_diagonal; [| |exact Hf].
  - intros j i g Hg; rewrite !model_upper_bind.
    exact (model_approx_mono (Hs i) (fun x => model_upper_bounds (@native) (k x j) Hg)).
  - intros i j g Hg; rewrite !model_upper_bind.
    apply model_upper_mono.
    + intro x; exact (model_upper_bounds (@native) (k x j) Hg).
    + intro x; exact (model_upper_bounds (@native) (k x (S j)) Hg).
    + intro x; exact (model_approx_mono (Hk x j) Hg).
Qed.
End NativeLaws.
End Continuity.
