(** Role: One-way, native-parametric external validation. The mathematical
    target is the independent OmegaVal domain, NOT another free syntax.
    Arbitrary raw lubs have an upper evaluator, not automatically a measure.
    No native backend, PTree theory, or internal observation relation is used. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Logic Require Import FunctionalExtensionality.
From Coq Require Import Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals boolp.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Domain Require Import Expectation Countable.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Validation.
Context {MN : Type -> Type}.
Variable R : realType.
Variable native : forall X, MN X -> OmegaVal R X.
Arguments native {X} _.

Fixpoint free_omega_model_upper {A} (t : FreeOmega MN A) (f : A -> R) : R :=
  match t with
  | FORet x => f x
  | FOZero => 0
  | @FOSample _ _ X mu k => oval_eval (native mu) (fun x => free_omega_model_upper (k x) f)
  | FOLub c => oval_sup (fun n => free_omega_model_upper (c n) f)
  end.

Lemma model_upper_bounds {A} (t : FreeOmega MN A) f :
  oval_test f -> 0 <= free_omega_model_upper t f /\ free_omega_model_upper t f <= 1.
Proof.
  intro Hf; induction t as [x| |X mu k IH|c IH]; cbn [free_omega_model_upper].
  - exact (Hf x).
  - split; [exact: lexx|exact: ler01].
  - exact (oval_eval_bounds (native mu) IH).
  - split.
    + exact: le_trans (proj1 (IH 0%nat)) (oval_sup_ge 0%nat (fun n => proj2 (IH n))).
    + exact: oval_sup_le (fun n => proj2 (IH n)).
Qed.

Lemma model_upper_bind {A B} (t : FreeOmega MN A) (k : A -> FreeOmega MN B) f :
  free_omega_model_upper (free_omega_bind t k) f =
  free_omega_model_upper t (fun x => free_omega_model_upper (k x) f).
Proof.
  induction t as [x| |X mu h IH|c IH]; cbn [free_omega_bind free_omega_model_upper];
    try reflexivity; f_equal; apply functional_extensionality; exact IH.
Qed.

Definition free_omega_modelable {A} (t : FreeOmega MN A) : Prop :=
  OmegaValLaws (free_omega_model_upper t).
Definition free_omega_model {A} (t : FreeOmega MN A)
    (H : free_omega_modelable t) : OmegaVal R A :=
  {| oval_eval := free_omega_model_upper t; oval_laws := H |}.
Definition free_omega_model_denotes {A} (t : FreeOmega MN A) (L : OmegaVal R A) : Prop :=
  forall f, oval_test f -> free_omega_model_upper t f = oval_eval L f.

Theorem modelable_iff_denotes {A} (t : FreeOmega MN A) :
  free_omega_modelable t <-> exists L, free_omega_model_denotes t L.
Proof.
  split.
  - intro H; exists (free_omega_model H); intros f Hf; reflexivity.
  - intros [L H]; eapply oval_laws_ext; [exact (oval_laws L)|].
    intros f Hf; symmetry; exact (H f Hf).
Qed.
Theorem model_denotes_unique {A} (t : FreeOmega MN A) L M :
  free_omega_model_denotes t L -> free_omega_model_denotes t M -> oval_eq L M.
Proof. intros HL HM f Hf; rewrite -(HL f Hf); exact (HM f Hf). Qed.
Theorem model_denotes_proper {A} (t : FreeOmega MN A) L M :
  free_omega_model_denotes t L -> oval_eq L M -> free_omega_model_denotes t M.
Proof. intros HL HM f Hf; rewrite (HL f Hf); exact (HM f Hf). Qed.
Lemma modelable_ext {A} (t u : FreeOmega MN A) :
  free_omega_modelable t ->
  (forall f, oval_test f -> free_omega_model_upper t f = free_omega_model_upper u f) ->
  free_omega_modelable u.
Proof. exact: oval_laws_ext. Qed.
Lemma modelable_ret {A} (x : A) : free_omega_modelable (FORet x).
Proof. exact (oval_laws (oval_ret R x)). Qed.
Lemma modelable_zero {A} : free_omega_modelable (@FOZero MN A).
Proof. exact (oval_laws (@oval_bottom R A)). Qed.
Lemma modelable_sample {A X} (mu : MN X) (k : X -> FreeOmega MN A) :
  (forall x, free_omega_modelable (k x)) -> free_omega_modelable (FOSample mu k).
Proof.
  intro H; exact (oval_laws (oval_bind (native mu) (fun x => free_omega_model (H x)))).
Qed.
Definition model_chain_increasing {A} (c : nat -> FreeOmega MN A) :=
  forall n f, oval_test f -> free_omega_model_upper (c n) f <= free_omega_model_upper (c (S n)) f.
Lemma modelable_lub {A} (c : nat -> FreeOmega MN A)
    (H : forall n, free_omega_modelable (c n)) :
  model_chain_increasing c -> free_omega_modelable (FOLub c).
Proof. intro Hi; exact (oval_laws (oval_lub (c := fun n => free_omega_model (H n)) Hi)). Qed.
Lemma modelable_bind {A B} (t : FreeOmega MN A) (k : A -> FreeOmega MN B) :
  free_omega_modelable t -> (forall x, free_omega_modelable (k x)) ->
  free_omega_modelable (free_omega_bind t k).
Proof.
  intros H Hk; eapply oval_laws_ext.
  - exact (oval_laws (oval_bind (free_omega_model H) (fun x => free_omega_model (Hk x)))).
  - intros f Hf; symmetry; exact: model_upper_bind.
Qed.
Theorem model_denotes_bind {A B} (t : FreeOmega MN A) (k : A -> FreeOmega MN B) L K :
  free_omega_model_denotes t L -> (forall x, free_omega_model_denotes (k x) (K x)) ->
  free_omega_model_denotes (free_omega_bind t k) (oval_bind L K).
Proof.
  intros H Hk f Hf; rewrite model_upper_bind.
  have He : (fun x => free_omega_model_upper (k x) f) = (fun x => oval_eval (K x) f).
  { apply functional_extensionality=> x; exact (Hk x f Hf). }
  rewrite He; exact (H _ (fun x => oval_eval_bounds (K x) Hf)).
Qed.
Theorem model_denotes_lub {A} (c : nat -> FreeOmega MN A) L (Hi : oval_increasing L) :
  (forall n, free_omega_model_denotes (c n) (L n)) ->
  free_omega_model_denotes (FOLub c) (oval_lub Hi).
Proof. intros H f Hf; apply oval_sup_ext=> n; exact (H n f Hf). Qed.

(** Supremum interchange, not commutativity of arbitrary native sampling. *)
Theorem model_upper_lub_swap {A} (c : nat -> nat -> FreeOmega MN A) f :
  oval_test f ->
  free_omega_model_upper (FOLub (fun i => FOLub (c i))) f =
  free_omega_model_upper (FOLub (fun j => FOLub (fun i => c i j))) f.
Proof.
  intro Hf; apply (oval_sup_swap (b := 1))=> i j.
  exact (proj2 (model_upper_bounds (c i j) Hf)).
Qed.

Theorem model_upper_lub_diagonal {A} (c : nat -> nat -> FreeOmega MN A) :
  (forall j, model_chain_increasing (fun i => c i j)) ->
  (forall i, model_chain_increasing (c i)) ->
  forall f, oval_test f ->
  free_omega_model_upper (FOLub (fun i => FOLub (c i))) f =
  free_omega_model_upper (FOLub (fun n => c n n)) f.
Proof.
  intros Hleft Hright f Hf.
  have Hb : forall i j, free_omega_model_upper (c i j) f <= 1 :=
    fun i j => proj2 (model_upper_bounds (c i j) Hf).
  apply/eqP; rewrite eq_le; apply/andP; split.
  - apply oval_sup_le=> i; apply oval_sup_le=> j.
    apply: le_trans (_ : free_omega_model_upper (c (Nat.max i j) (Nat.max i j)) f <= _).
    + apply: le_trans (_ : free_omega_model_upper (c (Nat.max i j) j) f <= _).
      * exact (oval_increasing_le (fun n => Hleft j n f Hf) (Nat.le_max_l i j)).
      * exact (oval_increasing_le (fun n => Hright (Nat.max i j) n f Hf) (Nat.le_max_r i j)).
    + exact (oval_sup_ge (Nat.max i j) (fun n => Hb n n)).
  - apply oval_sup_le=> n.
    apply: le_trans (oval_sup_ge n (Hb n)) _.
    exact (oval_sup_ge n (fun i => oval_sup_le (Hb i))).
Qed.

(** Only this section needs a link to the native AE interface. It requires
    preservation of null sets, not native relational bind or native omega laws. *)
Section AE.
Context `{NI : SemanticMeasure MN}.
Hypothesis native_ae : forall X (mu : MN X) P, sem_ae mu P -> oval_ae (native mu) P.

Lemma model_upper_ae_ext {A} (t : FreeOmega MN A) f g :
  oval_test f -> oval_test g -> free_omega_ae (fun x => f x = g x) t ->
  free_omega_model_upper t f = free_omega_model_upper t g.
Proof.
  intros Hf Hg Ha; induction Ha; cbn [free_omega_model_upper].
  - exact H.
  - reflexivity.
  - apply (native_ae H).
    + intro x; exact (model_upper_bounds (k x) Hf).
    + intro x; exact (model_upper_bounds (k x) Hg).
    + exact H1.
  - apply oval_sup_ext; exact H0.
Qed.

Definition model_support_kernel {A} (t : FreeOmega MN A) :=
  if pselect (free_omega_modelable t) then t else FOZero.
Lemma model_support_kernel_valid {A} (t : FreeOmega MN A) :
  free_omega_modelable (model_support_kernel t).
Proof. rewrite /model_support_kernel; case: pselect=> H; [exact H|exact: modelable_zero]. Qed.
Lemma model_support_kernel_eq {A} (t : FreeOmega MN A) :
  free_omega_modelable t -> model_support_kernel t = t.
Proof. intro H; rewrite /model_support_kernel; case: pselect=> // Hn; contradiction. Qed.

Lemma model_ae_mono {A} (P Q : A -> Prop) t :
  (forall x, P x -> Q x) -> free_omega_ae P t -> free_omega_ae Q t.
Proof.
  intros HP H; induction H.
  - apply FOAERet; auto.
  - apply FOAEZero.
  - eapply FOAESample; eauto.
  - apply FOAELub; auto.
Qed.

Theorem modelable_bind_ae {A B} (t : FreeOmega MN A) (k : A -> FreeOmega MN B) :
  free_omega_modelable t -> free_omega_ae (fun x => free_omega_modelable (k x)) t ->
  free_omega_modelable (free_omega_bind t k).
Proof.
  intros H Hk; eapply modelable_ext
    with (t := free_omega_bind t (fun x => model_support_kernel (k x))).
  - apply (modelable_bind H)=> x; exact: model_support_kernel_valid.
  - intros f Hf; rewrite !model_upper_bind.
    apply model_upper_ae_ext.
    + intro x; exact (model_upper_bounds _ Hf).
    + intro x; exact (model_upper_bounds _ Hf).
    + eapply model_ae_mono; [|exact Hk].
      intros x Hx; by rewrite (model_support_kernel_eq Hx).
Qed.
Theorem modelable_sample_ae {A X} (mu : MN X) (k : X -> FreeOmega MN A) :
  sem_ae mu (fun x => free_omega_modelable (k x)) -> free_omega_modelable (FOSample mu k).
Proof.
  intro H; change (free_omega_modelable (free_omega_bind (FOSample mu (fun x => FORet x)) k)).
  apply modelable_bind_ae.
  - apply modelable_sample=> x; exact: modelable_ret.
  - eapply FOAESample; [exact H|]. intros x Hx; exact (FOAERet Hx).
Qed.
Theorem model_denotes_sample_ae {A X} (mu : MN X) (k : X -> FreeOmega MN A) K :
  sem_ae mu (fun x => free_omega_model_denotes (k x) (K x)) ->
  free_omega_model_denotes (FOSample mu k) (oval_bind (native mu) K).
Proof.
  intros H f Hf; apply (native_ae H).
  - intro x; exact (model_upper_bounds (k x) Hf).
  - intro x; exact (oval_eval_bounds (K x) Hf).
  - intros x Hx; exact (Hx f Hf).
Qed.
Theorem model_denotes_bind_ae {A B} (t : FreeOmega MN A) (k : A -> FreeOmega MN B) L K :
  free_omega_model_denotes t L ->
  free_omega_ae (fun x => free_omega_model_denotes (k x) (K x)) t ->
  free_omega_model_denotes (free_omega_bind t k) (oval_bind L K).
Proof.
  intros H Hk f Hf; rewrite model_upper_bind.
  change (free_omega_model_upper t (fun x => free_omega_model_upper (k x) f) =
    oval_eval L (fun x => oval_eval (K x) f)).
  rewrite -(H _ (fun x => oval_eval_bounds (K x) Hf)).
  apply model_upper_ae_ext.
  - intro x; exact (model_upper_bounds (k x) Hf).
  - intro x; exact (oval_eval_bounds (K x) Hf).
  - eapply model_ae_mono; [|exact Hk]. intros x Hx; exact (Hx f Hf).
Qed.
End AE.

Section Approximation.
Context `{NI : SemanticMeasure MN}.
Hypothesis native_lift : forall X Y (S : X -> Y -> Prop) (mu : MN X) (nu : MN Y) f g,
  sem_lift S mu nu -> oval_test f -> oval_test g ->
  (forall x y, S x y -> f x <= g y) -> oval_eval (native mu) f <= oval_eval (native nu) g.

Theorem model_upper_approx {A B} (S : A -> B -> Prop) (t : FreeOmega MN A) u f g :
  free_omega_approx S t u -> oval_test f -> oval_test g ->
  (forall x y, S x y -> f x <= g y) -> free_omega_model_upper t f <= free_omega_model_upper u g.
Proof.
  intros H Hf Hg Hfg; induction H; cbn [free_omega_model_upper].
  - exact (proj1 (model_upper_bounds nu Hg)).
  - exact (Hfg x y H).
  - eapply native_lift; [exact H| | |exact H1].
    + intro x; exact (model_upper_bounds (k x) Hf).
    + intro y; exact (model_upper_bounds (h y) Hg).
  - apply (oval_sup_mono (b := 1)); [intro n; exact (proj2 (model_upper_bounds (d n) Hg))|exact H0].
Qed.
Theorem modelable_lub_approx {A} (c : nat -> FreeOmega MN A) :
  (forall n, free_omega_modelable (c n)) ->
  (forall n, free_omega_approx eq (c n) (c (S n))) -> free_omega_modelable (FOLub c).
Proof.
  intros H Hi; apply (modelable_lub H)=> n f Hf.
  eapply model_upper_approx; [exact (Hi n)|exact Hf|exact Hf|].
  intros x y ->; exact: lexx.
Qed.

Theorem model_upper_cofinal {A} (c d : nat -> FreeOmega MN A) :
  free_omega_chains_cofinal eq c d ->
  forall f, oval_test f -> free_omega_model_upper (FOLub c) f = free_omega_model_upper (FOLub d) f.
Proof.
  intros [Hcd Hdc] f Hf; apply/eqP; rewrite eq_le; apply/andP; split;
    apply oval_sup_le=> n.
  - destruct (Hcd n) as [m Hm].
    apply: le_trans (_ : free_omega_model_upper (d m) f <= _).
    + eapply model_upper_approx; [exact Hm|exact Hf|exact Hf|]. intros x y ->; exact: lexx.
    + exact (oval_sup_ge m (fun i => proj2 (model_upper_bounds (d i) Hf))).
  - destruct (Hdc n) as [m Hm].
    apply: le_trans (_ : free_omega_model_upper (c m) f <= _).
    + eapply model_upper_approx; [exact Hm|exact Hf|exact Hf|]. intros x y <-; exact: lexx.
    + exact (oval_sup_ge m (fun i => proj2 (model_upper_bounds (c i) Hf))).
Qed.
End Approximation.
End Validation.
