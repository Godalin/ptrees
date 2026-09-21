(** Role: Concentration and countable-carrier representation in the independent
    expectation domain. No FreeOmega, SemanticMeasure, or tree syntax. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals boolp.
From PTree.Prob.Domain Require Import Expectation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Countable.
Variable R : realType.

(** Concentration means that changing a bounded observable outside P does
    not change its expectation. This is a property, not an assumed capability. *)
Definition oval_ae {A} (L : OmegaVal R A) (P : A -> Prop) : Prop :=
  forall f g, oval_test f -> oval_test g ->
  (forall x, P x -> f x = g x) -> oval_eval L f = oval_eval L g.

Lemma oval_ae_mono {A} (L : OmegaVal R A) (P Q : A -> Prop) :
  oval_ae L P -> (forall x, P x -> Q x) -> oval_ae L Q.
Proof. intros H HPQ f g Hf Hg Hfg; apply H; auto. Qed.

Lemma oval_ae_le {A} (L : OmegaVal R A) P f g :
  oval_ae L P -> oval_test f -> oval_test g ->
  (forall x, P x -> f x <= g x) -> oval_eval L f <= oval_eval L g.
Proof.
  intros HP Hf Hg Hfg.
  pose h x := if pselect (P x) then f x else g x.
  have Hh : oval_test h.
  { intro x; unfold h; destruct (pselect (P x)); [apply Hf|apply Hg]. }
  have He : oval_eval L f = oval_eval L h.
  { apply HP; auto. intros x Hx; unfold h; destruct (pselect (P x)); [reflexivity|contradiction]. }
  rewrite He; apply (oval_mono (oval_laws L) Hh Hg)=> x.
  unfold h; destruct (pselect (P x)) as [Hx|Hx]; [exact (Hfg x Hx)|exact: lexx].
Qed.

Definition oval_enumerated {A} (e : nat -> option A) x := exists n, e n = Some x.
Definition oval_countably_supported {A} (L : OmegaVal R A) : Prop :=
  exists e : nat -> option A, oval_ae L (oval_enumerated e).

Definition oval_code {A} (e : nat -> option A) (x : A) : nat :=
  match pselect (oval_enumerated e x) with
  | left H => proj1_sig (cid H)
  | right _ => O
  end.

Lemma oval_code_spec {A} (e : nat -> option A) x :
  oval_enumerated e x -> e (oval_code e x) = Some x.
Proof.
  intro H; rewrite /oval_code; case: pselect=> [Hyes|Hno]; last contradiction.
  exact (proj2_sig (cid Hyes)).
Qed.

Definition oval_decode {A} (e : nat -> option A) n : OmegaVal R A :=
  match e n with Some x => oval_ret R x | None => oval_bottom R end.

(** A genuine representation over a countable carrier; the source A need
    not itself be countable, inhabited, or a MathComp carrier. *)
Theorem oval_countable_representation {A} (L : OmegaVal R A) e :
  oval_ae L (oval_enumerated e) ->
  exists N : OmegaVal R nat,
    oval_mass N = oval_mass L /\
    oval_ae N (fun n => exists x, e n = Some x) /\
    oval_eq L (oval_bind N (oval_decode e)).
Proof.
  intro H; exists (oval_bind L (fun x => oval_ret R (oval_code e x))).
  split; first reflexivity.
  split.
  - intros f g Hf Hg Hfg; apply H.
    + intro x; exact (Hf (oval_code e x)).
    + intro x; exact (Hg (oval_code e x)).
    + intros x Hx; apply Hfg; exists x; exact: oval_code_spec.
  - intros f Hf; apply H; first exact Hf.
    + intro x; exact (oval_eval_bounds (oval_decode e (oval_code e x)) Hf).
    + intros x Hx; change (f x = oval_eval (oval_decode e (oval_code e x)) f).
      rewrite /oval_decode (oval_code_spec Hx); reflexivity.
Qed.
End Countable.
