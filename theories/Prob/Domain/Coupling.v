(** Role: External joint-coupling specification and its dual consequences.
    The joint is an OmegaVal on the actual product carrier, not a new free
    representation. General dual-to-joint existence is NOT assumed here. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals boolp.
From PTree.Prob.Domain Require Import Expectation Countable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Coupling.
Variable R : realType.

Definition oval_dual {A B} (T : A -> B -> Prop) (L : OmegaVal R A) (M : OmegaVal R B) :=
  forall f g, oval_test f -> oval_test g ->
    (forall x y, T x y -> f x <= g y) -> oval_eval L f <= oval_eval M g.

Definition oval_bidual {A B} (T : A -> B -> Prop) (L : OmegaVal R A) (M : OmegaVal R B) :=
  oval_dual T L M /\ oval_dual (fun y x => T x y) M L.

Definition oval_joint {A B} (T : A -> B -> Prop) (L : OmegaVal R A) (M : OmegaVal R B)
    (J : OmegaVal R (A * B)) : Prop :=
  (forall f, oval_test f -> oval_eval J (fun z => f (fst z)) = oval_eval L f) /\
  (forall g, oval_test g -> oval_eval J (fun z => g (snd z)) = oval_eval M g) /\
  oval_ae J (fun z => T (fst z) (snd z)).

Definition oval_coupled {A B} (T : A -> B -> Prop) (L : OmegaVal R A) (M : OmegaVal R B) :=
  exists J, oval_joint T L M J.

Lemma oval_joint_dual {A B} (T : A -> B -> Prop) L M J :
  oval_joint T L M J -> oval_bidual T L M.
Proof.
  intros [Hl [Hr HS]]; split; intros f g Hf Hg Hfg.
  - rewrite -(Hl f Hf) -(Hr g Hg); apply (oval_ae_le HS).
    + intro z; exact (Hf (fst z)).
    + intro z; exact (Hg (snd z)).
    + intros [x y] Hxy; exact (Hfg x y Hxy).
  - rewrite -(Hr f Hf) -(Hl g Hg); apply (oval_ae_le HS).
    + intro z; exact (Hf (snd z)).
    + intro z; exact (Hg (fst z)).
    + intros [x y] Hxy; exact (Hfg y x Hxy).
Qed.

Lemma oval_bidual_mass {A B} (T : A -> B -> Prop) L M :
  oval_bidual T L M -> oval_mass L = oval_mass M.
Proof.
  intros [Hl Hr]; apply/eqP; rewrite eq_le; apply/andP; split.
  - apply Hl; [exact: oval_test_one|exact: oval_test_one|intros; exact: lexx].
  - apply Hr; [exact: oval_test_one|exact: oval_test_one|intros; exact: lexx].
Qed.

Definition oval_indicator {A} (P : A -> Prop) x : R := if pselect (P x) then 1 else 0.
Lemma oval_indicator_test {A} (P : A -> Prop) : oval_test (oval_indicator P).
Proof. intro x; unfold oval_indicator; destruct (pselect (P x)); split; [exact: ler01|exact: lexx|exact: lexx|exact: ler01]. Qed.

(** Under DS1b this is exactly zero measure of the complement of T. *)
Theorem oval_joint_off_relation_zero {A B} (T : A -> B -> Prop) L M J :
  oval_joint T L M J ->
  oval_eval J (oval_indicator (fun z => ~ T (fst z) (snd z))) = 0.
Proof.
  intros [_ [_ HS]]; rewrite -(oval_zero (oval_laws J)).
  apply HS; [apply oval_indicator_test|apply oval_test_zero|].
  intros [x y] Hxy; unfold oval_indicator; cbn [fst snd]; destruct (pselect (~ T x y));
    [contradiction|reflexivity].
Qed.

Definition oval_rel_image {A B} (T : A -> B -> Prop) (P : A -> Prop) y :=
  exists x, P x /\ T x y.

(** The full setwise Hall inequality, not merely a finite-support condition. *)
Theorem oval_dual_hall {A B} (T : A -> B -> Prop) L M :
  oval_dual T L M -> forall P,
  oval_eval L (oval_indicator P) <= oval_eval M (oval_indicator (oval_rel_image T P)).
Proof.
  intros H P; apply H; [apply oval_indicator_test|apply oval_indicator_test|].
  intros x y Hxy; rewrite /oval_indicator.
  destruct (pselect (P x)) as [Hx|Hx];
    destruct (pselect (oval_rel_image T P y)) as [Hy|Hy]; try exact: ler01; try exact: lexx.
  exfalso; apply Hy; exists x; split; assumption.
Qed.

Theorem oval_bidual_eq {A} (L M : OmegaVal R A) :
  oval_bidual eq L M -> oval_eq L M.
Proof.
  intros [Hl Hr] f Hf; apply/eqP; rewrite eq_le; apply/andP; split.
  - apply Hl; auto. intros x y ->; exact: lexx.
  - apply Hr; auto. intros x y <-; exact: lexx.
Qed.

(** Equality has an explicit diagonal joint, with no existence theorem for
    general relations hidden in a capability or constructor. *)
Theorem oval_eq_joint {A} (L M : OmegaVal R A) : oval_eq L M ->
  oval_joint eq L M (oval_bind L (fun x => oval_ret R (x,x))).
Proof.
  intro H; split; first by intros.
  split; first exact H.
  intros f g Hf Hg Hfg.
  change (oval_eval L (fun x => f (x,x)) = oval_eval L (fun x => g (x,x))).
  apply oval_eval_ext=> x; apply Hfg; reflexivity.
Qed.

Theorem oval_eq_coupled_iff {A} (L M : OmegaVal R A) :
  oval_coupled eq L M <-> oval_eq L M.
Proof.
  split.
  - intros [J H]; apply oval_bidual_eq; exact (oval_joint_dual H).
  - intro H; eexists; exact (oval_eq_joint H).
Qed.
End Coupling.
