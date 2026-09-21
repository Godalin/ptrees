(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Automatic Proposition Inductives.
From Coq.Program Require Import Equality.
From mathcomp Require Import ssralg ssrnum rat.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.Backend Require Import TwoLevelMeasureEnum.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Prob.Backend Require Import DiscreteMC RatSubTypes.
From PTree.Prob.Interface Require Import SemanticCoupling.
From PTree.Prob.Backend.FreeOmega Require Import FreeOmegaCouplingEnum.
From PTree.Eq.Internal Require Import FiniteInternal FiniteInternalJoint.
From PTree.Eq Require Import PStrong UnifiedFrontier PTreeKernel.
From PTree.Examples Require Import RandomWalk.
Import Enum.
Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PairedCompression.
Variant event : Type -> Type := .
Local Notation tree := (ptree event Enum bool).
Local Notation MF := (FreeOmega Enum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega)).
Local Notation execute := (@finite_internal event Enum MF FI FreeOmegaMixedMeasure bool).

Definition done : tree := Ret true.
Definition delayed : tree := Tau done.
Definition source : tree := Tau delayed.
Definition partner (b : bool) : tree := if b then done else delayed.

Inductive candidate : tree -> tree -> Prop :=
| candidate_source b : candidate source (partner b)
| candidate_done : candidate done done.

Definition mu : MF tree := FOSample rw_coin_raw (fun _ => FORet source).
Definition nu : MF tree := FOSample rw_coin_raw (fun b => FORet (partner b)).
Definition joint : MF (tree * tree) :=
  FOSample rw_coin_raw (fun b => FORet (source, partner b)).

Lemma joint_spec : @semantic_coupling MF FI _ _ candidate mu nu joint.
Proof.
  split.
  - apply FOQLSample with (T := eq).
    + apply sem_lift_refl. intro b. reflexivity.
    + intros x y ->. apply FOQLStructural. constructor. reflexivity.
  - split.
    + apply FOQLSample with (T := eq).
      * apply sem_lift_refl. intro b. reflexivity.
      * intros x y ->. apply FOQLStructural. constructor. reflexivity.
    + apply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros b _. constructor. apply candidate_source.
Qed.

(** The SAME left tree takes two Tau steps for the first partner and one
    for the second.  Both choices are finite_internal certificates, but
    their correlated marginal is a mixture, not a unary deterministic cut. *)
Definition left_cut (p : tree * tree) : MF tree := FORet (snd p).
Definition right_cut (p : tree * tree) : MF tree := FORet (snd p).

Lemma left_cut_valid t u : candidate t u -> execute t (left_cut (t,u)).
Proof.
  intro H. destruct H as [b|].
  - destruct b.
    + apply FITau, FITau.
      exact (@FIStop event Enum MF FI FreeOmegaMixedMeasure bool done).
    + apply FITau.
      exact (@FIStop event Enum MF FI FreeOmegaMixedMeasure bool delayed).
  - exact (@FIStop event Enum MF FI FreeOmegaMixedMeasure bool done).
Qed.

Lemma right_cut_valid t u : candidate t u -> execute u (right_cut (t,u)).
Proof. intros _. exact (@FIStop event Enum MF FI FreeOmegaMixedMeasure bool u). Qed.

Lemma partner_guarded t u : candidate t u -> (fun t u => pstrongF eq candidate (observe t) (observe u)) u u.
Proof.
  intro H. cbn beta. destruct H as [b|].
  - destruct b.
    + apply PSRet. reflexivity.
    + apply PSTau. apply candidate_done.
  - apply PSRet. reflexivity.
Qed.

Lemma cuts_guarded t u : candidate t u ->
  free_omega_qlift (fun t u => pstrongF eq candidate (observe t) (observe u))
    (left_cut (t,u)) (right_cut (t,u)).
Proof.
  intro H. apply FOQLStructural, FOLRet. exact (partner_guarded H).
Qed.

Theorem paired_residuals_guarded :
  free_omega_qlift (fun t u => pstrongF eq candidate (observe t) (observe u))
    (free_omega_bind joint left_cut) (free_omega_bind joint right_cut).
Proof.
  exact (finite_internal_joint_guarded
    (FI := FI) joint_spec cuts_guarded).
Qed.

Definition residual_joint (p : tree * tree) : MF (tree * tree) :=
  FORet (snd p, snd p).

Theorem paired_residual_joint_spec :
  @semantic_coupling MF FI _ _ (fun t u => pstrongF eq candidate (observe t) (observe u))
    (free_omega_bind joint left_cut) (free_omega_bind joint right_cut)
    (free_omega_bind joint residual_joint).
Proof.
  eapply (semantic_coupling_bind_dependent (MI := FI)); [exact joint_spec|].
  intros t u Htu. split.
  - apply FOQLStructural, FOLRet. reflexivity.
  - split.
    + apply FOQLStructural, FOLRet. reflexivity.
    + apply FOAERet. exact (partner_guarded Htu).
Qed.

(** In the structural case, the joint needed by correlated execution is
    now extracted from the coupling proof, rather than supplied by hand. *)
Theorem paired_residual_joint_exists :
  exists out, @semantic_coupling MF FI _ _ (fun t u => pstrongF eq candidate (observe t) (observe u))
    (free_omega_bind joint left_cut) (free_omega_bind joint right_cut) out.
Proof.
  apply free_enum_structural_coupling_realization.
  apply FOLSample with (S := eq).
  - apply sem_lift_refl. intro b. reflexivity.
  - intros x y ->. apply FOLRet.
    exact (partner_guarded (candidate_source y)).
Qed.

Lemma deterministic_prefix_cannot_sample n (r : bool) out :
  execute (tau_prefix n (Ret r)) out -> exists t, out = FORet t.
Proof.
  induction n as [|n IH] in out |- *; intro H.
  - exists (Ret r).
    exact (@finite_internal_ret_inv event Enum MF FI FreeOmegaMixedMeasure bool r out H).
  - cbn [tau_prefix] in H. dependent destruction H.
    + eexists. reflexivity.
    + apply IH. exact H.
Qed.

Theorem correlated_left_cut_is_not_unary :
  ~ execute source (free_omega_bind joint left_cut).
Proof.
  intro H.
  change (execute (tau_prefix 2 (Ret true))
    (FOSample rw_coin_raw (fun b => FORet (partner b)))) in H.
  destruct (deterministic_prefix_cannot_sample H) as [t Ht]. discriminate Ht.
Qed.

Lemma correlated_left_support (P : tree -> Prop) :
  free_omega_ae P (free_omega_bind joint left_cut) -> P done /\ P delayed.
Proof.
  intro Hae. dependent destruction Hae.
  assert (Htrue : Good true).
  { apply (H rw_down_weight true).
    - left. reflexivity.
    - intro Hz. apply (f_equal Qval) in Hz.
      change ((2 / 3 : rat) = 0) in Hz. vm_compute in Hz. discriminate. }
  assert (Hfalse : Good false).
  { apply (H rw_up_weight false).
    - right. left. reflexivity.
    - intro Hz. apply (f_equal Qval) in Hz.
      change ((1 / 3 : rat) = 0) in Hz. vm_compute in Hz. discriminate. }
  split.
  - pose proof (H0 true Htrue) as Hp. inversion Hp. assumption.
  - pose proof (H0 false Hfalse) as Hp. inversion Hp. assumption.
Qed.

(** The mismatch is not just a choice of representation: even equality
    coupling cannot turn the two-residual marginal into a unary cut.  This
    does not claim that the same program pair has no other sound policy. *)
Theorem correlated_left_cut_has_no_unary_realization :
  ~ exists out, execute source out /\
    free_omega_qlift eq (free_omega_bind joint left_cut) out.
Proof.
  intros [out [Hcut Hlift]].
  change (execute (tau_prefix 2 (Ret true)) out) in Hcut.
  destruct (deterministic_prefix_cannot_sample Hcut) as [t ->].
  pose proof (free_omega_qlift_support Hlift) as [_ Hback].
  assert (Hret : free_omega_ae (fun u : tree => u = t) (@FORet Enum tree t)).
  { constructor. reflexivity. }
  specialize (Hback _ Hret).
  assert (Hae : free_omega_ae (fun u => u = t) (free_omega_bind joint left_cut)).
  { eapply free_omega_ae_mono; [|exact Hback].
    intros x [y [-> ->]]. reflexivity. }
  destruct (correlated_left_support Hae) as [Hd Hdelay].
  assert (done = delayed) by congruence. discriminate.
Qed.

Theorem paired_compression_preserves_left_hitting
    (front : tree -> MF (stable_head event Enum bool))
    (Hfront : forall t, @ptree_stable_hitting event Enum MF FI
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool
      (observe t) (front t)) :
  free_omega_qlift eq
    (free_omega_bind (free_omega_bind joint left_cut) front)
    (free_omega_bind mu front).
Proof.
  exact (finite_internal_joint_hitting_left
    (FI := FI) joint_spec left_cut_valid Hfront).
Qed.

End PairedCompression.
