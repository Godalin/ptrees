Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect ssrnat eqtype.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift MeasureIteration.
From PTree.Eq Require Import PWeakAbstract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Omega frontiers extend finite frontiers with zero-mass truncation.  At
    fuel zero no returned or visible head has yet been observed.  Successor
    fuel exposes an immediate head, removes a tau, or integrates one layer of
    probabilistic branching. *)
Section OmegaFrontier.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M}
  `{MO : @MeasureOmegaInterface M MI} {R : Type}.

Inductive apfrontier_approx :
    nat -> ptree' E M R -> M (aphead E M R) -> Prop :=
  | APFAZero ot :
      apfrontier_approx 0 ot meas_zero
  | APFAReturn n r :
      apfrontier_approx n.+1 (RetF r) (meas_ret (APHRet r))
  | APFAVisible n {X} (e : E X) k :
      apfrontier_approx n.+1 (VisF e k) (meas_ret (APHVis e k))
  | APFATau n t hs :
      apfrontier_approx n (observe t) hs ->
      apfrontier_approx n.+1 (TauF t) hs
  | APFAProb n {X : eqType} (mu : M X) k
      (front : X -> M (aphead E M R)) (Good : X -> Prop) :
      meas_ae mu Good ->
      (forall x, Good x ->
        apfrontier_approx n (observe (k x)) (front x)) ->
      apfrontier_approx n.+1 (ProbF mu k) (meas_bind mu front).

Definition apomega_frontier
    (ot : ptree' E M R) (hs : M (aphead E M R)) : Prop :=
  exists chain : nat -> M (aphead E M R),
    (forall n, apfrontier_approx n ot (chain n)) /\
    meas_lub chain hs.

End OmegaFrontier.

(** Weak bisimulation over omega frontiers.  Internal divergence is handled
    by the zero/lub construction above; visible continuations remain guarded
    by the greatest fixed point. *)
Section OmegaWeak.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M}
  `{MC : @MeasureCoreLaws M MI}
  `{MO : @MeasureOmegaInterface M MI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Inductive apweak_omegaF
    (sim : ptree E M R1 -> ptree E M R2 -> Prop) :
    ptree' E M R1 -> ptree' E M R2 -> Prop :=
  | APWOFrontier ot1 ot2 hs1 hs2 :
      apomega_frontier ot1 hs1 ->
      apomega_frontier ot2 hs2 ->
      meas_lift (aphead_rel RR sim) hs1 hs2 ->
      apweak_omegaF sim ot1 ot2.

Lemma apweak_omegaF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall ot1 ot2,
    apweak_omegaF sim1 ot1 ot2 -> apweak_omegaF sim2 ot1 ot2.
Proof.
  move=> Hsim ot1 ot2 H; inversion H; subst.
  econstructor; [exact H0|exact H1|].
  eapply meas_lift_mono; [|exact H2].
  exact: aphead_rel_mono Hsim.
Qed.

Definition apweak_omega_body sim
    (t1 : ptree E M R1) (t2 : ptree E M R2) :=
  apweak_omegaF sim (observe t1) (observe t2).

Program Definition fapweak_omega :
    mon (ptree E M R1 -> ptree E M R2 -> Prop) :=
  {| body := apweak_omega_body |}.
Next Obligation.
  move=> sim1 sim2 Hsub t1 t2 H.
  eapply apweak_omegaF_monotone; [exact Hsub|exact H].
Qed.

Definition apweak_omega : ptree E M R1 -> ptree E M R2 -> Prop :=
  gfp fapweak_omega.

Lemma apweak_omega_unfold t1 t2 :
  apweak_omega t1 t2 ->
  apweak_omegaF apweak_omega (observe t1) (observe t2).
Proof.
  move=> H. apply (gfp_pfp fapweak_omega) in H. exact H.
Qed.

Lemma apweak_omega_fold t1 t2 :
  apweak_omegaF apweak_omega (observe t1) (observe t2) ->
  apweak_omega t1 t2.
Proof.
  move=> H. unfold apweak_omega. apply (gfp_fp fapweak_omega). exact H.
Qed.

End OmegaWeak.
