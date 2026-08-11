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
    fuel zero truncates a probabilistic node, while immediate heads and taus
    cost no probabilistic fuel.  A successor integrates exactly one layer of
    probabilistic branching.  This convention makes the approximation index
    coincide with [meas_iter_approx]. *)
Section OmegaFrontier.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M}
  `{MO : @MeasureOmegaInterface M MI} {R : Type}.

Inductive apfrontier_approx :
    nat -> ptree' E M R -> M (aphead E M R) -> Prop :=
  | APFAZero ot :
      apfrontier_approx 0 ot meas_zero
  | APFAReturn n r :
      apfrontier_approx n (RetF r) (meas_ret (APHRet r))
  | APFAVisible n {X} (e : E X) k :
      apfrontier_approx n (VisF e k) (meas_ret (APHVis e k))
  | APFATau n t hs :
      apfrontier_approx n (observe t) hs ->
      apfrontier_approx n (TauF t) hs
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

(** Head-valued absorbing approximation for a probabilistic loop whose step
    immediately returns its continue/finish decision. *)
Section IterOmegaFrontier.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M}
  `{MO : @MeasureOmegaInterface M MI} {R : eqType}.

Fixpoint ap_iter_head_approx {I A}
    (n : nat) (step : I -> M (I + A)) (i : I) :
    M (aphead E M A) :=
  match n with
  | 0 => meas_zero
  | n'.+1 =>
      meas_bind (step i) (fun next =>
        match next with
        | inl i' => ap_iter_head_approx n' step i'
        | inr a => meas_ret (APHRet a)
        end)
  end.

Definition ap_iter_tree {I A : eqType}
    (step : I -> M (I + A)) (i : I) :
    ptree E M A :=
  PTree.iter (fun j => Prob (step j) (fun next => Ret next)) i.

Lemma ap_iter_tree_approx
    `{MC : @MeasureCoreLaws M MI}
    `{ML : @MeasureLaws M MI MC}
    {I : eqType} n (step : I -> M (I + R)) i :
  apfrontier_approx n (observe (ap_iter_tree step i))
    (ap_iter_head_approx n step i).
Proof.
  elim: n i=> [|n IH] i.
  - exact: APFAZero.
  - cbn. apply: (APFAProb (Good := fun _ => True)).
    + exact: meas_ae_true.
    + move=> [i'|a] _ /=.
      * apply: APFATau. exact: IH.
      * exact: APFAReturn.
Qed.

Lemma ap_iter_tree_omega_frontier
    `{MC : @MeasureCoreLaws M MI}
    `{ML : @MeasureLaws M MI MC}
    {I : eqType} (step : I -> M (I + R)) i out :
  meas_lub (fun n => ap_iter_head_approx n step i) out ->
  apomega_frontier (observe (ap_iter_tree step i)) out.
Proof.
  move=> Hlub. exists (fun n => ap_iter_head_approx n step i).
  split; [move=> n; exact: ap_iter_tree_approx|exact Hlub].
Qed.

End IterOmegaFrontier.

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
