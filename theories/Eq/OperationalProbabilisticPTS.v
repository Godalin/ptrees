Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import UnifiedFrontier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Targets of the genuinely operational state-to-distribution kernel.
    Stable observations stop the internal computation; internal targets are
    PTree states from which the kernel can take another step. *)
Polymorphic Variant operational_target
    (E : Type -> Type) (MN : Type -> Type) (R : Type) : Type :=
  | OPStable (h : frontier_head E MN R)
  | OPInternal (t : ptree E MN R).

Arguments OPStable {E MN R} _.
Arguments OPInternal {E MN R} _.

Section OperationalKernel.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

(** One primitive PTree step, interpreted directly as a behavior-layer
    distribution.  The only syntax inspection in the operational semantics
    is here.  In particular, no rule recognizes [PTree.iter], [PTree.bind],
    or nested iteration. *)
Definition operational_kernel {R} (ot : ptree' E MN R) :
    MF (operational_target E MN R) :=
  match ot with
  | RetF r => sem_ret (OPStable (FHRet r))
  | VisF _ e k => sem_ret (OPStable (FHVis e k))
  | TauF t => sem_ret (OPInternal t)
  | ProbF _ mu k =>
      mixed_bind mu (fun x => sem_ret (OPInternal (k x)))
  end.

(** Resolve one operational target using at most [fuel] further primitive
    steps.  Unresolved internal mass goes to [sem_zero]. *)
Fixpoint operational_target_approx {R} (fuel : nat)
    (target : operational_target E MN R) :
    MF (frontier_head E MN R) :=
  match target with
  | OPStable h => sem_ret h
  | OPInternal t =>
      match fuel with
      | O => sem_zero
      | Datatypes.S fuel' =>
          sem_bind (operational_kernel (observe t))
            (operational_target_approx fuel')
      end
  end.

(** The [fuel]-bounded stable-hitting distribution of an observed state.
    Fuel counts primitive internal transitions.  Ret and Vis are stable after
    their one primitive observation step; Tau and Prob recursively spend the
    remaining fuel through the same kernel. *)
Definition operational_hitting_approx {R} (fuel : nat)
    (ot : ptree' E MN R) : MF (frontier_head E MN R) :=
  sem_bind (operational_kernel ot) (operational_target_approx fuel).

(** AST weak behavior is now stated solely as the total omega limit of the
    generic primitive-step hitting chain.  Unlike the old operational
    presentation, this definition has no Iter/Bind/NestedIter constructors. *)
Definition operational_ast_weak {R} (ot : ptree' E MN R)
    (out : MF (frontier_head E MN R)) : Prop :=
  sem_lub (fun fuel => operational_hitting_approx fuel ot) out /\
  sem_total out.

Lemma operational_kernel_retE {R} (r : R) :
  operational_kernel (RetF r) =
  sem_ret (OPStable (FHRet r)).
Proof. reflexivity. Qed.

Lemma operational_kernel_visE {R X} (e : E X)
    (k : X -> ptree E MN R) :
  operational_kernel (VisF e k) =
  sem_ret (OPStable (FHVis e k)).
Proof. reflexivity. Qed.

Lemma operational_kernel_tauE {R} (t : ptree E MN R) :
  operational_kernel (TauF t) = sem_ret (OPInternal t).
Proof. reflexivity. Qed.

Lemma operational_kernel_probE {R X} (mu : MN X)
    (k : X -> ptree E MN R) :
  operational_kernel (ProbF mu k) =
  mixed_bind mu (fun x => sem_ret (OPInternal (k x))).
Proof. reflexivity. Qed.

Lemma operational_target_stableE {R} fuel
    (h : frontier_head E MN R) :
  operational_target_approx fuel (OPStable h) = sem_ret h.
Proof. destruct fuel; reflexivity. Qed.

Lemma operational_target_internal_zeroE {R} (t : ptree E MN R) :
  operational_target_approx O (OPInternal t) = sem_zero.
Proof. reflexivity. Qed.

Lemma operational_target_internal_succE {R} fuel
    (t : ptree E MN R) :
  operational_target_approx (Datatypes.S fuel)
    (OPInternal t) =
  sem_bind (operational_kernel (observe t))
    (operational_target_approx fuel).
Proof. reflexivity. Qed.

End OperationalKernel.

Section OperationalKernelLaws.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}.

(** These equations are derived from the single operational kernel.  They
    are not constructors of the weak semantics. *)
Lemma operational_hitting_ret {R} fuel (r : R) :
  sem_eq (operational_hitting_approx (MF := MF) fuel (RetF r))
    (sem_ret (FHRet r : frontier_head E MN R)).
Proof.
  unfold operational_hitting_approx. rewrite operational_kernel_retE.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite operational_target_stableE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_vis {R X} fuel (e : E X)
    (k : X -> ptree E MN R) :
  sem_eq (operational_hitting_approx (MF := MF) fuel (VisF e k))
    (sem_ret (FHVis e k : frontier_head E MN R)).
Proof.
  unfold operational_hitting_approx. rewrite operational_kernel_visE.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite operational_target_stableE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_tau_zero {R} (t : ptree E MN R) :
  sem_eq (operational_hitting_approx (MF := MF) O (TauF t)) sem_zero.
Proof.
  unfold operational_hitting_approx. rewrite operational_kernel_tauE.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite operational_target_internal_zeroE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_tau_succ {R} fuel (t : ptree E MN R) :
  sem_eq
    (operational_hitting_approx (MF := MF) (Datatypes.S fuel) (TauF t))
    (operational_hitting_approx fuel (observe t)).
Proof.
  unfold operational_hitting_approx at 1. rewrite operational_kernel_tauE.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite operational_target_internal_succE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_prob {R X} fuel (mu : MN X)
    (k : X -> ptree E MN R) :
  sem_eq (operational_hitting_approx (MF := MF) fuel (ProbF mu k))
    (mixed_bind mu (fun x =>
      operational_target_approx fuel (OPInternal (k x)))).
Proof.
  unfold operational_hitting_approx. rewrite operational_kernel_probE.
  eapply sem_eq_trans.
  - apply mixed_bind_assoc.
  - apply mixed_bind_ae_proper.
    eapply sem_ae_mono; [|apply sem_ae_true].
    intros x _. apply sem_bind_ret_l.
Qed.

Lemma operational_hitting_prob_zero {R X} (mu : MN X)
    (k : X -> ptree E MN R) :
  sem_eq (operational_hitting_approx (MF := MF) O (ProbF mu k))
    (mixed_bind mu (fun _ => sem_zero)).
Proof.
  eapply sem_eq_trans; [apply operational_hitting_prob|].
  apply mixed_bind_ae_proper.
  eapply sem_ae_mono; [|apply sem_ae_true].
  intros x _. rewrite operational_target_internal_zeroE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_prob_succ {R X} fuel (mu : MN X)
    (k : X -> ptree E MN R) :
  sem_eq
    (operational_hitting_approx (MF := MF) (Datatypes.S fuel) (ProbF mu k))
    (mixed_bind mu (fun x =>
      operational_hitting_approx fuel (observe (k x)))).
Proof.
  eapply sem_eq_trans; [apply operational_hitting_prob|].
  apply mixed_bind_ae_proper.
  eapply sem_ae_mono; [|apply sem_ae_true].
  intros x _. rewrite operational_target_internal_succE. apply sem_eq_refl.
Qed.

End OperationalKernelLaws.
