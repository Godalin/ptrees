Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Program.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import UnifiedFrontier UnifiedPWeak.

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

(** A generic weak behavior is the (possibly subprobabilistic) stable-hitting
    limit of primitive execution.  Unresolved mass is absent from each finite
    approximant, hence pure divergence has the zero subdistribution as its
    hitting limit. *)
Definition operational_weak {R} (ot : ptree' E MN R)
    (out : MF (frontier_head E MN R)) : Prop :=
  sem_lub (fun fuel => operational_hitting_approx fuel ot) out.

(** AST is a separate property of a weak behavior: its stable-hitting limit
    has total mass.  Keeping these notions separate is necessary because an
    ordinary finite frontier may legitimately be a subprobability measure. *)
Definition operational_ast_weak {R} (ot : ptree' E MN R)
    (out : MF (frontier_head E MN R)) : Prop :=
  operational_weak ot out /\ sem_total out.

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

Section OperationalHittingOrder.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}.

Lemma operational_target_approx_increasing {R} fuel
    (target : operational_target E MN R) :
  sem_le
    (operational_target_approx (MF := MF) fuel target)
    (operational_target_approx (Datatypes.S fuel) target).
Proof.
  induction fuel as [|fuel IH] in target |- *; destruct target as [h|t].
  - apply sem_le_refl.
  - apply sem_zero_le.
  - apply sem_le_refl.
  - apply sem_bind_le_k. exact IH.
Qed.

Theorem operational_hitting_increasing {R} (ot : ptree' E MN R) :
  sem_increasing
    (fun fuel => operational_hitting_approx (MF := MF) fuel ot).
Proof.
  intros fuel. unfold operational_hitting_approx.
  apply sem_bind_le_k. intros target.
  exact (operational_target_approx_increasing fuel target).
Qed.

Theorem operational_hitting_mono {R} (ot : ptree' E MN R) n m :
  Peano.le n m ->
  sem_le (operational_hitting_approx (MF := MF) n ot)
    (operational_hitting_approx (MF := MF) m ot).
Proof.
  intro Hnm. induction Hnm.
  - apply sem_le_refl.
  - eapply sem_le_trans; [exact IHHnm|].
    apply operational_hitting_increasing.
Qed.

End OperationalHittingOrder.

Section OperationalWeakExistence.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}.

Theorem operational_weak_exists {R} (ot : ptree' E MN R) :
  exists out, operational_weak (MF := MF) ot out.
Proof.
  unfold operational_weak. apply sem_lub_exists.
  exact (operational_hitting_increasing ot).
Qed.

Theorem operational_weak_unique {R} (ot : ptree' E MN R) out1 out2 :
  operational_weak (MF := MF) ot out1 ->
  operational_weak (MF := MF) ot out2 ->
  sem_eq out1 out2.
Proof.
  unfold operational_weak. intros H1 H2.
  eapply sem_lub_unique; eassumption.
Qed.

End OperationalWeakExistence.

Section OperationalStableSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}.

Theorem operational_weak_ret {R} (r : R) :
  operational_weak (MF := MF) (RetF r)
    (sem_ret (FHRet r : frontier_head E MN R)).
Proof.
  unfold operational_weak. eapply sem_lub_chain_proper.
  - intro n. apply sem_eq_sym. apply operational_hitting_ret.
  - apply sem_lub_constant.
Qed.

Theorem operational_weak_vis {R X} (e : E X)
    (k : X -> ptree E MN R) :
  operational_weak (MF := MF) (VisF e k)
    (sem_ret (FHVis e k : frontier_head E MN R)).
Proof.
  unfold operational_weak. eapply sem_lub_chain_proper.
  - intro n. apply sem_eq_sym. apply operational_hitting_vis.
  - apply sem_lub_constant.
Qed.

End OperationalStableSoundness.

Section OperationalTauSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}.

Lemma operational_hitting_tau_zero_prefix {R}
    (t : ptree E MN R) fuel :
  sem_eq
    (operational_hitting_approx (MF := MF) fuel (TauF t))
    (sem_zero_prefix
      (fun n => operational_hitting_approx (MF := MF) n (observe t))
      fuel).
Proof.
  destruct fuel as [|fuel].
  - apply operational_hitting_tau_zero.
  - apply operational_hitting_tau_succ.
Qed.

(** A silent primitive step changes only the finite indexing of the hitting
    chain.  Cofinality, rather than a Tau-specific weak constructor, is what
    makes its unbounded behavior invariant. *)
Theorem operational_weak_tau_iff {R} (t : ptree E MN R) out :
  operational_weak (MF := MF) (TauF t) out <->
  operational_weak (MF := MF) (observe t) out.
Proof.
  unfold operational_weak. split; intro Hlim.
  - apply (proj2 (sem_lub_zero_prefix
      (fun n => operational_hitting_approx (MF := MF) n (observe t)) out)).
    eapply sem_lub_chain_proper; [|exact Hlim].
    intro n. apply operational_hitting_tau_zero_prefix.
  - eapply sem_lub_chain_proper.
    + intro n. apply sem_eq_sym.
      apply operational_hitting_tau_zero_prefix.
    + apply (proj1 (sem_lub_zero_prefix
        (fun n => operational_hitting_approx (MF := MF) n (observe t)) out)).
      exact Hlim.
Qed.

Corollary operational_ast_weak_tau_iff {R} (t : ptree E MN R) out :
  operational_ast_weak (MF := MF) (TauF t) out <->
  operational_ast_weak (MF := MF) (observe t) out.
Proof.
  unfold operational_ast_weak. rewrite operational_weak_tau_iff.
  reflexivity.
Qed.

End OperationalTauSoundness.

Section OperationalProbSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.

Lemma operational_hitting_prob_zero_prefix {R X}
    (mu : MN X) (k : X -> ptree E MN R) fuel :
  sem_eq
    (operational_hitting_approx (MF := MF) fuel (ProbF mu k))
    (sem_zero_prefix
      (fun n => mixed_bind mu (fun x =>
        operational_hitting_approx (MF := MF) n (observe (k x))))
      fuel).
Proof.
  destruct fuel as [|fuel].
  - cbn [sem_zero_prefix]. eapply sem_eq_trans.
    + apply operational_hitting_prob_zero.
    + apply mixed_bind_zero.
  - cbn [sem_zero_prefix]. apply operational_hitting_prob_succ.
Qed.

(** Primitive probabilistic sampling commutes with unbounded stable hitting
    exactly under the mixed monotone-convergence capability. *)
Theorem operational_weak_prob {R X}
    (mu : MN X) (k : X -> ptree E MN R)
    (front : X -> MF (frontier_head E MN R)) (Good : X -> Prop) :
  sem_ae mu Good ->
  (forall x, Good x -> operational_weak (MF := MF) (observe (k x)) (front x)) ->
  operational_weak (MF := MF) (ProbF mu k) (mixed_bind mu front).
Proof.
  intros Hae Hbranch. unfold operational_weak in Hbranch |- *.
  eapply sem_lub_chain_proper.
  - intro n. apply sem_eq_sym.
    apply operational_hitting_prob_zero_prefix.
  - apply (proj1 (sem_lub_zero_prefix
      (fun n => mixed_bind mu (fun x =>
        operational_hitting_approx (MF := MF) n (observe (k x))))
      (mixed_bind mu front))).
    eapply mixed_bind_lub; [exact Hae| |exact Hbranch].
    intros x _. apply operational_hitting_increasing.
Qed.

Corollary operational_ast_weak_prob {R X}
    (mu : MN X) (k : X -> ptree E MN R)
    (front : X -> MF (frontier_head E MN R)) (Good : X -> Prop) :
  sem_ae mu Good ->
  (forall x, Good x ->
    operational_ast_weak (MF := MF) (observe (k x)) (front x)) ->
  sem_total (mixed_bind mu front) ->
  operational_ast_weak (MF := MF) (ProbF mu k) (mixed_bind mu front).
Proof.
  intros Hae Hbranch Htotal. split; [|exact Htotal].
  eapply operational_weak_prob; [exact Hae|].
  intros x Hx. exact (proj1 (Hbranch x Hx)).
Qed.

End OperationalProbSoundness.

Section OperationalBindDiagonal.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

Definition operational_head_bind_approx {A R} (fuel : nat)
    (k : A -> ptree E MN R) (h : frontier_head E MN A) :
    MF (frontier_head E MN R) :=
  match h with
  | FHRet a => operational_hitting_approx (MF := MF) fuel (observe (k a))
  | @FHVis _ _ _ X e c =>
      sem_ret (FHVis e (fun x => PTree.bind (c x) k))
  end.

Definition operational_bind_diagonal_approx {A R} (fuel : nat)
    (t : ptree E MN A) (k : A -> ptree E MN R) :
    MF (frontier_head E MN R) :=
  sem_bind (operational_hitting_approx (MF := MF) fuel (observe t))
    (operational_head_bind_approx fuel k).

(** The remaining PTree-specific obligation for Bind: global primitive fuel
    and the diagonal allocation of the same index to source and continuation
    must be cofinal.  This statement contains no frontier derivation and is
    kept separate from measure-level diagonal continuity. *)
Definition operational_bind_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) : Prop :=
  forall out,
    sem_lub (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.bind t k))) out <->
    sem_lub (fun fuel => operational_bind_diagonal_approx fuel t k) out.

End OperationalBindDiagonal.

Section OperationalBindSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}.

Lemma operational_head_bind_approx_increasing {A R}
    (k : A -> ptree E MN R) h :
  sem_increasing (fun fuel => operational_head_bind_approx
    (MF := MF) fuel k h).
Proof.
  destruct h as [a|X e c]; intro fuel; cbn [operational_head_bind_approx].
  - apply operational_hitting_increasing.
  - apply sem_le_refl.
Qed.

Lemma operational_head_bind_approx_mono {A R}
    (k : A -> ptree E MN R) h n m :
  Peano.le n m ->
  sem_le (operational_head_bind_approx (MF := MF) n k h)
    (operational_head_bind_approx (MF := MF) m k h).
Proof.
  intro Hnm. destruct h as [a|X e c]; cbn [operational_head_bind_approx].
  - apply operational_hitting_mono. exact Hnm.
  - apply sem_le_refl.
Qed.

Lemma operational_bind_diagonal_mono {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) n m :
  Peano.le n m ->
  sem_le (operational_bind_diagonal_approx (MF := MF) n t k)
    (operational_bind_diagonal_approx (MF := MF) m t k).
Proof.
  intro Hnm. unfold operational_bind_diagonal_approx.
  eapply sem_le_trans.
  - apply sem_bind_le_mu. apply operational_hitting_mono. exact Hnm.
  - apply sem_bind_le_k. intro h.
    apply operational_head_bind_approx_mono. exact Hnm.
Qed.

Lemma operational_head_bind_approx_lub {A R}
    (k : A -> ptree E MN R)
    (front : A -> MF (frontier_head E MN R))
    (Hfront : forall a,
      operational_weak (MF := MF) (observe (k a)) (front a)) h :
  sem_lub (fun fuel => operational_head_bind_approx
      (MF := MF) fuel k h)
    (frontier_head_bind_front k front h).
Proof.
  destruct h as [a|X e c]; cbn [operational_head_bind_approx
    frontier_head_bind_front].
  - exact (Hfront a).
  - apply sem_lub_constant.
Qed.

Theorem operational_weak_bind {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R)
    hs (front : A -> MF (frontier_head E MN R)) :
  operational_bind_cofinal (MF := MF) t k ->
  operational_weak (MF := MF) (observe t) hs ->
  (forall a, operational_weak (MF := MF) (observe (k a)) (front a)) ->
  operational_weak (MF := MF) (observe (PTree.bind t k))
    (sem_bind hs (frontier_head_bind_front k front)).
Proof.
  intros Hcofinal Hsource Hfront. unfold operational_weak in *.
  apply (proj2 (Hcofinal _)).
  unfold operational_bind_diagonal_approx.
  eapply sem_bind_diagonal_lub.
  - apply operational_hitting_increasing.
  - intro h. apply operational_head_bind_approx_increasing.
  - exact Hsource.
  - intro h. apply operational_head_bind_approx_lub. exact Hfront.
Qed.

Corollary operational_ast_weak_bind {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R)
    hs (front : A -> MF (frontier_head E MN R)) :
  operational_bind_cofinal (MF := MF) t k ->
  operational_ast_weak (MF := MF) (observe t) hs ->
  (forall a, operational_ast_weak (MF := MF)
    (observe (k a)) (front a)) ->
  sem_total (sem_bind hs (frontier_head_bind_front k front)) ->
  operational_ast_weak (MF := MF) (observe (PTree.bind t k))
    (sem_bind hs (frontier_head_bind_front k front)).
Proof.
  intros Hcofinal Hsource Hfront Htotal. split; [|exact Htotal].
  eapply operational_weak_bind; [exact Hcofinal|exact (proj1 Hsource)|].
  intro a. exact (proj1 (Hfront a)).
Qed.

End OperationalBindSoundness.

Section OperationalIterationCofinality.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

Definition operational_iter_round_approx {I R} (fuel : nat)
    (transition : I -> MN (I + R)) (i : I) :
    MF (frontier_head E MN R) :=
  sem_bind (mixed_iter_approx fuel transition i)
    (fun r => sem_ret (FHRet r)).

Definition operational_iter_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) : Prop :=
  forall out,
    sem_lub (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.iter step i))) out <->
    sem_lub (fun fuel => operational_iter_round_approx
      fuel transition i) out.

End OperationalIterationCofinality.

Section OperationalIterationSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}.

Theorem operational_weak_iter {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) out :
  sem_increasing (fun fuel => mixed_iter_approx fuel transition i) ->
  operational_iter_cofinal (MF := MF) step transition i ->
  mixed_iter transition i out ->
  operational_weak (MF := MF) (observe (PTree.iter step i))
    (sem_bind out (fun r => sem_ret
      (FHRet r : frontier_head E MN R))).
Proof.
  intros Hinc Hcofinal Hiter. unfold operational_weak.
  apply (proj2 (Hcofinal _)). unfold operational_iter_round_approx.
  eapply sem_bind_lub; [exact Hinc|exact Hiter].
Qed.

Corollary operational_ast_weak_iter {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) out :
  sem_increasing (fun fuel => mixed_iter_approx fuel transition i) ->
  operational_iter_cofinal (MF := MF) step transition i ->
  mixed_iter transition i out ->
  sem_total (sem_bind out (fun r => sem_ret
    (FHRet r : frontier_head E MN R))) ->
  operational_ast_weak (MF := MF) (observe (PTree.iter step i))
    (sem_bind out (fun r => sem_ret
      (FHRet r : frontier_head E MN R))).
Proof.
  intros Hinc Hcofinal Hiter Htotal. split; [|exact Htotal].
  eapply operational_weak_iter; eassumption.
Qed.

End OperationalIterationSoundness.

Section FrontierOperationalSoundness.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}.

Variable bind_cofinality : forall A R
    (t : ptree E MN A) (k : A -> ptree E MN R),
    operational_bind_cofinal (MF := MF) t k.

Variable iter_productivity : forall I R
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I),
    (forall j, operational_weak (MF := MF) (observe (step j))
      (mixed_bind (transition j)
        (fun next => sem_ret (FHRet next)))) ->
    sem_increasing (fun fuel => mixed_iter_approx fuel transition i) /\
    operational_iter_cofinal (MF := MF) step transition i.

(** Conditional end-to-end soundness of the structured frontier.  The
    analytic assumptions are measure capabilities; the only PTree-specific
    assumptions left are global-vs-diagonal fuel cofinality for Bind and
    productive iteration rounds. *)
Theorem frontier_to_operational_weak {R}
    (ot : ptree' E MN R) out :
  frontier ot out -> operational_weak (MF := MF) ot out.
Proof.
  intro Hfront. induction Hfront.
  - apply operational_weak_ret.
  - apply operational_weak_vis.
  - apply (proj2 (operational_weak_tau_iff t hs)). exact IHHfront.
  - eapply operational_weak_prob; [exact H|exact H1].
  - destruct (iter_productivity (I := I) (R := R)
      (step := step) (transition := transition) i H0)
      as [Hinc Hcofinal].
    eapply operational_weak_iter; eassumption.
  - eapply operational_weak_bind.
    + apply bind_cofinality.
    + exact IHHfront.
    + exact H0.
  - destruct (iter_productivity (I := I) (R := R)
      (step := step) (transition := transition) i H0)
      as [Hinc Hcofinal].
    eapply operational_weak_iter; eassumption.
Qed.

End FrontierOperationalSoundness.

Section GuardedOperationalBisimulation.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Definition operational_ast_match
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop)
    (ot1 : ptree' E MN R1) (ot2 : ptree' E MN R2) : Prop :=
  (forall out1, operational_ast_weak (MF := MF) ot1 out1 ->
    exists out2, operational_ast_weak (MF := MF) ot2 out2 /\
      sem_lift (frontier_head_rel RR sim) out1 out2) /\
  (forall out2, operational_ast_weak (MF := MF) ot2 out2 ->
    exists out1, operational_ast_weak (MF := MF) ot1 out1 /\
      sem_lift (frontier_head_rel RR sim) out1 out2).

Inductive operational_bisimF
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop) :
    ptree' E MN R1 -> ptree' E MN R2 -> Prop :=
  | OPBStable ot1 ot2 out1 out2 :
      operational_ast_weak (MF := MF) ot1 out1 ->
      operational_ast_weak (MF := MF) ot2 out2 ->
      sem_lift (frontier_head_rel RR sim) out1 out2 ->
      operational_bisimF sim ot1 ot2
  | OPBRet r1 r2 :
      RR r1 r2 -> operational_bisimF sim (RetF r1) (RetF r2)
  | OPBVis {X : Type} (e : E X) k1 k2 :
      (forall x, sim (k1 x) (k2 x)) ->
      operational_bisimF sim (VisF e k1) (VisF e k2)
  | OPBTau t1 t2 :
      operational_ast_match sim (TauF t1) (TauF t2) ->
      sim t1 t2 -> operational_bisimF sim (TauF t1) (TauF t2)
  | OPBProb {X Y : Type} (mu : MN X) (nu : MN Y) k1 k2 :
      operational_ast_match sim (ProbF mu k1) (ProbF nu k2) ->
      sem_lift (fun x y => sim (k1 x) (k2 y)) mu nu ->
      operational_bisimF sim (ProbF mu k1) (ProbF nu k2)
  | OPBTauL t1 ot2 :
      operational_bisimF sim (observe t1) ot2 ->
      operational_bisimF sim (TauF t1) ot2
  | OPBTauR ot1 t2 :
      operational_bisimF sim ot1 (observe t2) ->
      operational_bisimF sim ot1 (TauF t2).

Lemma operational_ast_match_mono sim1 sim2 ot1 ot2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  operational_ast_match sim1 ot1 ot2 ->
  operational_ast_match sim2 ot1 ot2.
Proof.
  intros Hsim [HL HR]. split; intros out Hweak.
  - destruct (HL _ Hweak) as [out' [Hweak' Hlift]].
    exists out'. split; [exact Hweak'|].
    eapply sem_lift_mono; [|exact Hlift].
    exact (frontier_head_rel_mono Hsim).
  - destruct (HR _ Hweak) as [out' [Hweak' Hlift]].
    exists out'. split; [exact Hweak'|].
    eapply sem_lift_mono; [|exact Hlift].
    exact (frontier_head_rel_mono Hsim).
Qed.

Lemma operational_bisimF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall ot1 ot2, operational_bisimF sim1 ot1 ot2 ->
    operational_bisimF sim2 ot1 ot2.
Proof.
  intros Hsim ot1 ot2 Hstep. induction Hstep.
  - eapply OPBStable; [exact H|exact H0|].
    eapply sem_lift_mono; [|exact H1].
    exact (frontier_head_rel_mono Hsim).
  - apply OPBRet. exact H.
  - apply OPBVis. intros x. exact (Hsim _ _ (H x)).
  - apply OPBTau.
    + exact (operational_ast_match_mono Hsim H).
    + exact (Hsim _ _ H0).
  - apply OPBProb.
    + exact (operational_ast_match_mono Hsim H).
    + eapply sem_lift_mono; [|exact H0].
      intros x y Hxy. exact (Hsim _ _ Hxy).
  - exact (OPBTauL IHHstep).
  - exact (OPBTauR IHHstep).
Qed.

Definition operational_bisim_body sim
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) :=
  operational_bisimF sim (observe t1) (observe t2).

Program Definition foperational_bisim :
    mon (ptree E MN R1 -> ptree E MN R2 -> Prop) :=
  {| body := operational_bisim_body |}.
Next Obligation.
  intros sim1 sim2 Hsub t1 t2 Hstep.
  eapply operational_bisimF_monotone; eauto.
Qed.

Definition operational_bisim :
    ptree E MN R1 -> ptree E MN R2 -> Prop :=
  gfp foperational_bisim.

Lemma operational_bisim_unfold t1 t2 :
  operational_bisim t1 t2 ->
  operational_bisimF operational_bisim (observe t1) (observe t2).
Proof.
  intro H. apply (gfp_pfp foperational_bisim) in H. exact H.
Qed.

Lemma operational_bisim_fold t1 t2 :
  operational_bisimF operational_bisim (observe t1) (observe t2) ->
  operational_bisim t1 t2.
Proof.
  intro H. unfold operational_bisim.
  apply (gfp_fp foperational_bisim). exact H.
Qed.

End GuardedOperationalBisimulation.

Section GuardedOperationalReflexivity.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

Lemma operational_ast_match_refl {R}
    (sim : ptree E MN R -> ptree E MN R -> Prop)
    (Hhead : Reflexive (frontier_head_rel eq sim)) :
  forall ot, operational_ast_match eq sim ot ot.
Proof.
  intro ot. split; intros out Hweak; exists out; split; auto.
  all: apply sem_lift_refl; exact Hhead.
Qed.

Lemma operational_bisim_refl {R} :
  Reflexive (@operational_bisim E MN MF NI FI NC FC MX FO R R eq).
Proof.
  intro t. revert t. unfold operational_bisim.
  coinduction CH CIH. intro t.
  unfold operational_bisim_body. set (ot := observe t).
  change (operational_bisimF eq (elem CH) ot ot).
  destruct ot as [r|u|X e k|X mu k].
  - apply OPBRet. reflexivity.
  - apply OPBTau.
    + apply operational_ast_match_refl.
      apply unified_head_rel_refl. exact CIH.
    + exact (CIH u).
  - apply OPBVis. intro x. exact (CIH (k x)).
  - apply OPBProb.
    + apply operational_ast_match_refl.
      apply unified_head_rel_refl. exact CIH.
    + apply sem_lift_refl. intro x. exact (CIH (k x)).
Qed.

Lemma operational_bisim_of_common_ast {R}
    (t1 t2 : ptree E MN R) out :
  operational_ast_weak (MF := MF) (observe t1) out ->
  operational_ast_weak (MF := MF) (observe t2) out ->
  @operational_bisim E MN MF NI FI NC FC MX FO R R eq t1 t2.
Proof.
  intros H1 H2. apply operational_bisim_fold.
  eapply OPBStable; [exact H1|exact H2|].
  apply sem_lift_refl. apply unified_head_rel_refl.
  exact operational_bisim_refl.
Qed.

End GuardedOperationalReflexivity.
