Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Program.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Compatibility names for the canonical primitive stable-target layer.
    There is no second operational target datatype. *)
Polymorphic Definition operational_target
    (E : Type -> Type) (MN : Type -> Type) (R : Type) : Type :=
  stable_target (ptree' E MN R) (frontier_head E MN R).

Notation OPStable := SHStable.
Notation OPInternal := SHInternal.

Section OperationalKernel.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

(** The same primitive transition in the generic stable-hitting interface.
    Residual states are observations, not syntax constructors: taking the
    transition never recognizes a derived [bind] or [iter] form. *)
Definition ptree_primitive_kernel {R} (ot : ptree' E MN R) :
    MF (stable_target (ptree' E MN R) (frontier_head E MN R)) :=
  match ot with
  | RetF r => sem_ret (SHStable (FHRet r))
  | VisF _ e k => sem_ret (SHStable (FHVis e k))
  | TauF t => sem_ret (SHInternal (observe t))
  | ProbF _ mu k =>
      mixed_bind mu (fun x => sem_ret (SHInternal (observe (k x))))
  end.

(** Deprecated compatibility alias.  Residual states are observations in
    both presentations, so the two kernels are definitionally identical. *)
Definition operational_kernel {R} (ot : ptree' E MN R) :
    MF (operational_target E MN R) :=
  ptree_primitive_kernel ot.

(** Resolve one operational target using at most [fuel] further primitive
    steps.  Unresolved internal mass goes to [sem_zero]. *)
Definition operational_target_approx {R} (fuel : nat)
    (target : operational_target E MN R) :
    MF (frontier_head E MN R) :=
  stable_target_approx ptree_primitive_kernel fuel target.

(** The [fuel]-bounded stable-hitting distribution of an observed state.
    Fuel counts primitive internal transitions.  Ret and Vis are stable after
    their one primitive observation step; Tau and Prob recursively spend the
    remaining fuel through the same kernel. *)
Definition operational_hitting_approx {R} (fuel : nat)
    (ot : ptree' E MN R) : MF (frontier_head E MN R) :=
  stable_hitting_approx ptree_primitive_kernel fuel ot.

(** A generic weak behavior is the (possibly subprobabilistic) stable-hitting
    limit of primitive execution.  Unresolved mass is absent from each finite
    approximant, hence pure divergence has the zero subdistribution as its
    hitting limit. *)
Definition operational_weak {R} (ot : ptree' E MN R)
    (out : MF (frontier_head E MN R)) : Prop :=
  stable_hitting_weak ptree_primitive_kernel ot out.

(** AST is a separate property of a weak behavior: its stable-hitting limit
    has total mass.  Keeping these notions separate is necessary because an
    ordinary finite frontier may legitimately be a subprobability measure. *)
Definition operational_ast_weak {R} (ot : ptree' E MN R)
    (out : MF (frontier_head E MN R)) : Prop :=
  operational_weak ot out /\ sem_total out.

(** A syntax-independent bridge for genuinely nested unbounded execution.
    [grid outer inner] may allocate separate fuel to an outer protocol and
    an inner AST sampler.  The program-specific obligation is only that its
    primitive global-fuel chain has the same limits as the diagonal grid.
    Fubini continuity then turns iterated row limits into that diagonal
    limit; no [Bind], [Iter], or [NestedIter] semantic constructor is used. *)
Definition operational_hitting_diagonal_cofinal {R}
    (ot : ptree' E MN R)
    (grid : nat -> nat -> MF (frontier_head E MN R)) : Prop :=
  forall out,
    sem_lub (fun fuel => operational_hitting_approx fuel ot) out <->
    sem_lub (fun fuel => grid fuel fuel) out.

Section OperationalNestedGrid.
Context `{FFubini : @SemanticOmegaFubiniLaws MF FI FO}.

Theorem operational_weak_of_nested_grid {R}
    (ot : ptree' E MN R)
    (grid : nat -> nat -> MF (frontier_head E MN R))
    (row_out : nat -> MF (frontier_head E MN R)) out :
  operational_hitting_diagonal_cofinal ot grid ->
  (forall outer, sem_increasing (grid outer)) ->
  (forall inner, sem_increasing (fun outer => grid outer inner)) ->
  (forall outer, sem_lub (grid outer) (row_out outer)) ->
  sem_lub row_out out ->
  operational_weak ot out.
Proof.
  intros Hcofinal Hinner Houter Hrows Hout.
  unfold operational_weak.
  apply (proj2 (Hcofinal out)).
  eapply sem_lub_double_diagonal; eassumption.
Qed.

Corollary operational_ast_weak_of_nested_grid {R}
    (ot : ptree' E MN R)
    (grid : nat -> nat -> MF (frontier_head E MN R))
    (row_out : nat -> MF (frontier_head E MN R)) out :
  operational_hitting_diagonal_cofinal ot grid ->
  (forall outer, sem_increasing (grid outer)) ->
  (forall inner, sem_increasing (fun outer => grid outer inner)) ->
  (forall outer, sem_lub (grid outer) (row_out outer)) ->
  sem_lub row_out out ->
  sem_total out ->
  operational_ast_weak ot out.
Proof.
  intros Hcofinal Hinner Houter Hrows Hout Htotal.
  split; [|exact Htotal].
  eapply operational_weak_of_nested_grid; eassumption.
Qed.

End OperationalNestedGrid.

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
  operational_kernel (TauF t) = sem_ret (OPInternal (observe t)).
Proof. reflexivity. Qed.

Lemma operational_kernel_probE {R X} (mu : MN X)
    (k : X -> ptree E MN R) :
  operational_kernel (ProbF mu k) =
  mixed_bind mu (fun x => sem_ret (OPInternal (observe (k x)))).
Proof. reflexivity. Qed.

Lemma operational_target_stableE {R} fuel
    (h : frontier_head E MN R) :
  operational_target_approx fuel (OPStable h) = sem_ret h.
Proof. destruct fuel; reflexivity. Qed.

Lemma operational_target_internal_zeroE {R} (t : ptree' E MN R) :
  operational_target_approx O (OPInternal t) = sem_zero.
Proof. reflexivity. Qed.

Lemma operational_target_internal_succE {R} fuel
    (t : ptree' E MN R) :
  operational_target_approx (Datatypes.S fuel)
    (OPInternal t) =
  sem_bind (operational_kernel t)
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
  unfold operational_hitting_approx, stable_hitting_approx,
    ptree_primitive_kernel.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite stable_target_stableE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_vis {R X} fuel (e : E X)
    (k : X -> ptree E MN R) :
  sem_eq (operational_hitting_approx (MF := MF) fuel (VisF e k))
    (sem_ret (FHVis e k : frontier_head E MN R)).
Proof.
  unfold operational_hitting_approx, stable_hitting_approx,
    ptree_primitive_kernel.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite stable_target_stableE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_tau_zero {R} (t : ptree E MN R) :
  sem_eq (operational_hitting_approx (MF := MF) O (TauF t)) sem_zero.
Proof.
  unfold operational_hitting_approx, stable_hitting_approx,
    ptree_primitive_kernel.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite stable_target_internal_zeroE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_tau_succ {R} fuel (t : ptree E MN R) :
  sem_eq
    (operational_hitting_approx (MF := MF) (Datatypes.S fuel) (TauF t))
    (operational_hitting_approx fuel (observe t)).
Proof.
  unfold operational_hitting_approx, stable_hitting_approx at 1.
  unfold ptree_primitive_kernel.
  eapply sem_eq_trans.
  - apply sem_bind_ret_l.
  - rewrite stable_target_internal_succE. apply sem_eq_refl.
Qed.

Lemma operational_hitting_prob {R X} fuel (mu : MN X)
    (k : X -> ptree E MN R) :
  sem_eq (operational_hitting_approx (MF := MF) fuel (ProbF mu k))
    (mixed_bind mu (fun x =>
      operational_target_approx fuel (OPInternal (observe (k x))))).
Proof.
  unfold operational_hitting_approx, stable_hitting_approx,
    ptree_primitive_kernel.
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

Section GenericKernelAdequacy.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}.

(** Adequacy of the PTree adapter for the syntax-independent primitive
    kernel semantics.  This is pointwise in finite fuel, so the later weak
    and AST correspondence does not assume omega-limit uniqueness or a
    structured frontier derivation. *)
Theorem ptree_primitive_hitting_adequate {R} fuel
    (ot : ptree' E MN R) :
  sem_eq
    (stable_hitting_approx
      (@ptree_primitive_kernel E MN MF FI MX R) fuel ot)
    (operational_hitting_approx (MF := MF) fuel ot).
Proof.
  induction fuel as [|fuel IH] in ot |- *; destruct ot as [r|t|X e k|X mu k].
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE.
    apply sem_eq_sym. apply operational_hitting_ret.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_internal_zeroE.
    apply sem_eq_sym. apply operational_hitting_tau_zero.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE.
    apply sem_eq_sym. apply operational_hitting_vis.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply mixed_bind_assoc|].
    eapply sem_eq_trans.
    + apply mixed_bind_ae_proper.
      eapply sem_ae_mono; [|apply sem_ae_true].
      intros x _. eapply sem_eq_trans; [apply sem_bind_ret_l|].
      rewrite stable_target_internal_zeroE. apply sem_eq_refl.
    + apply sem_eq_sym. apply operational_hitting_prob_zero.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE.
    apply sem_eq_sym. apply operational_hitting_ret.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_internal_succE.
    eapply sem_eq_trans; [apply IH|].
    apply sem_eq_sym. apply operational_hitting_tau_succ.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE.
    apply sem_eq_sym. apply operational_hitting_vis.
  - unfold stable_hitting_approx, ptree_primitive_kernel.
    eapply sem_eq_trans; [apply mixed_bind_assoc|].
    eapply sem_eq_trans.
    + apply mixed_bind_ae_proper.
      eapply sem_ae_mono; [|apply sem_ae_true].
      intros x _. eapply sem_eq_trans; [apply sem_bind_ret_l|].
      rewrite stable_target_internal_succE. apply IH.
    + apply sem_eq_sym. apply operational_hitting_prob_succ.
Qed.

Context `{FOL : @SemanticOmegaLaws MF FI FO}.

Theorem ptree_primitive_weak_adequate {R}
    (ot : ptree' E MN R) out :
  stable_hitting_weak
      (@ptree_primitive_kernel E MN MF FI MX R) ot out <->
  operational_weak (MF := MF) ot out.
Proof.
  unfold stable_hitting_weak, operational_weak. split; intro Hlim.
  - eapply sem_lub_chain_proper; [|exact Hlim].
    intro fuel. apply ptree_primitive_hitting_adequate.
  - eapply sem_lub_chain_proper; [|exact Hlim].
    intro fuel. apply sem_eq_sym.
    apply ptree_primitive_hitting_adequate.
Qed.

Theorem ptree_primitive_ast_adequate {R}
    (ot : ptree' E MN R) out :
  stable_hitting_ast
      (@ptree_primitive_kernel E MN MF FI MX R) ot out <->
  operational_ast_weak (MF := MF) ot out.
Proof.
  unfold stable_hitting_ast, operational_ast_weak.
  rewrite ptree_primitive_weak_adequate. reflexivity.
Qed.

End GenericKernelAdequacy.


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

Section OperationalInterpDiagonal.
Context {E F : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

Definition operational_interp_head_tree {R}
    (handler : forall X, E X -> ptree F MN X)
    (h : frontier_head E MN R) : ptree F MN R :=
  match h with
  | FHRet r => Ret r
  | @FHVis _ _ _ X e k =>
      Tau (PTree.bind (@handler X e)
        (fun x => PTree.interp handler (k x)))
  end.

Definition operational_interp_head_approx {R}
    (fuel : nat) (handler : forall X, E X -> ptree F MN X)
    (h : frontier_head E MN R) :
    MF (frontier_head F MN R) :=
  operational_hitting_approx (MF := MF) fuel
    (observe (operational_interp_head_tree handler h)).

Definition operational_interp_diagonal_approx {R}
    (fuel : nat) (handler : forall X, E X -> ptree F MN X)
    (t : ptree E MN R) : MF (frontier_head F MN R) :=
  sem_bind
    (operational_hitting_approx (MF := MF) fuel (observe t))
    (operational_interp_head_approx fuel handler).

Definition operational_interp_cofinal {R}
    (handler : forall X, E X -> ptree F MN X)
    (t : ptree E MN R) : Prop :=
  forall out,
    sem_lub (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.interp handler t))) out <->
    sem_lub (fun fuel => operational_interp_diagonal_approx
      fuel handler t) out.

End OperationalInterpDiagonal.

Section OperationalInterpSoundness.
Context {E F : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}.

Lemma operational_interp_head_approx_increasing {R}
    (handler : forall X, E X -> ptree F MN X)
    (h : frontier_head E MN R) :
  sem_increasing (fun fuel => operational_interp_head_approx
    (MF := MF) fuel handler h).
Proof.
  intro fuel. apply operational_hitting_increasing.
Qed.

Lemma operational_interp_head_approx_lub {R}
    (handler : forall X, E X -> ptree F MN X)
    (front : frontier_head E MN R -> MF (frontier_head F MN R))
    (Hfront : forall h, operational_weak (MF := MF)
      (observe (operational_interp_head_tree handler h)) (front h)) h :
  sem_lub (fun fuel => operational_interp_head_approx
      (MF := MF) fuel handler h) (front h).
Proof.
  exact (Hfront h).
Qed.

Theorem operational_weak_interp {R}
    (handler : forall X, E X -> ptree F MN X)
    (t : ptree E MN R)
    hs (front : frontier_head E MN R -> MF (frontier_head F MN R)) :
  operational_interp_cofinal (MF := MF) handler t ->
  operational_weak (MF := MF) (observe t) hs ->
  (forall h, operational_weak (MF := MF)
    (observe (operational_interp_head_tree handler h)) (front h)) ->
  operational_weak (MF := MF) (observe (PTree.interp handler t))
    (sem_bind hs front).
Proof.
  intros Hcofinal Hsource Hfront. unfold operational_weak in *.
  apply (proj2 (Hcofinal _)).
  unfold operational_interp_diagonal_approx.
  eapply sem_bind_diagonal_lub.
  - apply operational_hitting_increasing.
  - intro h. apply operational_interp_head_approx_increasing.
  - exact Hsource.
  - intro h. apply operational_interp_head_approx_lub. exact Hfront.
Qed.

End OperationalInterpSoundness.

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
Qed.

(** Soundness into the syntax-independent standard model.  The conclusion
    mentions only the primitive PTree kernel adapter and generic stable
    hitting; the structured frontier is used solely as a proof system on the
    premise side. *)
Theorem frontier_to_primitive_stable_weak {R}
    (ot : ptree' E MN R) out :
  frontier ot out ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R) ot out.
Proof.
  intro Hfront.
  apply (proj2 (ptree_primitive_weak_adequate ot out)).
  exact (frontier_to_operational_weak Hfront).
Qed.

Corollary frontier_to_primitive_stable_ast {R}
    (ot : ptree' E MN R) out :
  frontier ot out -> sem_total out ->
  stable_hitting_ast
    (@ptree_primitive_kernel E MN MF FI MX R) ot out.
Proof.
  intros Hfront Htotal. split.
  - exact (frontier_to_primitive_stable_weak Hfront).
  - exact Htotal.
Qed.

End FrontierOperationalSoundness.
