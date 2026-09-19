Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import List Arith.PeanoNat FunctionalExtensionality Lia
  Logic.ClassicalChoice Program.Equality Morphisms.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import DiscreteMC FrontierLiftEnum TwoLevelMeasure
  TwoLevelMeasureEnum FreeOmegaMeasure MeasureIteration.
From PTree.Eq Require Import Shallow UnifiedFrontier PrimitiveStableHitting
  PTreeKernel PEutt PStruct PStrong PFinite.
From PTree.Eq.FreeOmega Require Import Base Relation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FreeOmegaBind.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).

Lemma ptree_hitting_pstruct_no_event {A}
    (no_event : forall X, E X -> False) fuel
    (t1 t2 : ptree E MN A) :
  pstruct eq t1 t2 ->
  free_omega_lift eq
    (ptree_hitting_approx (MF := MF) fuel (observe t1))
    (ptree_hitting_approx (MF := MF) fuel (observe t2)).
Proof.
  intro Hstruct. eapply free_omega_lift_mono with
    (R := stable_head_rel eq (pstruct eq)).
  - intros h1 h2 Hhead.
    destruct h1 as [a1|X1 e1 k1];
      destruct h2 as [a2|X2 e2 k2].
    + inversion Hhead; subst. reflexivity.
    + exfalso. exact (@no_event X2 e2).
    + exfalso. exact (@no_event X1 e1).
    + exfalso. exact (@no_event X1 e1).
  - exact (ptree_hitting_pstruct
      (RR := eq) fuel Hstruct).
Qed.

Theorem ptree_stable_hitting_pstruct_no_event {A}
    (no_event : forall X, E X -> False)
    (t1 t2 : ptree E MN A) :
  pstruct eq t1 t2 ->
  forall out,
    @ptree_stable_hitting E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega A (observe t1) out <->
    @ptree_stable_hitting E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega A (observe t2) out.
Proof.
  intros Hstruct out. unfold ptree_stable_hitting. split; intro Hlim.
  - eapply sem_lub_chain_proper; [|exact Hlim]. intro fuel.
    apply FOQLStructural.
    exact (ptree_hitting_pstruct_no_event
      no_event fuel Hstruct).
  - eapply sem_lub_chain_proper; [|exact Hlim]. intro fuel.
    apply FOQLStructural.
    apply free_omega_lift_sym.
    eapply free_omega_lift_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + exact (ptree_hitting_pstruct_no_event
        no_event fuel Hstruct).
Qed.

Corollary ptree_stable_hitting_bind_assoc_no_event {A B C}
    (no_event : forall X, E X -> False)
    (t : ptree E MN A) (k : A -> ptree E MN B)
    (h : B -> ptree E MN C) out :
  @ptree_stable_hitting E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega C
    (observe (PTree.bind (PTree.bind t k) h)) out <->
  @ptree_stable_hitting E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega C
    (observe (PTree.bind t (fun a => PTree.bind (k a) h))) out.
Proof.
  apply ptree_stable_hitting_pstruct_no_event; [exact no_event|].
  apply pstruct_bind_assoc.
Qed.

Lemma ptree_bind_diagonal_mono {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) n m :
  Peano.le n m ->
  free_omega_approx eq
    (ptree_bind_diagonal_approx (MF := MF) n t k)
    (ptree_bind_diagonal_approx (MF := MF) m t k).
Proof.
  apply (ptree_bind_diagonal_mono
    (FI := FreeOmegaObservableSemanticMeasure)
    (FO := FreeOmegaObservableSemanticOmega)
    (MX := FreeOmegaMixedMeasure)).
Qed.

(** A concrete, finite obligation replacing the abstract Bind lub equality:
    every global-fuel approximant is contained in some diagonal approximant,
    and conversely. *)
Definition ptree_bind_approx_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) : Prop :=
  free_omega_chains_cofinal eq
    (fun fuel => ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.bind t k)))
    (fun fuel => ptree_bind_diagonal_approx (MF := MF) fuel t k).

Theorem ptree_bind_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  ptree_bind_approx_cofinal t k ->
  @PTreeKernel.ptree_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A R t k.
Proof.
  intros Hcofinal out. unfold PTreeKernel.ptree_bind_cofinal.
  apply free_omega_cofinal_lub_iff.
  - intro n. apply ptree_observable_hitting_increasing.
  - intro n. exact (@PTreeKernel.ptree_bind_diagonal_mono E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
      FreeOmegaObservableSemanticMeasureOrderLaws A R t k n (S n)
      (Nat.le_succ_diag_r n)).
  - exact Hcofinal.
Qed.

Lemma ptree_bind_ret_approx_cofinal {A R}
    (a : A) (k : A -> ptree E MN R) :
  ptree_bind_approx_cofinal (Ret a) k.
Proof.
  split; intro n; exists n.
  all: rewrite (observing_observe (bind_ret_ a k)).
  all:
    unfold ptree_bind_approx_cofinal,
      ptree_bind_diagonal_approx,
      ptree_head_bind_approx,
      ptree_hitting_approx, ptree_primitive_kernel;
    cbn.
  all: rewrite !stable_target_stableE; cbn.
  all: apply free_omega_approx_refl; intros x; reflexivity.
Qed.

Corollary ptree_bind_ret_cofinal {A R}
    (a : A) (k : A -> ptree E MN R) :
  @PTreeKernel.ptree_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A R (Ret a) k.
Proof.
  apply ptree_bind_cofinal.
  apply ptree_bind_ret_approx_cofinal.
Qed.

(** Binding a pure continuation does not introduce a second unbounded
    computation.  Stable heads are mapped immediately, so global primitive
    fuel and diagonal bind fuel coincide rather than merely being cofinal. *)
Definition pure_head_bind {A R} (f : A -> R)
    (h : stable_head E MN A) : stable_head E MN R :=
  match h with
  | FHRet a => FHRet (f a)
  | @FHVis _ _ _ X e c =>
      FHVis e (fun x => PTree.bind (c x) (fun a => Ret (f a)))
  end.

Lemma ptree_hitting_bind_ret_map {A R}
    (t : ptree E MN A) (f : A -> R) fuel :
  ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.bind t (fun a => Ret (f a)))) =
  free_omega_bind
    (ptree_hitting_approx (MF := MF) fuel (observe t))
    (fun h => FORet (pure_head_bind f h)).
Proof.
  revert t. induction fuel as [|fuel IH]; intro t;
    rewrite observe_bind; remember (observe t) as ot eqn:Hot;
    destruct ot as [a|u|X e c|X mu c].
  - reflexivity.
  - cbn [ptree_hitting_approx ptree_primitive_kernel].
    reflexivity.
  - reflexivity.
  - change (FOSample mu (fun _ : X => FOZero) =
      free_omega_bind (FOSample mu (fun _ : X => FOZero))
        (fun h => FORet (pure_head_bind f h))).
    reflexivity.
  - reflexivity.
  - cbn [observe ptree_hitting_approx ptree_primitive_kernel].
    exact (IH u).
  - reflexivity.
  - change (FOSample mu (fun x => ptree_hitting_approx (MF := MF)
        fuel (observe (PTree.bind (c x) (fun a => Ret (f a))))) =
      free_omega_bind
        (FOSample mu (fun x => ptree_hitting_approx (MF := MF)
          fuel (observe (c x))))
        (fun h => FORet (pure_head_bind f h))).
    cbn [free_omega_bind].
    f_equal. apply functional_extensionality. intro x.
    exact (IH (c x)).
Qed.

Lemma ptree_head_bind_ret_map {A R}
    (f : A -> R) fuel (h : stable_head E MN A) :
  ptree_head_bind_approx (MF := MF) fuel
    (fun a => Ret (f a)) h = FORet (pure_head_bind f h).
Proof.
  destruct h as [a|X e c].
  - cbn [ptree_head_bind_approx pure_head_bind].
    assert (Hret : observe (Ret (f a) : ptree E MN R) = RetF (f a))
      by reflexivity.
    rewrite Hret. unfold ptree_hitting_approx, ptree_primitive_kernel.
    cbn. rewrite stable_target_stableE. reflexivity.
  - reflexivity.
Qed.

Lemma ptree_bind_ret_diagonal_map {A R}
    (t : ptree E MN A) (f : A -> R) fuel :
  ptree_bind_diagonal_approx (MF := MF) fuel t
      (fun a => Ret (f a)) =
  free_omega_bind
    (ptree_hitting_approx (MF := MF) fuel (observe t))
    (fun h => FORet (pure_head_bind f h)).
Proof.
  unfold ptree_bind_diagonal_approx.
  change (free_omega_bind
    (ptree_hitting_approx (MF := MF) fuel (observe t))
    (ptree_head_bind_approx (MF := MF) fuel
      (fun a => Ret (f a))) =
    free_omega_bind
      (ptree_hitting_approx (MF := MF) fuel (observe t))
      (fun h => FORet (pure_head_bind f h))).
  f_equal. apply functional_extensionality. intro h.
  apply ptree_head_bind_ret_map.
Qed.

Theorem ptree_bind_ret_map_approx_cofinal {A R}
    (t : ptree E MN A) (f : A -> R) :
  ptree_bind_approx_cofinal t (fun a => Ret (f a)).
Proof.
  split; intro fuel; exists fuel.
  - rewrite ptree_hitting_bind_ret_map,
      ptree_bind_ret_diagonal_map.
    apply free_omega_approx_refl. intros h. reflexivity.
  - rewrite ptree_hitting_bind_ret_map,
      ptree_bind_ret_diagonal_map.
    apply free_omega_approx_refl. intros h. reflexivity.
Qed.

Corollary ptree_bind_ret_map_cofinal {A R}
    (t : ptree E MN A) (f : A -> R) :
  @PTreeKernel.ptree_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A R t
    (fun a => Ret (f a)).
Proof.
  apply ptree_bind_cofinal.
  exact (ptree_bind_ret_map_approx_cofinal t f).
Qed.

(** A shared global primitive budget is contained in the more generous
    diagonal allocation that gives the same budget to the source and to the
    continuation. *)
Lemma ptree_bind_hitting_le_diagonal {A R}
    (fuel : nat) (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_omega_approx eq
    (ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.bind t k)))
    (ptree_bind_diagonal_approx (MF := MF) fuel t k).
Proof.
  revert t. induction fuel as [|fuel IH]; intro t.
  - rewrite observe_bind. remember (observe t) as ot eqn:Hot.
    destruct ot as [a|u|X e c|X mu c];
      unfold ptree_bind_diagonal_approx; rewrite <- Hot.
    + change (free_omega_approx eq
        (ptree_hitting_approx (MF := MF) 0 (observe (k a)))
        (free_omega_bind (FORet (FHRet a))
          (ptree_head_bind_approx (MF := MF) 0 k))).
      cbn [free_omega_bind ptree_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + constructor.
    + change (free_omega_approx eq
        (FORet (FHVis e (fun x => PTree.bind (c x) k)))
        (free_omega_bind (FORet (FHVis e c))
          (ptree_head_bind_approx (MF := MF) 0 k))).
      cbn [free_omega_bind ptree_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + change (free_omega_approx eq
        (FOSample mu (fun _ : X => FOZero))
        (free_omega_bind (FOSample mu (fun _ : X => FOZero))
          (ptree_head_bind_approx (MF := MF) 0 k))).
      cbn [free_omega_bind].
      eapply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intros x. reflexivity.
      * intros x y ->. constructor.
  - rewrite observe_bind. remember (observe t) as ot eqn:Hot.
    destruct ot as [a|u|X e c|X mu c].
    + unfold ptree_bind_diagonal_approx. rewrite <- Hot.
      cbn [ptree_hitting_approx ptree_primitive_kernel
        ptree_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + unfold ptree_bind_diagonal_approx. rewrite <- Hot.
      cbn [ptree_hitting_approx ptree_primitive_kernel
        ptree_head_bind_approx].
      eapply free_omega_approx_trans.
      * apply IH.
      * unfold ptree_bind_diagonal_approx.
        eapply free_omega_approx_bind with (R := eq) (T := eq).
        -- apply free_omega_approx_refl. intros x. reflexivity.
        -- intros h1 h2 ->.
           destruct h2; cbn [ptree_head_bind_approx].
           ++ apply ptree_hitting_mono. apply le_S, le_n.
           ++ apply free_omega_approx_refl. intros z. reflexivity.
    + unfold ptree_bind_diagonal_approx. rewrite <- Hot.
      cbn [ptree_hitting_approx ptree_primitive_kernel
        ptree_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + unfold ptree_bind_diagonal_approx. rewrite <- Hot.
      change (free_omega_approx eq
        (FOSample mu (fun x => ptree_hitting_approx (MF := MF)
          fuel (observe (PTree.bind (c x) k))))
        (free_omega_bind
          (FOSample mu (fun x => ptree_hitting_approx (MF := MF)
            fuel (observe (c x))))
          (ptree_head_bind_approx (MF := MF)
            (S fuel) k))).
      cbn [free_omega_bind].
      eapply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intros x. reflexivity.
      * intros x y ->. eapply free_omega_approx_trans.
        -- apply IH.
        -- unfold ptree_bind_diagonal_approx.
           eapply free_omega_approx_bind with (R := eq) (T := eq).
           ++ apply free_omega_approx_refl. intros z. reflexivity.
           ++ intros h1 h2 ->.
              destruct h2; cbn [ptree_head_bind_approx].
              ** apply ptree_hitting_mono. apply le_S, le_n.
              ** apply free_omega_approx_refl. intros z. reflexivity.
Qed.

(** Split-budget form of a bind approximation.  It is useful for proving
    that sequentially spending [source_fuel] and [continuation_fuel] is
    implementable by their sum in the primitive global machine. *)
Definition ptree_bind_split_approx {A R}
    (source_fuel continuation_fuel : nat)
    (t : ptree E MN A) (k : A -> ptree E MN R) :
    MF (stable_head E MN R) :=
  free_omega_bind
    (ptree_hitting_approx (MF := MF) source_fuel (observe t))
    (ptree_head_bind_approx (MF := MF) continuation_fuel k).

Lemma ptree_bind_split_le_hitting {A R}
    (source_fuel continuation_fuel : nat)
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_omega_approx eq
    (ptree_bind_split_approx
      source_fuel continuation_fuel t k)
    (ptree_hitting_approx (MF := MF)
      (source_fuel + continuation_fuel)
      (observe (PTree.bind t k))).
Proof.
  revert t. induction source_fuel as [|source_fuel IH]; intro t.
  - unfold ptree_bind_split_approx.
    rewrite observe_bind. remember (observe t) as ot eqn:Hot.
    destruct ot as [a|u|X e c|X mu c].
    + change (free_omega_approx eq
        (free_omega_bind (FORet (FHRet a))
          (ptree_head_bind_approx (MF := MF)
            continuation_fuel k))
        (ptree_hitting_approx (MF := MF)
          continuation_fuel (observe (k a)))).
      cbn [free_omega_bind ptree_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + constructor.
    + assert (Hvis : observe (Vis e (fun x => PTree.bind (c x) k)) =
          VisF e (fun x => PTree.bind (c x) k)).
      { reflexivity. }
      rewrite Hvis.
      cbv [ptree_hitting_approx ptree_primitive_kernel sem_bind sem_ret
        FreeOmegaObservableSemanticMeasure free_omega_bind
        FreeOmegaSemanticMeasure
        ptree_stable_target_approx stable_hitting_approx
        ptree_primitive_kernel observe].
      cbn [observe].
      rewrite !stable_target_stableE.
      cbv [sem_ret FreeOmegaObservableSemanticMeasure
        FreeOmegaSemanticMeasure free_omega_bind].
      cbn [free_omega_bind ptree_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + cbv [ptree_hitting_approx ptree_primitive_kernel sem_bind sem_ret
        FreeOmegaObservableSemanticMeasure free_omega_bind
        FreeOmegaSemanticMeasure
        ptree_stable_target_approx stable_hitting_approx
        ptree_primitive_kernel observe].
      eapply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intros x. reflexivity.
      * intros x y ->. constructor.
  - unfold ptree_bind_split_approx.
    rewrite observe_bind. remember (observe t) as ot eqn:Hot.
    destruct ot as [a|u|X e c|X mu c].
    + change (free_omega_approx eq
        (ptree_hitting_approx (MF := MF)
          continuation_fuel (observe (k a)))
        (ptree_hitting_approx (MF := MF)
          (S source_fuel + continuation_fuel) (observe (k a)))).
      apply ptree_hitting_mono. lia.
    + change (free_omega_approx eq
        (ptree_bind_split_approx
          source_fuel continuation_fuel u k)
        (ptree_hitting_approx (MF := MF)
          (source_fuel + continuation_fuel)
          (observe (PTree.bind u k)))).
      apply IH.
    + assert (Hvis : observe (Vis e (fun x => PTree.bind (c x) k)) =
          VisF e (fun x => PTree.bind (c x) k)).
      { reflexivity. }
      rewrite Hvis.
      cbv [ptree_hitting_approx ptree_primitive_kernel sem_bind sem_ret
        FreeOmegaObservableSemanticMeasure free_omega_bind
        FreeOmegaSemanticMeasure
        ptree_stable_target_approx stable_hitting_approx
        ptree_primitive_kernel observe].
      cbn [observe].
      rewrite !stable_target_stableE.
      cbv [sem_ret FreeOmegaObservableSemanticMeasure
        FreeOmegaSemanticMeasure free_omega_bind].
      cbn [free_omega_bind ptree_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + change (free_omega_approx eq
        (FOSample mu (fun x => ptree_bind_split_approx
          source_fuel continuation_fuel (c x) k))
        (FOSample mu (fun x => ptree_hitting_approx (MF := MF)
          (source_fuel + continuation_fuel)
          (observe (PTree.bind (c x) k))))).
      eapply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intros x. reflexivity.
      * intros x y ->. apply IH.
Qed.

Lemma ptree_bind_diagonal_le_hitting {A R}
    (fuel : nat) (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_omega_approx eq
    (ptree_bind_diagonal_approx (MF := MF) fuel t k)
    (ptree_hitting_approx (MF := MF) (2 * fuel)
      (observe (PTree.bind t k))).
Proof.
  change (free_omega_approx eq
    (ptree_bind_split_approx fuel fuel t k)
    (ptree_hitting_approx (MF := MF) (2 * fuel)
      (observe (PTree.bind t k)))).
  replace (2 * fuel) with (fuel + fuel) by lia.
  apply ptree_bind_split_le_hitting.
Qed.

Theorem ptree_bind_approx_cofinal_all {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  ptree_bind_approx_cofinal t k.
Proof.
  split.
  - intro fuel. exists fuel.
    apply ptree_bind_hitting_le_diagonal.
  - intro fuel. exists (2 * fuel).
    eapply free_omega_approx_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + apply ptree_bind_diagonal_le_hitting.
Qed.

Corollary ptree_bind_cofinal_all {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  @PTreeKernel.ptree_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A R t k.
Proof.
  apply ptree_bind_cofinal.
  apply ptree_bind_approx_cofinal_all.
Qed.

Section InterpCofinality.
Context {F : Type -> Type}.
Variable handler : forall X, E X -> ptree F MN X.

Definition ptree_interp_approx_cofinal {R}
    (t : ptree E MN R) : Prop :=
  free_omega_chains_cofinal eq
    (fun fuel => ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.interp handler t)))
    (fun fuel => ptree_interp_diagonal_approx fuel handler t).

Lemma ptree_interp_hitting_le_diagonal {R}
    (fuel : nat) (t : ptree E MN R) :
  free_omega_approx eq
    (ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.interp handler t)))
    (ptree_interp_diagonal_approx fuel handler t).
Proof.
  revert t. induction fuel as [|fuel IH]; intro t.
  all: unfold ptree_interp_diagonal_approx;
    rewrite observe_interp; remember (observe t) as ot eqn:Hot;
    destruct ot as [r|u|X e k|X mu k].
  - cbn [ptree_hitting_approx ptree_primitive_kernel
      ptree_interp_head_approx ptree_interp_head_tree
      free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - constructor.
  - constructor.
  - change (free_omega_approx eq
      (FOSample mu (fun _ : X => FOZero))
      (free_omega_bind (FOSample mu (fun _ : X => FOZero))
        (ptree_interp_head_approx (MF := MF) (R := R) 0 handler))).
    cbn [free_omega_bind]. eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. constructor.
  - cbn [ptree_hitting_approx ptree_primitive_kernel
      ptree_interp_head_approx ptree_interp_head_tree
      free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - cbn [ptree_hitting_approx ptree_primitive_kernel].
    eapply free_omega_approx_trans; [apply IH|].
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply free_omega_approx_refl. intro h. reflexivity.
    + intros h1 h2 ->. apply ptree_hitting_mono. lia.
  - cbn [ptree_hitting_approx ptree_primitive_kernel
      ptree_interp_head_approx free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - change (free_omega_approx eq
      (FOSample mu (fun x => ptree_hitting_approx (MF := MF)
        fuel (observe (PTree.interp handler (k x)))))
      (free_omega_bind
        (FOSample mu (fun x => ptree_hitting_approx (MF := MF)
          fuel (observe (k x))))
        (ptree_interp_head_approx (MF := MF) (R := R)
          (S fuel) handler))).
    cbn [free_omega_bind]. eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. eapply free_omega_approx_trans; [apply IH|].
      eapply free_omega_approx_bind with (R := eq) (T := eq).
      * apply free_omega_approx_refl. intro h. reflexivity.
      * intros h1 h2 ->. apply ptree_hitting_mono. lia.
Qed.

Definition ptree_interp_split_approx {R}
    (source_fuel head_fuel : nat) (t : ptree E MN R) :
    MF (stable_head F MN R) :=
  free_omega_bind
    (ptree_hitting_approx (MF := MF) source_fuel (observe t))
    (ptree_interp_head_approx (MF := MF) (R := R)
      head_fuel handler).

Lemma ptree_interp_split_le_hitting {R}
    (source_fuel head_fuel : nat) (t : ptree E MN R) :
  free_omega_approx eq
    (ptree_interp_split_approx source_fuel head_fuel t)
    (ptree_hitting_approx (MF := MF) (source_fuel + head_fuel)
      (observe (PTree.interp handler t))).
Proof.
  revert t. induction source_fuel as [|source_fuel IH]; intro t.
  all: unfold ptree_interp_split_approx;
    rewrite observe_interp; remember (observe t) as ot eqn:Hot;
    destruct ot as [r|u|X e k|X mu k].
  - cbn [ptree_hitting_approx ptree_primitive_kernel
      ptree_interp_head_approx ptree_interp_head_tree
      free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - constructor.
  - cbn [free_omega_bind ptree_interp_head_approx
      ptree_interp_head_tree].
    apply free_omega_approx_refl. intro h. reflexivity.
  - change (free_omega_approx eq
      (free_omega_bind (FOSample mu (fun _ : X => FOZero))
        (ptree_interp_head_approx (MF := MF) (R := R)
          head_fuel handler))
      (ptree_hitting_approx (MF := MF) head_fuel
        (observe (Prob mu (fun x => PTree.interp handler (k x)))))).
    cbn [free_omega_bind ptree_hitting_approx ptree_primitive_kernel].
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. constructor.
  - unfold ptree_hitting_approx, ptree_primitive_kernel,
      ptree_interp_head_approx, ptree_interp_head_tree.
    cbn. rewrite !stable_target_stableE. cbn [free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - cbn [ptree_hitting_approx ptree_primitive_kernel]. apply IH.
  - cbn [free_omega_bind ptree_interp_head_approx
      ptree_interp_head_tree].
    apply ptree_hitting_mono. lia.
  - change (free_omega_approx eq
      (FOSample mu (fun x => ptree_interp_split_approx
        source_fuel head_fuel (k x)))
      (FOSample mu (fun x => ptree_hitting_approx (MF := MF)
        (source_fuel + head_fuel)
        (observe (PTree.interp handler (k x)))))).
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. apply IH.
Qed.

Lemma ptree_interp_diagonal_le_hitting {R}
    (fuel : nat) (t : ptree E MN R) :
  free_omega_approx eq
    (ptree_interp_diagonal_approx fuel handler t)
    (ptree_hitting_approx (MF := MF) (2 * fuel)
      (observe (PTree.interp handler t))).
Proof.
  change (free_omega_approx eq
    (ptree_interp_split_approx fuel fuel t)
    (ptree_hitting_approx (MF := MF) (2 * fuel)
      (observe (PTree.interp handler t)))).
  replace (2 * fuel) with (fuel + fuel) by lia.
  apply ptree_interp_split_le_hitting.
Qed.

Theorem ptree_interp_approx_cofinal_all {R}
    (t : ptree E MN R) : ptree_interp_approx_cofinal t.
Proof.
  split.
  - intro fuel. exists fuel.
    apply ptree_interp_hitting_le_diagonal.
  - intro fuel. exists (2 * fuel).
    eapply free_omega_approx_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + apply ptree_interp_diagonal_le_hitting.
Qed.

Corollary ptree_interp_cofinal_all {R}
    (t : ptree E MN R) :
  @PTreeKernel.ptree_interp_cofinal E F MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R handler t.
Proof.
  intro out. unfold PTreeKernel.ptree_interp_cofinal.
  apply free_omega_cofinal_lub_iff.
  - intro n. apply ptree_observable_hitting_increasing.
  - intro n. unfold ptree_interp_diagonal_approx.
    apply free_omega_approx_bind with (R := eq).
    + apply ptree_observable_hitting_increasing.
    + intros x y ->. unfold ptree_interp_head_approx.
      apply ptree_observable_hitting_increasing.
  - apply ptree_interp_approx_cofinal_all.
Qed.

End InterpCofinality.

Definition stable_head_is_ret {R}
    (h : stable_head E MN R) : Prop :=
  match h with
  | FHRet _ => True
  | @FHVis _ _ _ X e k => False
  end.

Definition stable_head_ret_bind_front {A R}
    (front : A -> MF (stable_head E MN R))
    (h : stable_head E MN A) : MF (stable_head E MN R) :=
  match h with
  | FHRet a => front a
  | @FHVis _ _ _ X e k => FOZero
  end.

(** Lift a coupling of closed-source heads through Ret-only continuations.
    Related returns use the supplied continuation coupling; related visible
    heads are discarded on both sides.  Thus clients do not need to unfold
    [FOQLBind] merely to place a closed sampler before an eventful context. *)
Theorem sem_lift_ret_bind_front
    {A1 A2 R1 R2}
    (RA : A1 -> A2 -> Prop)
    (simA : ptree E MN A1 -> ptree E MN A2 -> Prop)
    (RR : R1 -> R2 -> Prop)
    (simR : ptree E MN R1 -> ptree E MN R2 -> Prop)
    (hs1 : MF (stable_head E MN A1))
    (hs2 : MF (stable_head E MN A2))
    (front1 : A1 -> MF (stable_head E MN R1))
    (front2 : A2 -> MF (stable_head E MN R2)) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    _ _ (stable_head_rel RA simA) hs1 hs2 ->
  (forall a1 a2, RA a1 a2 ->
    @sem_lift MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      _ _ (stable_head_rel RR simR) (front1 a1) (front2 a2)) ->
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    _ _ (stable_head_rel RR simR)
    (free_omega_bind hs1 (stable_head_ret_bind_front front1))
    (free_omega_bind hs2 (stable_head_ret_bind_front front2)).
Proof.
  intros Hsource Hfront. eapply FOQLBind; [exact Hsource|].
  intros h1 h2 Hhead. inversion Hhead; subst; clear Hhead.
  - cbn [stable_head_ret_bind_front]. apply Hfront. exact H.
  - cbn [stable_head_ret_bind_front].
    apply FOQLStructural. constructor.
Qed.

(** If the complete source behavior is almost everywhere a return head,
    bind may discard the unreachable visible-head branch.  This is the
    generic composition rule needed when a closed sampler is embedded in an
    eventful client. *)
Theorem stable_hitting_bind_ret_only
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R)
    (hs : MF (stable_head E MN A))
    (front : A -> MF (stable_head E MN R)) :
  free_omega_ae stable_head_is_ret hs ->
  @ptree_stable_hitting E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A (observe t) hs ->
  (forall a,
    @ptree_stable_hitting E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega R
      (observe (k a)) (front a)) ->
  @ptree_stable_hitting E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R
    (observe (PTree.bind t k))
    (free_omega_bind hs (stable_head_ret_bind_front front)).
Proof.
  intros Hret Hsource Hfront.
  pose (full :=
    free_omega_bind hs (stable_head_bind_front k front)).
  assert (Hfull :
      @ptree_stable_hitting E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega R
        (observe (PTree.bind t k)) full).
  { unfold full. eapply (stable_hitting_bind
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)).
    - apply ptree_bind_cofinal_all.
    - exact Hsource.
    - exact Hfront. }
  assert (Hrestricted :
      @sem_lift MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        _ _ (fun h1 h2 => h1 = h2 /\ stable_head_is_ret h1)
        hs hs).
  { eapply FOQLAERestrict with
      (T := eq) (P := stable_head_is_ret)
      (Q := stable_head_is_ret).
    - apply free_omega_qlift_refl. intro h. reflexivity.
    - exact Hret.
    - exact Hret.
    - intros h1 h2 [-> [H1 H2]]. split; [reflexivity|exact H1]. }
  assert (Houtputs :
      @sem_lift MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        _ _ eq full
        (free_omega_bind hs (stable_head_ret_bind_front front))).
  { unfold full. eapply FOQLBind; [exact Hrestricted|].
    intros h1 h2 [-> Hret1].
    destruct h2 as [a|X e c]; [|contradiction].
    cbn [stable_head_bind_front stable_head_ret_bind_front].
    apply free_omega_qlift_refl. intro h. reflexivity. }
  unfold ptree_stable_hitting, stable_hitting in Hfull |- *.
  eapply FOQLComp with (T := eq) (U := eq) (mid := full).
  - apply FOQLSym. eapply FOQLMono; [exact Houtputs|].
    intros x y ->. reflexivity.
  - exact Hfull.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

(** Unconditional monadic congruence for the maintained unbounded backend.
    The generic theorem keeps its local scheduling premise; FreeOmega now
    discharges it for every eventful PTree. *)
Corollary peutt_bind
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2)
    (k1 : R1 -> ptree E MN A) (k2 : R2 -> ptree E MN A) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R1 R2 RR t1 t2 ->
  (forall r1 r2, RR r1 r2 ->
    @peutt E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega A A eq (k1 r1) (k2 r2)) ->
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A A eq
    (PTree.bind t1 k1) (PTree.bind t2 k2).
Proof.
  intros Hsource Hk.
  eapply peutt_bind.
  - intros B S t k. apply ptree_bind_cofinal_all.
  - exact Hsource.
  - exact Hk.
  Unshelve. all: try typeclasses eauto.
Qed.

Theorem ptree_bind_approx_cofinal_no_event {A R}
    (no_event : forall X, E X -> False)
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  ptree_bind_approx_cofinal t k.
Proof.
  apply ptree_bind_approx_cofinal_all.
Qed.

Corollary ptree_bind_cofinal_no_event {A R}
    (no_event : forall X, E X -> False)
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  @PTreeKernel.ptree_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A R t k.
Proof.
  apply ptree_bind_cofinal.
  apply ptree_bind_approx_cofinal_no_event. exact no_event.
Qed.

Section NestedNoEventGrid.
Context {I A R : Type}.
Context `{NCAE : @SemanticMeasureCouplingAELaws MN NI}.
Context `{NCountAE : @SemanticMeasureCountableAELaws MN NI}.
Variable no_event : forall X, E X -> False.
Variable sample : ptree E MN A.
Variable round : I -> A -> I + R.

Definition nested_step (i : I) : ptree E MN (I + R) :=
  PTree.bind sample (fun a => Ret (round i a)).

Definition nested_program (i : I) : ptree E MN R :=
  PTree.iter nested_step i.

Definition nested_after (i : I) (a : A) : ptree E MN R :=
  match round i a with
  | inl i' => Tau (nested_program i')
  | inr r => Ret r
  end.

Lemma nested_ret_after_structural (i : I) (a : A) :
  pstruct eq
    (PTree.bind (Ret (round i a)) (fun lr =>
      match lr with
      | inl i' => Tau (nested_program i')
      | inr r => Ret r
      end))
    (nested_after i a).
Proof.
  apply observe_eq_pstruct. unfold nested_after. rewrite observe_bind.
  destruct (round i a); reflexivity.
Qed.

(** One canonical primitive round, obtained solely from the coinductive
    [iter] unfolding and structural bind laws. *)
Lemma nested_program_unfold_structural (i : I) :
  pstruct eq (nested_program i)
    (PTree.bind sample (nested_after i)).
Proof.
  set (handler := fun lr : I + R =>
    match lr with
    | inl i' => Tau (nested_program i')
    | inr r => Ret r
    end).
  eapply pstruct_trans.
  - apply observe_eq_pstruct.
    exact (observing_observe (unfold_aloop_ nested_step i)).
  - eapply pstruct_trans.
    + unfold nested_step.
      apply pstruct_bind_assoc.
    + eapply pstruct_bind.
      * intros a1 a2 ->. unfold handler.
        apply nested_ret_after_structural.
      * apply pstruct_refl.
Qed.

Lemma nested_program_hitting_unfold (fuel : nat) (i : I) :
  free_omega_lift eq
    (ptree_hitting_approx (MF := MF) fuel
      (observe (nested_program i)))
    (ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.bind sample (nested_after i)))).
Proof.
  apply ptree_hitting_pstruct_no_event.
  - exact no_event.
  - apply nested_program_unfold_structural.
Qed.

Definition no_event_head_value_for {X}
    (h : stable_head E MN X) : X :=
  match h with
  | FHRet x => x
  | @FHVis _ _ _ Y e _ => False_rect X (no_event e)
  end.

Definition no_event_head_value
    (h : stable_head E MN A) : A :=
  no_event_head_value_for h.

Lemma no_event_head_ret (h : stable_head E MN A) :
  exists a, h = FHRet a.
Proof.
  destruct h as [a|X e c].
  - exists a. reflexivity.
  - exfalso. exact (no_event e).
Qed.

Lemma omega_approx_monotone_nat {X}
    (chain : nat -> MF X)
    (Hstep : forall n, free_omega_approx eq (chain n) (chain (S n))) :
  forall n m, n <= m -> free_omega_approx eq (chain n) (chain m).
Proof.
  intros n m Hle. induction Hle.
  - apply free_omega_approx_refl. intros x. reflexivity.
  - eapply free_omega_approx_trans; [exact IHHle|apply Hstep].
Qed.

(** [outer] bounds how many completed sampler results may be consumed;
    [inner] bounds primitive execution inside every sampler invocation. *)
Fixpoint nested_execution_grid (outer inner : nat) (i : I) :
    MF (stable_head E MN R) :=
  match outer with
  | O => FOZero
  | Datatypes.S outer' =>
      free_omega_bind
        (ptree_hitting_approx (MF := MF) inner (observe sample))
        (fun h =>
          match round i (no_event_head_value h) with
          | inl i' => nested_execution_grid outer' inner i'
          | inr r => FORet (FHRet r)
          end)
  end.

(** Finite productivity data for a genuinely nested execution.  Unlike the
    earlier one-dimensional iteration certificate, the structured side has
    two independent budgets.  No finite budget is required to contain the
    complete AST sampler: every obligation compares only finite primitive
    execution with one finite grid cell.

    The schedules need not preserve indices.  This is essential because a
    global primitive budget is shared by all sampler invocations, whereas a
    grid cell grants its [inner] budget afresh in each of [outer] rounds. *)
Record nested_productivity_certificate (i : I) := {
  nested_ptree_to_grid_outer : nat -> nat;
  nested_ptree_to_grid_inner : nat -> nat;
  nested_grid_to_ptree_fuel : nat -> nat -> nat;
  nested_ptree_to_grid_sound : forall fuel,
    free_omega_approx eq
      (ptree_hitting_approx (MF := MF) fuel
        (observe (nested_program i)))
      (nested_execution_grid
        (nested_ptree_to_grid_outer fuel)
        (nested_ptree_to_grid_inner fuel) i);
  nested_grid_to_ptree_sound : forall outer inner,
    free_omega_approx eq
      (nested_execution_grid outer inner i)
      (ptree_hitting_approx (MF := MF)
        (nested_grid_to_ptree_fuel outer inner)
        (observe (nested_program i)))
}.

(** The corresponding row limit replaces the finite inner hitting chain by
    its complete AST output, while retaining finite outer fuel. *)
Fixpoint nested_row_out
    (sample_out : MF (stable_head E MN A))
    (outer : nat) (i : I) : MF (stable_head E MN R) :=
  match outer with
  | O => FOZero
  | Datatypes.S outer' =>
      free_omega_bind sample_out (fun h =>
        match round i (no_event_head_value h) with
        | inl i' => nested_row_out sample_out outer' i'
        | inr r => FORet (FHRet r)
        end)
  end.

(** Low-level finite-round meaning corresponding to [nested_row_out]. *)
Fixpoint nested_measure_row
    (sample_measure : MN A) (outer : nat) (i : I) : MN R :=
  match outer with
  | O => sem_zero
  | S outer' =>
      sem_bind sample_measure (fun a =>
        match round i a with
        | inl i' => nested_measure_row sample_measure outer' i'
        | inr r => sem_ret r
        end)
  end.

Section NestedRowDenotation.
Context `{DB : @FreeOmegaDenotationBindLaws MN NI NO}.

Lemma nested_row_out_denotes
    (sample_out : MF (stable_head E MN A))
    (sample_measure : MN A)
    (Hsample : free_omega_denotes
      (@no_event_head_value_for A)
      sample_out sample_measure) :
  forall outer i,
    free_omega_denotes
      (@no_event_head_value_for R)
      (nested_row_out sample_out outer i)
      (nested_measure_row sample_measure outer i).
Proof.
  induction outer as [|outer IH]; intro i.
  - apply free_omega_observes_denotes. constructor.
  - cbn [nested_row_out nested_measure_row].
    eapply free_omega_denotes_bind.
    + exact Hsample.
    + intro h. destruct (no_event_head_ret h) as [a ->].
      cbn [no_event_head_value no_event_head_value_for].
      destruct (round i a) as [i'|r].
      * apply IH.
      * apply free_omega_observes_denotes. constructor.
Qed.

End NestedRowDenotation.

Section NestedLimitDenotation.
Context `{DO : @FreeOmegaDenotationOmegaLaws MN NI NO}.

Lemma nested_row_out_increasing sample_out outer : forall i,
  free_omega_approx eq (nested_row_out sample_out outer i)
    (nested_row_out sample_out (S outer) i).
Proof.
  induction outer as [|outer IH]; intro i; cbn [nested_row_out].
  - apply FOApproxZero.
  - eapply free_omega_approx_bind with (R := eq).
    + apply free_omega_approx_refl. intro h. reflexivity.
    + intros h h' ->. destruct (round i (no_event_head_value h')) as [next|r].
      * apply IH.
      * apply FOApproxRet. reflexivity.
Qed.

Lemma nested_rows_lub_denotes
    (sample_out : MF (stable_head E MN A))
    (sample_measure : MN A)
    (Hrows : forall outer i,
      free_omega_denotes
        (@no_event_head_value_for R)
        (nested_row_out sample_out outer i)
        (nested_measure_row sample_measure outer i))
    (i : I) out :
  sem_lub (fun outer => nested_measure_row
      sample_measure outer i) out ->
  free_omega_denotes
    (@no_event_head_value_for R)
    (FOLub (fun outer => nested_row_out sample_out outer i)) out.
Proof.
  intro Hlub. eapply free_omega_denotes_lub.
  - intro outer. apply Hrows.
  - exact Hlub.
  - intro outer. apply nested_row_out_increasing.
Qed.

End NestedLimitDenotation.

Lemma nested_execution_grid_inner_increasing outer :
  forall i inner,
    free_omega_approx eq
      (nested_execution_grid outer inner i)
      (nested_execution_grid outer (Datatypes.S inner) i).
Proof.
  induction outer as [|outer IH]; intros i inner.
  - constructor.
  - cbn [nested_execution_grid].
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply ptree_hitting_mono. apply le_S, le_n.
    + intros h1 h2 ->.
      destruct (round i (no_event_head_value h2)) as [i'|r].
      * apply IH.
      * apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma canonical_nested_ptree_to_grid_sound fuel :
  forall i,
  free_omega_approx eq
    (ptree_hitting_approx (MF := MF) fuel
      (observe (nested_program i)))
    (nested_execution_grid (S fuel) fuel i).
Proof.
  induction fuel as [|fuel IH]; intro i.
  - eapply free_omega_approx_trans.
    + apply free_omega_lift_to_approx.
      apply nested_program_hitting_unfold.
    + eapply free_omega_approx_trans.
      * apply ptree_bind_hitting_le_diagonal.
      * unfold ptree_bind_diagonal_approx.
        cbn [nested_execution_grid].
        eapply free_omega_approx_bind with (R := eq) (T := eq).
        -- apply free_omega_approx_refl. intros h. reflexivity.
        -- intros h1 h2 ->.
           destruct (no_event_head_ret h2) as [a ->].
           cbn [ptree_head_bind_approx no_event_head_value
             no_event_head_value_for].
           unfold nested_after. destruct (round i a) as [i'|r].
           ++ cbn [ptree_hitting_approx ptree_primitive_kernel].
              constructor.
           ++ cbn [ptree_hitting_approx ptree_primitive_kernel].
              try rewrite stable_target_stableE.
              apply free_omega_approx_refl. intros x. reflexivity.
  - eapply free_omega_approx_trans.
    + apply free_omega_lift_to_approx.
      apply nested_program_hitting_unfold.
    + eapply free_omega_approx_trans.
      * apply ptree_bind_hitting_le_diagonal.
      * unfold ptree_bind_diagonal_approx.
        cbn [nested_execution_grid].
        eapply free_omega_approx_bind with (R := eq) (T := eq).
        -- apply free_omega_approx_refl. intros h. reflexivity.
        -- intros h1 h2 ->.
           destruct (no_event_head_ret h2) as [a ->].
           cbn [ptree_head_bind_approx no_event_head_value
             no_event_head_value_for].
           unfold nested_after. destruct (round i a) as [i'|r].
           ++ cbn [ptree_hitting_approx ptree_primitive_kernel].
              eapply free_omega_approx_trans.
              ** apply IH.
              ** apply omega_approx_monotone_nat with
                    (chain := fun inner =>
                      nested_execution_grid (S fuel) inner i').
                 --- intro inner.
                     apply nested_execution_grid_inner_increasing.
                 --- apply le_S, le_n.
           ++ cbn [ptree_hitting_approx ptree_primitive_kernel].
              try rewrite stable_target_stableE.
              apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma nested_execution_grid_outer_increasing inner :
  forall outer i,
    free_omega_approx eq
      (nested_execution_grid outer inner i)
      (nested_execution_grid (Datatypes.S outer) inner i).
Proof.
  induction outer as [|outer IH]; intro i.
  - constructor.
  - cbn [nested_execution_grid].
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply free_omega_approx_refl. intros h. reflexivity.
    + intros h1 h2 ->.
      destruct (round i (no_event_head_value h2)) as [i'|r].
      * apply IH.
      * apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Fixpoint nested_grid_ptree_fuel
    (outer inner : nat) : nat :=
  match outer with
  | O => O
  | S outer' => inner + S (nested_grid_ptree_fuel outer' inner)
  end.

Lemma canonical_nested_grid_to_ptree_sound outer :
  forall inner i,
  free_omega_approx eq
    (nested_execution_grid outer inner i)
    (ptree_hitting_approx (MF := MF)
      (nested_grid_ptree_fuel outer inner)
      (observe (nested_program i))).
Proof.
  induction outer as [|outer IH]; intros inner i.
  - constructor.
  - cbn [nested_execution_grid nested_grid_ptree_fuel].
    eapply free_omega_approx_trans with
      (nu := ptree_bind_split_approx inner
        (S (nested_grid_ptree_fuel outer inner))
        sample (nested_after i)).
    +
      unfold ptree_bind_split_approx.
      eapply free_omega_approx_bind with (R := eq) (T := eq).
      * apply free_omega_approx_refl. intros h. reflexivity.
      * intros h1 h2 ->.
        destruct (no_event_head_ret h2) as [a ->].
        cbn [no_event_head_value no_event_head_value_for
          ptree_head_bind_approx].
        unfold nested_after. destruct (round i a) as [i'|r].
        -- cbn [ptree_hitting_approx ptree_primitive_kernel].
           apply IH.
        -- cbn [ptree_hitting_approx ptree_primitive_kernel].
           try rewrite stable_target_stableE.
           apply free_omega_approx_refl. intros x. reflexivity.
    + eapply free_omega_approx_trans.
      * apply ptree_bind_split_le_hitting.
      * apply free_omega_lift_to_approx.
        eapply free_omega_lift_mono.
        -- intros x y Hyx. symmetry. exact Hyx.
        -- apply free_omega_lift_sym.
           apply nested_program_hitting_unfold.
Qed.

Theorem nested_productivity (i : I) :
  nested_productivity_certificate i.
Proof.
  refine {|
    nested_ptree_to_grid_outer := S;
    nested_ptree_to_grid_inner := fun fuel => fuel;
    nested_grid_to_ptree_fuel := nested_grid_ptree_fuel
  |}.
  - intro fuel. apply canonical_nested_ptree_to_grid_sound.
  - intros outer inner. apply canonical_nested_grid_to_ptree_sound.
Qed.

(** A finite productivity certificate is sufficient for the canonical
    program/grid omega-limit bridge.  Monotonicity in both grid coordinates
    moves arbitrary scheduled cells to the diagonal. *)
Theorem nested_productivity_diagonal_cofinal (i : I) :
  nested_productivity_certificate i ->
  @ptree_hitting_diagonal_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R
    (observe (nested_program i))
    (fun outer inner => nested_execution_grid outer inner i).
Proof.
  intro cert. intro out. apply free_omega_cofinal_lub_iff.
  { intro n. apply ptree_observable_hitting_increasing. }
  { intro n. eapply free_omega_approx_trans.
    - apply nested_execution_grid_inner_increasing.
    - apply nested_execution_grid_outer_increasing. }
  split.
  - intro fuel.
    set (outer := nested_ptree_to_grid_outer cert fuel).
    set (inner := nested_ptree_to_grid_inner cert fuel).
    exists (Nat.max outer inner).
    eapply free_omega_approx_trans.
    + exact (nested_ptree_to_grid_sound cert fuel).
    + eapply free_omega_approx_trans.
      * apply omega_approx_monotone_nat with
          (chain := fun n => nested_execution_grid n inner i).
        -- intros n. apply nested_execution_grid_outer_increasing.
        -- apply Nat.le_max_l.
      * apply omega_approx_monotone_nat with
          (chain := fun n => nested_execution_grid
            (Nat.max outer inner) n i).
        -- intros n. apply nested_execution_grid_inner_increasing.
        -- apply Nat.le_max_r.
  - intro diagonal.
    exists (nested_grid_to_ptree_fuel cert diagonal diagonal).
    eapply free_omega_approx_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + exact (nested_grid_to_ptree_sound cert diagonal diagonal).
Qed.

Corollary nested_program_diagonal_cofinal (i : I) :
  @ptree_hitting_diagonal_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R
    (observe (nested_program i))
    (fun outer inner => nested_execution_grid outer inner i).
Proof.
  apply nested_productivity_diagonal_cofinal.
  apply nested_productivity.
Qed.

Lemma nested_execution_grid_row_lub
    (sample_out : MF (stable_head E MN A))
    (Hsample : @ptree_stable_hitting E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega A
      (observe sample) sample_out) :
  forall outer i,
    @sem_lub MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega _
      (fun inner => nested_execution_grid outer inner i)
      (nested_row_out sample_out outer i).
Proof.
  induction outer as [|outer IH]; intro i.
  - cbn [nested_execution_grid nested_row_out].
    apply sem_lub_constant.
  - cbn [nested_execution_grid nested_row_out].
    change (@sem_lub MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega _
      (fun inner => @sem_bind MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        _ _ (ptree_hitting_approx (MF := MF) inner (observe sample))
        (fun h => match round i (no_event_head_value h) with
          | inl i' => nested_execution_grid outer inner i'
          | inr r => FORet (FHRet r)
          end))
      (@sem_bind MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        _ _ sample_out
        (fun h => match round i (no_event_head_value h) with
          | inl i' => nested_row_out sample_out outer i'
          | inr r => FORet (FHRet r)
          end))).
    eapply sem_bind_diagonal_lub.
    + apply (ptree_hitting_increasing
        (FI := FreeOmegaObservableSemanticMeasure)
        (MX := FreeOmegaMixedMeasure)
        (FO := FreeOmegaObservableSemanticOmega)).
    + intro h. destruct (round i (no_event_head_value h)) as [i'|r].
      * intro inner. apply nested_execution_grid_inner_increasing.
      * intro inner. apply free_omega_approx_refl. intros x. reflexivity.
    + exact Hsample.
    + intro h. destruct (round i (no_event_head_value h)) as [i'|r].
      * apply IH.
      * apply sem_lub_constant.
Qed.

Theorem nested_execution_grid_diagonal_lub
    (sample_out : MF (stable_head E MN A))
    (Hsample : @ptree_stable_hitting E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega A
      (observe sample) sample_out)
    (i : I) out :
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega _
    (fun outer => nested_row_out sample_out outer i) out ->
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega _
    (fun fuel => nested_execution_grid fuel fuel i) out.
Proof.
  intro Houter.
  refine (@sem_lub_double_diagonal MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega
    FreeOmegaObservableSemanticOmegaFubiniLaws (stable_head E MN R)
    (fun outer inner => nested_execution_grid outer inner i)
    (fun outer => nested_row_out sample_out outer i) out _ _ _ _).
  - intros outer inner. apply nested_execution_grid_inner_increasing.
  - intros inner outer. apply nested_execution_grid_outer_increasing.
  - intro outer. apply nested_execution_grid_row_lub. exact Hsample.
  - exact Houter.
Qed.

Theorem ptree_stable_hitting_of_nested_no_event_grid
    (program : ptree E MN R)
    (sample_out : MF (stable_head E MN A))
    (Hsample : @ptree_stable_hitting E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega A
      (observe sample) sample_out)
    (i : I) out :
  @ptree_hitting_diagonal_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R (observe program)
    (fun outer inner => nested_execution_grid outer inner i) ->
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega _
    (fun outer => nested_row_out sample_out outer i) out ->
  @ptree_stable_hitting E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R
    (observe program) out.
Proof.
  intros Hdiagonal Houter.
  eapply ptree_stable_hitting_of_nested_grid
    with (row_out := fun outer => nested_row_out sample_out outer i).
  - exact Hdiagonal.
  - intros outer inner. apply nested_execution_grid_inner_increasing.
  - intros inner outer. apply nested_execution_grid_outer_increasing.
  - intro outer. apply nested_execution_grid_row_lub. exact Hsample.
  - exact Houter.
Qed.

(** User-facing form for the canonical nested program: the example supplies
    only finite productivity schedules and the outer probabilistic limit. *)
Corollary ptree_stable_hitting_of_nested_productivity
    (sample_out : MF (stable_head E MN A))
    (Hsample : @ptree_stable_hitting E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega A
      (observe sample) sample_out)
    (i : I) out :
  nested_productivity_certificate i ->
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega _
    (fun outer => nested_row_out sample_out outer i) out ->
  @ptree_stable_hitting E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R
    (observe (nested_program i)) out.
Proof.
  intros Hproductivity Houter.
  eapply ptree_stable_hitting_of_nested_no_event_grid.
  - exact Hsample.
  - exact (nested_productivity_diagonal_cofinal Hproductivity).
  - exact Houter.
Qed.

Corollary ptree_stable_hitting_ast_of_nested_productivity
    (sample_out : MF (stable_head E MN A))
    (Hsample : @ptree_stable_hitting E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega A
      (observe sample) sample_out)
    (i : I) out :
  nested_productivity_certificate i ->
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega _
    (fun outer => nested_row_out sample_out outer i) out ->
  @sem_total MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega _ out ->
  @ptree_stable_hitting_ast E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R
    (observe (nested_program i)) out.
Proof.
  intros Hproductivity Houter Htotal. split; [|exact Htotal].
  eapply ptree_stable_hitting_of_nested_productivity; eassumption.
Qed.

Corollary ptree_stable_hitting_of_canonical_nested
    (sample_out : MF (stable_head E MN A))
    (Hsample : @ptree_stable_hitting E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega A
      (observe sample) sample_out)
    (i : I) out :
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega _
    (fun outer => nested_row_out sample_out outer i) out ->
  @ptree_stable_hitting E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R
    (observe (nested_program i)) out.
Proof.
  intro Houter. eapply ptree_stable_hitting_of_nested_productivity.
  - exact Hsample.
  - apply nested_productivity.
  - exact Houter.
Qed.

Corollary ptree_stable_hitting_ast_of_canonical_nested
    (sample_out : MF (stable_head E MN A))
    (Hsample : @ptree_stable_hitting E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega A
      (observe sample) sample_out)
    (i : I) out :
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega _
    (fun outer => nested_row_out sample_out outer i) out ->
  @sem_total MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega _ out ->
  @ptree_stable_hitting_ast E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R
    (observe (nested_program i)) out.
Proof.
  intros Houter Htotal. split; [|exact Htotal].
  eapply ptree_stable_hitting_of_canonical_nested; eassumption.
Qed.

End NestedNoEventGrid.

Lemma ptree_bind_vis_approx_cofinal {A R X}
    (e : E X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) :
  ptree_bind_approx_cofinal (Vis e c) k.
Proof.
  split; intro n; exists n;
    unfold ptree_bind_approx_cofinal,
      ptree_bind_diagonal_approx,
      ptree_head_bind_approx,
      ptree_hitting_approx, ptree_primitive_kernel;
    cbn.
  all: rewrite !stable_target_stableE; cbn.
  all: apply free_omega_approx_refl; intros x; reflexivity.
Qed.

Corollary ptree_bind_vis_cofinal {A R X}
    (e : E X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) :
  @PTreeKernel.ptree_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A R (Vis e c) k.
Proof.
  apply ptree_bind_cofinal.
  apply ptree_bind_vis_approx_cofinal.
Qed.

Lemma ptree_bind_tau_diagonal_left {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) n :
  free_omega_approx eq
    (ptree_bind_diagonal_approx (MF := MF) n t k)
    (ptree_bind_diagonal_approx (MF := MF)
      (Datatypes.S n) (Tau t) k).
Proof.
  change (free_omega_approx eq
    (free_omega_bind
      (ptree_hitting_approx (MF := MF) n (observe t))
      (ptree_head_bind_approx (MF := MF) n k))
    (free_omega_bind
      (ptree_hitting_approx (MF := MF) n (observe t))
      (ptree_head_bind_approx (MF := MF) (Datatypes.S n) k))).
  eapply free_omega_approx_bind with (R := eq) (T := eq).
  - apply free_omega_approx_refl. intros x. reflexivity.
  - intros h1 h2 ->. destruct h2 as [a|X e c];
      cbn [ptree_head_bind_approx].
    + apply ptree_hitting_mono.
      apply le_S. apply le_n.
    + apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma ptree_bind_tau_diagonal_right {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) n :
  free_omega_approx eq
    (ptree_bind_diagonal_approx (MF := MF)
      (Datatypes.S n) (Tau t) k)
    (ptree_bind_diagonal_approx (MF := MF)
      (Datatypes.S n) t k).
Proof.
  change (free_omega_approx eq
    (free_omega_bind
      (ptree_hitting_approx (MF := MF) n (observe t))
      (ptree_head_bind_approx (MF := MF) (Datatypes.S n) k))
    (free_omega_bind
      (ptree_hitting_approx (MF := MF) (Datatypes.S n) (observe t))
      (ptree_head_bind_approx (MF := MF) (Datatypes.S n) k))).
  eapply free_omega_approx_bind with (R := eq) (T := eq).
  - apply ptree_hitting_mono.
    apply le_S. apply le_n.
  - intros h1 h2 ->. apply free_omega_approx_refl.
    intros x. reflexivity.
Qed.

Lemma ptree_bind_tau_approx_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  ptree_bind_approx_cofinal t k ->
  ptree_bind_approx_cofinal (Tau t) k.
Proof.
  intros [Hglobal Hdiagonal]. split.
  - intros [|n].
    + exists 0. unfold ptree_bind_diagonal_approx,
        ptree_hitting_approx, ptree_primitive_kernel. cbn.
      apply free_omega_approx_refl. intros x. reflexivity.
    + destruct (Hglobal n) as [m Hm]. exists (Datatypes.S m).
      rewrite observe_bind. cbn [ptree_hitting_approx ptree_primitive_kernel].
      eapply free_omega_approx_trans; [exact Hm|].
      apply ptree_bind_tau_diagonal_left.
  - intros [|m].
    + exists 0. unfold ptree_bind_diagonal_approx,
        ptree_hitting_approx, ptree_primitive_kernel. cbn.
      apply free_omega_approx_refl. intros x. reflexivity.
    + destruct (Hdiagonal (Datatypes.S m)) as [n Hn].
      exists (Datatypes.S n).
      change (free_omega_approx (fun y x => x = y)
        (ptree_bind_diagonal_approx (MF := MF)
          (Datatypes.S m) (Tau t) k)
        (ptree_hitting_approx (MF := MF) n
          (observe (PTree.bind t k)))).
      eapply free_omega_approx_mono with (R := eq).
      * intros x y Hxy. symmetry. exact Hxy.
      * eapply free_omega_approx_trans.
        -- apply ptree_bind_tau_diagonal_right.
        -- eapply free_omega_approx_mono; [|exact Hn].
           intros x y Hyx. symmetry. exact Hyx.
Qed.

Corollary ptree_bind_tau_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  ptree_bind_approx_cofinal t k ->
  @PTreeKernel.ptree_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A R (Tau t) k.
Proof.
  intro Hcofinal. apply ptree_bind_cofinal.
  exact (ptree_bind_tau_approx_cofinal Hcofinal).
Qed.

(** Prob requires a genuinely stronger productivity condition than pointwise
    branch cofinality: each outer approximant needs one fuel bound that works
    almost everywhere for the sampled branches.  Finite Enum support can
    obtain such a bound by taking a maximum; arbitrary measures must provide
    it analytically. *)
Definition ptree_bind_prob_uniform {A R X}
    (mu : MN X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) : Prop :=
  (forall n, exists m Good,
      sem_ae mu Good /\
      forall x, Good x -> free_omega_approx eq
        (ptree_hitting_approx (MF := MF) n
          (observe (PTree.bind (c x) k)))
        (ptree_bind_diagonal_approx (MF := MF) m (c x) k)) /\
  (forall m, exists n Good,
      sem_ae mu Good /\
      forall x, Good x -> free_omega_approx eq
        (ptree_bind_diagonal_approx (MF := MF) m (c x) k)
        (ptree_hitting_approx (MF := MF) n
          (observe (PTree.bind (c x) k)))).

Lemma ptree_bind_prob_approx_cofinal {A R X}
    (mu : MN X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) :
  ptree_bind_prob_uniform mu c k ->
  ptree_bind_approx_cofinal (Prob mu c) k.
Proof.
  intros [Hglobal Hdiagonal]. split.
  - intros [|n].
    + exists 0. unfold ptree_bind_diagonal_approx,
        ptree_hitting_approx, ptree_primitive_kernel. cbn.
      apply free_omega_approx_refl. intros x. reflexivity.
    + destruct (Hglobal n) as [m [Good [Hae Hbranches]]].
      exists (Datatypes.S m).
      rewrite observe_bind. cbn [ptree_hitting_approx ptree_primitive_kernel].
      eapply FOApproxSample with
        (S := fun x y => x = y /\ Good x).
      * apply sem_lift_refl_ae. exact Hae.
      * intros x y [-> Hgood].
        eapply free_omega_approx_trans.
        -- exact (Hbranches y Hgood).
        -- apply ptree_bind_tau_diagonal_left.
  - intros [|m].
    + exists 0. unfold ptree_bind_diagonal_approx,
        ptree_hitting_approx, ptree_primitive_kernel. cbn.
      apply free_omega_approx_refl. intros x. reflexivity.
    + destruct (Hdiagonal (Datatypes.S m))
        as [n [Good [Hae Hbranches]]].
      exists (Datatypes.S n).
      rewrite observe_bind. cbn [ptree_hitting_approx ptree_primitive_kernel].
      eapply free_omega_approx_mono with (R := eq).
      * intros x y Hxy. symmetry. exact Hxy.
      * eapply FOApproxSample with
          (S := fun x y => x = y /\ Good x).
        -- apply sem_lift_refl_ae. exact Hae.
        -- intros x y [-> Hgood].
           eapply free_omega_approx_trans.
           ++ apply ptree_bind_tau_diagonal_right.
           ++ exact (Hbranches y Hgood).
Qed.

Corollary ptree_bind_prob_cofinal {A R X}
    (mu : MN X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) :
  ptree_bind_prob_uniform mu c k ->
  @PTreeKernel.ptree_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A R (Prob mu c) k.
Proof.
  intro Huniform. apply ptree_bind_cofinal.
  exact (ptree_bind_prob_approx_cofinal Huniform).
Qed.

(** A two-dimensional primitive-execution model for an iterator whose individual
    state-indexed steps may themselves have unbounded running time.  The
    first coordinate bounds completed iterator rounds; the second bounds
    primitive execution inside every step.  Unlike [nested_program],
    this construction consumes the client's actual [step] directly, so no
    bind reassociation or [pstruct] normalization is involved. *)
Section DirectUnboundedIteration.
Context {I R : Type}.
Context `{NCAEIter : @SemanticMeasureCouplingAELaws MN NI}.
Context `{NCountAEIter : @SemanticMeasureCountableAELaws MN NI}.
Variable no_event : forall X, E X -> False.
Variable step : I -> ptree E MN (I + R).

Definition iter_after (next : I + R) : ptree E MN R :=
  match next with
  | inl j => Tau (PTree.iter step j)
  | inr r => Ret r
  end.

Lemma iter_program_observe i :
  observe (PTree.iter step i) =
  observe (PTree.bind (step i) iter_after).
Proof.
  pose proof (unfold_aloop_ step i) as Hunfold.
  rewrite (observing_observe Hunfold), observe_bind. reflexivity.
Qed.

Definition iter_head_next
    (h : stable_head E MN (I + R)) : I + R :=
  match h with
  | FHRet next => next
  | @FHVis _ _ _ X e k => False_rect _ (no_event e)
  end.

Definition iter_result_value
    (h : stable_head E MN R) : R :=
  match h with
  | FHRet r => r
  | @FHVis _ _ _ X e k => False_rect _ (no_event e)
  end.

Fixpoint iter_execution_grid (rounds inner : nat) (i : I) :
    MF (stable_head E MN R) :=
  match rounds with
  | O => FOZero
  | S rounds' =>
      free_omega_bind
        (ptree_hitting_approx (MF := MF) inner (observe (step i)))
        (fun h =>
          match iter_head_next h with
          | inl j => iter_execution_grid rounds' inner j
          | inr r => FORet (FHRet r)
          end)
  end.

Lemma iter_head_ret (h : stable_head E MN (I + R)) :
  exists next, h = FHRet next.
Proof.
  destruct h as [next|X e k].
  - exists next. reflexivity.
  - exfalso. exact (no_event e).
Qed.

Lemma iter_execution_grid_inner_increasing rounds :
  forall inner i,
    free_omega_approx eq
      (iter_execution_grid rounds inner i)
      (iter_execution_grid rounds (S inner) i).
Proof.
  induction rounds as [|rounds IH]; intros inner i.
  - constructor.
  - cbn [iter_execution_grid].
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply ptree_hitting_mono. apply le_S, le_n.
    + intros h1 h2 ->.
      destruct (iter_head_next h2) as [j|r].
      * apply IH.
      * apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma iter_execution_grid_outer_increasing inner :
  forall rounds i,
    free_omega_approx eq
      (iter_execution_grid rounds inner i)
      (iter_execution_grid (S rounds) inner i).
Proof.
  induction rounds as [|rounds IH]; intro i.
  - constructor.
  - cbn [iter_execution_grid].
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply free_omega_approx_refl. intros h. reflexivity.
    + intros h1 h2 ->.
      destruct (iter_head_next h2) as [j|r].
      * apply IH.
      * apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma iter_ptree_to_grid_sound fuel : forall i,
  free_omega_approx eq
    (ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.iter step i)))
    (iter_execution_grid (S fuel) fuel i).
Proof.
  induction fuel as [|fuel IH]; intro i.
  - rewrite iter_program_observe.
    eapply free_omega_approx_trans.
    + apply ptree_bind_hitting_le_diagonal.
    + unfold ptree_bind_diagonal_approx.
      cbn [iter_execution_grid].
      eapply free_omega_approx_bind with (R := eq) (T := eq).
      * apply free_omega_approx_refl. intros h. reflexivity.
      * intros h1 h2 ->.
        destruct (iter_head_ret h2) as [next ->].
        cbn [ptree_head_bind_approx iter_head_next].
        destruct next as [j|r].
        -- cbn [ptree_hitting_approx ptree_primitive_kernel]. constructor.
        -- cbn [ptree_hitting_approx ptree_primitive_kernel].
           try rewrite stable_target_stableE.
           apply free_omega_approx_refl. intros x. reflexivity.
  - rewrite iter_program_observe.
    eapply free_omega_approx_trans.
    + apply ptree_bind_hitting_le_diagonal.
    + unfold ptree_bind_diagonal_approx.
      cbn [iter_execution_grid].
      eapply free_omega_approx_bind with (R := eq) (T := eq).
      * apply free_omega_approx_refl. intros h. reflexivity.
      * intros h1 h2 ->.
        destruct (iter_head_ret h2) as [next ->].
        cbn [ptree_head_bind_approx iter_head_next].
        destruct next as [j|r].
        -- cbn [ptree_hitting_approx ptree_primitive_kernel].
           eapply free_omega_approx_trans.
           ++ apply IH.
           ++ apply omega_approx_monotone_nat with
                (chain := fun inner =>
                  iter_execution_grid (S fuel) inner j).
              ** intro inner.
                 apply iter_execution_grid_inner_increasing.
              ** apply le_S, le_n.
        -- cbn [ptree_hitting_approx ptree_primitive_kernel].
           try rewrite stable_target_stableE.
           apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Fixpoint iter_grid_ptree_fuel
    (rounds inner : nat) : nat :=
  match rounds with
  | O => O
  | S rounds' => inner + S (iter_grid_ptree_fuel rounds' inner)
  end.

Lemma iter_grid_to_ptree_sound rounds : forall inner i,
  free_omega_approx eq
    (iter_execution_grid rounds inner i)
    (ptree_hitting_approx (MF := MF)
      (iter_grid_ptree_fuel rounds inner)
      (observe (PTree.iter step i))).
Proof.
  induction rounds as [|rounds IH]; intros inner i.
  - constructor.
  - cbn [iter_execution_grid iter_grid_ptree_fuel].
    rewrite iter_program_observe.
    eapply free_omega_approx_trans with
      (nu := ptree_bind_split_approx inner
        (S (iter_grid_ptree_fuel rounds inner))
        (step i) iter_after).
    + unfold ptree_bind_split_approx.
      eapply free_omega_approx_bind with (R := eq) (T := eq).
      * apply free_omega_approx_refl. intros h. reflexivity.
      * intros h1 h2 ->.
        destruct (iter_head_ret h2) as [next ->].
        cbn [iter_head_next ptree_head_bind_approx].
        destruct next as [j|r].
        -- cbn [ptree_hitting_approx ptree_primitive_kernel]. apply IH.
        -- cbn [ptree_hitting_approx ptree_primitive_kernel].
           try rewrite stable_target_stableE.
           apply free_omega_approx_refl. intros x. reflexivity.
    + apply ptree_bind_split_le_hitting.
Qed.

Record iter_diagonal_productivity_certificate (i : I) := {
  iter_ptree_to_grid : forall fuel,
    free_omega_approx eq
      (ptree_hitting_approx (MF := MF) fuel
        (observe (PTree.iter step i)))
      (iter_execution_grid (S fuel) fuel i);
  iter_grid_to_ptree_fuel : forall rounds inner,
    free_omega_approx eq
      (iter_execution_grid rounds inner i)
      (ptree_hitting_approx (MF := MF)
        (iter_grid_ptree_fuel rounds inner)
        (observe (PTree.iter step i)))
}.

Theorem iter_diagonal_productivity i :
  iter_diagonal_productivity_certificate i.
Proof.
  constructor.
  - intro fuel. exact (iter_ptree_to_grid_sound fuel i).
  - intros rounds inner.
    exact (iter_grid_to_ptree_sound rounds inner i).
Qed.

Theorem iter_grid_diagonal_cofinal i :
  @ptree_hitting_diagonal_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R
    (observe (PTree.iter step i))
    (fun rounds inner => iter_execution_grid rounds inner i).
Proof.
  intro out. apply free_omega_cofinal_lub_iff.
  { intro n. apply ptree_observable_hitting_increasing. }
  { intro n. eapply free_omega_approx_trans.
    - apply iter_execution_grid_inner_increasing.
    - apply iter_execution_grid_outer_increasing. }
  split.
  - intro fuel. exists (S fuel).
    eapply free_omega_approx_trans.
    + apply iter_ptree_to_grid_sound.
    + apply omega_approx_monotone_nat with
        (chain := fun inner => iter_execution_grid (S fuel) inner i).
      * intro inner. apply iter_execution_grid_inner_increasing.
      * apply le_S, le_n.
  - intro diagonal.
    exists (iter_grid_ptree_fuel diagonal diagonal).
    eapply free_omega_approx_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + apply iter_grid_to_ptree_sound.
Qed.

Variable step_out : I -> MF (stable_head E MN (I + R)).

Fixpoint iter_complete_rows (rounds : nat) (i : I) :
    MF (stable_head E MN R) :=
  match rounds with
  | O => FOZero
  | S rounds' =>
      free_omega_bind (step_out i) (fun h =>
        match iter_head_next h with
        | inl j => iter_complete_rows rounds' j
        | inr r => FORet (FHRet r)
        end)
  end.

Lemma iter_execution_grid_row_lub
    (Hstep : forall i,
      @ptree_stable_hitting E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega (I + R)
        (observe (step i)) (step_out i)) :
  forall rounds i,
    @sem_lub MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega _
      (fun inner => iter_execution_grid rounds inner i)
      (iter_complete_rows rounds i).
Proof.
  induction rounds as [|rounds IH]; intro i.
  - cbn [iter_execution_grid iter_complete_rows].
    apply sem_lub_constant.
  - cbn [iter_execution_grid iter_complete_rows].
    change (@sem_lub MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega _
      (fun inner => @sem_bind MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        _ _ (ptree_hitting_approx (MF := MF) inner (observe (step i)))
        (fun h => match iter_head_next h with
          | inl j => iter_execution_grid rounds inner j
          | inr r => FORet (FHRet r)
          end))
      (@sem_bind MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        _ _ (step_out i)
        (fun h => match iter_head_next h with
          | inl j => iter_complete_rows rounds j
          | inr r => FORet (FHRet r)
          end))).
    eapply sem_bind_diagonal_lub.
    + apply (ptree_hitting_increasing
        (FI := FreeOmegaObservableSemanticMeasure)
        (MX := FreeOmegaMixedMeasure)
        (FO := FreeOmegaObservableSemanticOmega)).
    + intro h. destruct (iter_head_next h) as [j|r].
      * intro inner. apply iter_execution_grid_inner_increasing.
      * intro inner. apply free_omega_approx_refl. intros x. reflexivity.
    + apply Hstep.
    + intro h. destruct (iter_head_next h) as [j|r].
      * apply IH.
      * apply sem_lub_constant.
Qed.

Theorem iter_execution_grid_diagonal_lub
    (Hstep : forall i,
      @ptree_stable_hitting E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega (I + R)
        (observe (step i)) (step_out i))
    (i : I) out :
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega _
    (fun rounds => iter_complete_rows rounds i) out ->
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega _
    (fun fuel => iter_execution_grid fuel fuel i) out.
Proof.
  intro Hrows.
  refine (@sem_lub_double_diagonal MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega
    FreeOmegaObservableSemanticOmegaFubiniLaws (stable_head E MN R)
    (fun rounds inner => iter_execution_grid rounds inner i)
    (fun rounds => iter_complete_rows rounds i) out _ _ _ _).
  - intros rounds inner. apply iter_execution_grid_inner_increasing.
  - intros inner rounds. apply iter_execution_grid_outer_increasing.
  - intro rounds. apply iter_execution_grid_row_lub. exact Hstep.
  - exact Hrows.
Qed.

Theorem ptree_stable_hitting_iter_of_unbounded_steps
    (Hstep : forall i,
      @ptree_stable_hitting E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega (I + R)
        (observe (step i)) (step_out i))
    (i : I) out :
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega _
    (fun rounds => iter_complete_rows rounds i) out ->
  @ptree_stable_hitting E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R
    (observe (PTree.iter step i)) out.
Proof.
  intro Hrounds. unfold ptree_stable_hitting.
  apply (proj2 (iter_grid_diagonal_cofinal i out)).
  apply iter_execution_grid_diagonal_lub; assumption.
Qed.

Section DirectUnboundedIterationDenotation.
Context `{DB : @FreeOmegaDenotationBindLaws MN NI NO}.
Variable transition : I -> MN (I + R).

Fixpoint iter_measure_rows (rounds : nat) (i : I) : MN R :=
  match rounds with
  | O => sem_zero
  | S rounds' => sem_bind (transition i) (fun next =>
      match next with
      | inl j => iter_measure_rows rounds' j
      | inr r => sem_ret r
      end)
  end.

Lemma iter_complete_rows_denotes
    (Hstep : forall i,
      free_omega_denotes iter_head_next (step_out i) (transition i)) :
  forall rounds i,
      free_omega_denotes iter_result_value
      (iter_complete_rows rounds i)
      (iter_measure_rows rounds i).
Proof.
  induction rounds as [|rounds IH]; intro i.
  - apply free_omega_observes_denotes. constructor.
  - cbn [iter_complete_rows iter_measure_rows].
    eapply free_omega_denotes_bind.
    + apply Hstep.
    + intro h. destruct (iter_head_ret h) as [next ->].
      cbn [iter_head_next]. destruct next as [j|r].
      * apply IH.
      * apply free_omega_observes_denotes. constructor.
Qed.

End DirectUnboundedIterationDenotation.

Section DirectUnboundedIterationLimitDenotation.
Context `{DO : @FreeOmegaDenotationOmegaLaws MN NI NO}.
Variable transition : I -> MN (I + R).

Lemma iter_complete_limit_denotes
    (Hrows : forall rounds i,
      free_omega_denotes iter_result_value
        (iter_complete_rows rounds i)
        (iter_measure_rows transition rounds i))
    (i : I) out :
  sem_lub (fun rounds => iter_measure_rows transition rounds i) out ->
  free_omega_denotes iter_result_value
    (FOLub (fun rounds => iter_complete_rows rounds i)) out.
Proof.
  intro Hlub. eapply free_omega_denotes_lub.
  - intro rounds. apply Hrows.
  - exact Hlub.
  - intro rounds. clear Hlub. revert i. induction rounds as [|rounds IH]; intro i;
      cbn [iter_complete_rows].
    + apply FOApproxZero.
    + eapply free_omega_approx_bind with (R := eq).
      * apply free_omega_approx_refl. intro h. reflexivity.
      * intros h h' ->. destruct (iter_head_next h') as [next|r].
        -- apply IH.
        -- apply FOApproxRet. reflexivity.
Qed.

End DirectUnboundedIterationLimitDenotation.

End DirectUnboundedIteration.

(** The analogous finite obligation for iteration rounds.  This is where
    bounded cost/productivity proofs for concrete samplers belong. *)
Definition ptree_iter_approx_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) : Prop :=
  free_omega_chains_cofinal eq
    (fun fuel => ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.iter step i)))
    (fun rounds => ptree_iter_round_approx (MF := MF)
      rounds transition i).

(** Finite, proof-relevant productivity data for bounded-cost iterations.
    A certificate does more than
    assert equality of two omega limits: it exhibits how much structured
    round fuel is sufficient for each primitive fuel, and conversely.
    This is deliberately only a sufficient condition.  A genuinely
    unbounded nested sampler generally cannot provide the reverse finite
    schedule: no finite inner fuel contains its complete AST output measure.
    Such programs require diagonal/Fubini continuity of the two omega
    limits, rather than a maximum finite fuel. *)
Record ptree_iter_productivity_certificate {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) := {
  ptree_to_round_schedule : nat -> nat;
  round_to_ptree_schedule : nat -> nat;
  ptree_to_round_sound : forall fuel,
    free_omega_approx eq
      (ptree_hitting_approx (MF := MF) fuel
        (observe (PTree.iter step i)))
      (ptree_iter_round_approx (MF := MF)
        (ptree_to_round_schedule fuel) transition i);
  round_to_ptree_sound : forall rounds,
    free_omega_approx (fun y x => x = y)
      (ptree_iter_round_approx (MF := MF) rounds transition i)
      (ptree_hitting_approx (MF := MF)
        (round_to_ptree_schedule rounds)
        (observe (PTree.iter step i)))
}.

Lemma ptree_iter_certificate_approx_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) :
  ptree_iter_productivity_certificate step transition i ->
  ptree_iter_approx_cofinal step transition i.
Proof.
  intros cert. split.
  - intro fuel. exists (ptree_to_round_schedule cert fuel).
    exact (ptree_to_round_sound cert fuel).
  - intro rounds. exists (round_to_ptree_schedule cert rounds).
    exact (round_to_ptree_sound cert rounds).
Qed.

Lemma ptree_iter_round_increasing {I R}
    (transition : I -> MN (I + R)) n i :
  free_omega_approx eq
    (@ptree_iter_round_approx E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega I R n transition i)
    (@ptree_iter_round_approx E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega I R (S n) transition i).
Proof.
  unfold ptree_iter_round_approx.
  apply free_omega_approx_bind with (R := eq).
  - induction n as [|n IH] in i |- *.
    + constructor.
    + cbn [mixed_iter_approx]. apply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intros x. reflexivity.
      * intros [j|r] y <-.
        -- apply IH.
        -- apply free_omega_approx_refl. intros x. reflexivity.
  - intros x y ->. apply free_omega_approx_refl. intros h. reflexivity.
Qed.

Corollary ptree_iter_certificate_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) :
  ptree_iter_productivity_certificate step transition i ->
  @PTreeKernel.ptree_iter_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega I R step transition i.
Proof.
  intros cert out. unfold PTreeKernel.ptree_iter_cofinal.
  apply free_omega_cofinal_lub_iff.
  - intro n. apply ptree_observable_hitting_increasing.
  - intro n. apply ptree_iter_round_increasing.
  - exact (ptree_iter_certificate_approx_cofinal cert).
Qed.

(** A primitive Markov step has a uniform syntactic cost: one probabilistic
    node followed by the silent back-edge inserted by [PTree.iter].  Hence
    its global stable-hitting chain and its absorbing-round chain are
    cofinal.  This theorem is entirely semantic; no frontier-certificate derivation
    or iteration constructor occurs in its assumptions. *)
Section PrimitiveProbIteration.
Context {I R : Type} (transition : I -> MN (I + R)).

Definition primitive_iter_step (i : I) : ptree E MN (I + R) :=
  Prob (transition i) (fun next => Ret next).

Definition primitive_iter_program (i : I) : ptree E MN R :=
  PTree.iter primitive_iter_step i.

Definition primitive_iter_hitting (fuel : nat) (i : I) :
    MF (stable_head E MN R) :=
  ptree_hitting_approx (MF := MF) fuel
    (observe (primitive_iter_program i)).

Definition primitive_iter_rounds (rounds : nat) (i : I) :
    MF (stable_head E MN R) :=
  ptree_iter_round_approx (MF := MF) rounds transition i.

Definition primitive_iter_after (next : I + R) : ptree E MN R :=
  match next with
  | inl j => Tau (primitive_iter_program j)
  | inr r => Ret r
  end.

Definition primitive_iter_cont (next : I + R) : ptree E MN R :=
  PTree.bind (Ret next) (fun lr =>
    match lr with
    | inl j => Tau (primitive_iter_program j)
    | inr r => Ret r
    end).

Lemma primitive_iter_observe i :
  observe (primitive_iter_program i) =
  ProbF (transition i) primitive_iter_cont.
Proof.
  unfold primitive_iter_program.
  pose proof (unfold_aloop_ primitive_iter_step i) as Hunfold.
  rewrite (observing_observe Hunfold), observe_bind.
  assert (Hstep : observe (primitive_iter_step i) =
    ProbF (transition i) (fun next => Ret next)) by reflexivity.
  rewrite Hstep. reflexivity.
Qed.

Lemma primitive_iter_cont_observe next :
  observe (primitive_iter_cont next) =
  observe (primitive_iter_after next).
Proof.
  unfold primitive_iter_cont. rewrite observe_bind.
  destruct next as [j|r]; reflexivity.
Qed.

Lemma primitive_iter_rounds_zero i :
  primitive_iter_rounds 0 i = FOZero.
Proof. reflexivity. Qed.

Lemma primitive_iter_rounds_succ rounds i :
  primitive_iter_rounds (Datatypes.S rounds) i =
  FOSample (transition i) (fun next =>
    match next with
    | inl j => primitive_iter_rounds rounds j
    | inr r => FORet (FHRet r)
    end).
Proof.
  unfold primitive_iter_rounds, ptree_iter_round_approx.
  cbv [mixed_iter_approx sem_bind mixed_bind sem_ret free_omega_bind
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticMeasure
    FreeOmegaSemanticMeasure].
  f_equal. apply functional_extensionality. intros [j|r]; reflexivity.
Qed.

Lemma primitive_iter_hitting_succ fuel i :
  primitive_iter_hitting (Datatypes.S fuel) i =
  FOSample (transition i) (fun next =>
    ptree_hitting_approx (MF := MF) fuel
      (observe (primitive_iter_cont next))).
Proof.
  unfold primitive_iter_hitting. rewrite primitive_iter_observe.
  reflexivity.
Qed.

Lemma primitive_iter_retry_zero j :
  ptree_hitting_approx (MF := MF) 0
    (observe (primitive_iter_cont (inl j))) = FOZero.
Proof. reflexivity. Qed.

Lemma primitive_iter_retry_succ fuel j :
  ptree_hitting_approx (MF := MF) (Datatypes.S fuel)
    (observe (primitive_iter_cont (inl j))) =
  primitive_iter_hitting fuel j.
Proof.
  rewrite primitive_iter_cont_observe. reflexivity.
Qed.

Lemma primitive_iter_success fuel r :
  ptree_hitting_approx (MF := MF) fuel
    (observe (primitive_iter_cont (inr r))) = FORet (FHRet r).
Proof.
  rewrite primitive_iter_cont_observe.
  unfold primitive_iter_after, ptree_hitting_approx,
    ptree_primitive_kernel. cbn. rewrite stable_target_stableE.
  reflexivity.
Qed.

Lemma primitive_iter_hitting_le_round fuel :
  forall i, free_omega_approx eq
    (primitive_iter_hitting fuel i)
    (primitive_iter_rounds (Datatypes.S fuel) i).
Proof.
  induction fuel as [|fuel IH]; intro i.
  - rewrite primitive_iter_rounds_succ.
    unfold primitive_iter_hitting. rewrite primitive_iter_observe.
    unfold ptree_hitting_approx, ptree_primitive_kernel. cbn.
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. destruct y as [j|r]; constructor.
  - rewrite primitive_iter_hitting_succ,
      primitive_iter_rounds_succ.
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. destruct y as [j|r].
      * eapply free_omega_approx_trans with
          (nu := primitive_iter_hitting fuel j).
        -- destruct fuel as [|fuel].
           ++ constructor.
           ++ rewrite primitive_iter_retry_succ.
              apply ptree_hitting_mono.
              apply le_S. apply le_n.
        -- apply IH.
      * rewrite primitive_iter_success.
        apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma primitive_iter_round_le_hitting rounds :
  forall i, free_omega_approx eq
    (primitive_iter_rounds rounds i)
    (primitive_iter_hitting (2 * rounds) i).
Proof.
  induction rounds as [|rounds IH]; intro i.
  - rewrite primitive_iter_rounds_zero. constructor.
  - rewrite primitive_iter_rounds_succ.
    replace (2 * Datatypes.S rounds) with
      (Datatypes.S (Datatypes.S (2 * rounds))) by lia.
    rewrite primitive_iter_hitting_succ.
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. destruct y as [j|r].
      * rewrite primitive_iter_retry_succ. apply IH.
      * rewrite primitive_iter_success.
        apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Theorem primitive_iter_productivity i :
  ptree_iter_productivity_certificate
    primitive_iter_step transition i.
Proof.
  refine {| ptree_to_round_schedule := Datatypes.S;
    round_to_ptree_schedule := fun rounds => 2 * rounds |}.
  - intro fuel. exact (primitive_iter_hitting_le_round fuel i).
  - intro rounds. eapply free_omega_approx_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + exact (primitive_iter_round_le_hitting rounds i).
Qed.

Corollary primitive_iter_approx_cofinal i :
  ptree_iter_approx_cofinal
    primitive_iter_step transition i.
Proof.
  apply ptree_iter_certificate_approx_cofinal.
  exact (primitive_iter_productivity i).
Qed.

Corollary primitive_iter_cofinal i :
  @PTreeKernel.ptree_iter_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega I R
    primitive_iter_step transition i.
Proof.
  apply ptree_iter_certificate_cofinal.
  exact (primitive_iter_productivity i).
Qed.

End PrimitiveProbIteration.

Theorem ptree_iter_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) :
  ptree_iter_approx_cofinal step transition i ->
  @PTreeKernel.ptree_iter_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega I R step transition i.
Proof.
  intros Hcofinal out. unfold PTreeKernel.ptree_iter_cofinal.
  apply free_omega_cofinal_lub_iff.
  - intro n. apply ptree_observable_hitting_increasing.
  - intro n. apply ptree_iter_round_increasing.
  - exact Hcofinal.
Qed.

End FreeOmegaBind.
