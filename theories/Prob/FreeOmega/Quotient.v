(** Role: Observation-closed coupling and its support soundness. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import FunctionalExtensionality.
From Coq.Program Require Import Equality.
Require Import Morphisms Arith.

From PTree.Prob.Interface Require Import Measure AE Coupling Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift.


(** An observation-closed coupling for the free omega completion.  The
    structural lifting above remains useful for syntax-directed proofs, but
    it deliberately cannot identify, for example, a formal omega limit with
    a single sampling node.  [free_omega_qlift] is the least relation which
    also admits couplings between low-universe observations and is closed
    under the algebraic operations needed by the generic development. *)
Polymorphic Inductive free_omega_qlift {MN}
    `{NI : SemanticMeasure MN}
    `{NO : @SemanticOmega MN NI}
    {A B} (R : A -> B -> Prop) :
    FreeOmega MN A -> FreeOmega MN B -> Prop :=
  | FOQLStructural mu nu :
      free_omega_lift R mu nu -> free_omega_qlift R mu nu
  | FOQLObserve {OA OB} (obsA : A -> OA) (obsB : B -> OB)
      (mu : FreeOmega MN A) (nu : FreeOmega MN B)
      (outA : MN OA) (outB : MN OB) (S : OA -> OB -> Prop) :
      free_omega_observes obsA mu outA ->
      free_omega_observes obsB nu outB ->
      sem_lift S outA outB ->
      (forall x y, S (obsA x) (obsB y) -> R x y) ->
      free_omega_support_lift R mu nu ->
      free_omega_qlift R mu nu
  | FOQLAERestrict (T : A -> B -> Prop)
      (mu : FreeOmega MN A) (nu : FreeOmega MN B)
      (P : A -> Prop) (Q : B -> Prop) :
      free_omega_qlift T mu nu ->
      free_omega_ae P mu -> free_omega_ae Q nu ->
      (forall x y, T x y /\ P x /\ Q y -> R x y) ->
      free_omega_qlift R mu nu
  | FOQLMono (T : A -> B -> Prop) mu nu :
      free_omega_qlift T mu nu ->
      (forall x y, T x y -> R x y) ->
      free_omega_qlift R mu nu
  | FOQLSym mu nu :
      free_omega_qlift (fun y x => R x y) nu mu ->
      free_omega_qlift R mu nu
  | FOQLComp {C} (T : A -> C -> Prop) (U : C -> B -> Prop) mu mid nu :
      free_omega_qlift T mu mid ->
      free_omega_qlift U mid nu ->
      (forall x z, (exists y, T x y /\ U y z) -> R x z) ->
      free_omega_qlift R mu nu
  | FOQLBind {C D} (T : C -> D -> Prop)
      (mu : FreeOmega MN C) (nu : FreeOmega MN D)
      (k : C -> FreeOmega MN A) (h : D -> FreeOmega MN B) :
      free_omega_qlift T mu nu ->
      (forall x y, T x y -> free_omega_qlift R (k x) (h y)) ->
      free_omega_qlift R (free_omega_bind mu k) (free_omega_bind nu h)
  | FOQLSample {C D} (T : C -> D -> Prop)
      (mu : MN C) (nu : MN D)
      (k : C -> FreeOmega MN A) (h : D -> FreeOmega MN B) :
      sem_lift T mu nu ->
      (forall x y, T x y -> free_omega_qlift R (k x) (h y)) ->
      free_omega_qlift R (FOSample mu k) (FOSample nu h)
  | FOQLSampleRetL {C} (x : C) (k : C -> FreeOmega MN A)
      (nu : FreeOmega MN B) :
      (forall P, sem_ae (sem_ret x) P <-> P x) ->
      free_omega_qlift R (k x) nu ->
      free_omega_qlift R (FOSample (sem_ret x) k) nu
  | FOQLSampleBind {C D} (mu : MN C) (h : C -> MN D)
      (k : D -> FreeOmega MN A) (l : D -> FreeOmega MN B) :
      (forall P, sem_ae (sem_bind mu h) P <->
        sem_ae mu (fun x => sem_ae (h x) P)) ->
      (forall y, free_omega_qlift R (k y) (l y)) ->
      free_omega_qlift R
        (FOSample mu (fun x => FOSample (h x) k))
        (FOSample (sem_bind mu h) l)
  | FOQLSampleExchange {C D} (mu : MN C) (nu : MN D)
      (k : C -> D -> FreeOmega MN A)
      (l : D -> C -> FreeOmega MN B) :
      sem_lift semantic_pair_swap_rel
        (semantic_product mu nu) (semantic_product nu mu) ->
      (forall x y, free_omega_qlift R (k x y) (l y x)) ->
      free_omega_support_lift R
        (FOSample mu (fun x => FOSample nu (k x)))
        (FOSample nu (fun y => FOSample mu (l y))) ->
      free_omega_qlift R
        (FOSample mu (fun x => FOSample nu (k x)))
        (FOSample nu (fun y => FOSample mu (l y)))
  | FOQLLub (c : nat -> FreeOmega MN A) (d : nat -> FreeOmega MN B) :
      (forall n, free_omega_qlift R (c n) (d n)) ->
      free_omega_qlift R (FOLub c) (FOLub d)
  | FOQLLubZeroPrefixL (c : nat -> FreeOmega MN A)
      (d : nat -> FreeOmega MN B) :
      (forall n, free_omega_qlift R (c n) (d n)) ->
      free_omega_qlift R
        (FOLub (fun n => match n with O => FOZero
          | Datatypes.S n' => c n' end))
        (FOLub d)
  | FOQLLubZeroPrefixR (c : nat -> FreeOmega MN A)
      (d : nat -> FreeOmega MN B) :
      (forall n, free_omega_qlift R (c n) (d n)) ->
      free_omega_qlift R
        (FOLub c)
        (FOLub (fun n => match n with O => FOZero
          | Datatypes.S n' => d n' end))
  | FOQLSampleLub {C} (mu : MN C) (Good : C -> Prop)
      (chain : C -> nat -> FreeOmega MN B)
      (out : C -> FreeOmega MN A) :
      sem_ae mu Good ->
      (forall x, Good x -> forall n,
        free_omega_approx eq (chain x n) (chain x (S n))) ->
      (forall x, Good x ->
        free_omega_qlift R (out x) (FOLub (chain x))) ->
      free_omega_qlift R
        (FOSample mu out)
        (FOLub (fun n => FOSample mu (fun x => chain x n)))
  | FOQLSampleZero {C} (mu : MN C) :
      free_omega_qlift R (FOSample mu (fun _ => FOZero)) FOZero
  | FOQLLubConstantR (mu : FreeOmega MN A) (nu : FreeOmega MN B) :
      free_omega_qlift R mu nu ->
      free_omega_qlift R mu (FOLub (fun _ => nu))
  | FOQLBindLub {C} (source : nat -> FreeOmega MN C)
      (source_out : FreeOmega MN C)
      (kernels : C -> nat -> FreeOmega MN B)
      (kernel_out : C -> FreeOmega MN A) :
      (* Diagonalization is valid for increasing source AND kernel chains.
         Support transport alone does not prevent a moving diagonal from
         having more mass than any of its pointwise limits. *)
      (forall n, free_omega_approx eq (source n) (source (S n))) ->
      (forall x n, free_omega_approx eq (kernels x n) (kernels x (S n))) ->
      free_omega_qlift eq source_out (FOLub source) ->
      (forall x, free_omega_qlift R (kernel_out x) (FOLub (kernels x))) ->
      free_omega_support_lift R
        (free_omega_bind source_out kernel_out)
        (FOLub (fun n => free_omega_bind (source n)
          (fun x => kernels x n))) ->
      free_omega_qlift R
        (free_omega_bind source_out kernel_out)
        (FOLub (fun n => free_omega_bind (source n)
          (fun x => kernels x n)))
  | FOQLDoubleDiagonal (HAB : A = B)
      (grid : nat -> nat -> FreeOmega MN A) :
      (forall outer inner,
        free_omega_approx eq (grid outer inner)
          (grid outer (Datatypes.S inner))) ->
      (forall outer inner,
        free_omega_approx eq (grid outer inner)
          (grid (Datatypes.S outer) inner)) ->
      (forall x, R x (eq_rect A (fun T => T) x B HAB)) ->
      free_omega_support_lift R
        (FOLub (fun outer => FOLub (grid outer)))
        (eq_rect A (fun T => FreeOmega MN T)
          (FOLub (fun fuel => grid fuel fuel)) B HAB) ->
      free_omega_qlift R
        (FOLub (fun outer => FOLub (grid outer)))
        (eq_rect A (fun T => FreeOmega MN T)
          (FOLub (fun fuel => grid fuel fuel)) B HAB)
  | FOQLCofinal (left : nat -> FreeOmega MN A)
      (right : nat -> FreeOmega MN B) :
      (* Mutual finite domination preserves increasing limits, not
         arbitrary convergent sequences with transient larger terms. *)
      (forall n, free_omega_approx eq (left n) (left (S n))) ->
      (forall n, free_omega_approx eq (right n) (right (S n))) ->
      free_omega_chains_cofinal R left right ->
      free_omega_qlift R (FOLub left) (FOLub right).

Theorem free_omega_qlift_support {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    `{NO : @SemanticOmega MN NI}
    {A B} (R : A -> B -> Prop) mu nu :
  @free_omega_qlift MN NI NO A B R mu nu ->
  free_omega_support_lift R mu nu.
Proof.
  intro Hq. induction Hq.
  - apply free_omega_lift_support_lift. assumption.
  - assumption.
  - eapply free_omega_support_lift_mono.
    + eapply free_omega_support_lift_restrict; eauto.
    + eauto.
  - eapply free_omega_support_lift_mono; eauto.
  - apply free_omega_support_lift_sym. assumption.
  - eapply free_omega_support_lift_mono.
    + eapply free_omega_support_lift_comp; eassumption.
    + assumption.
  - eapply free_omega_support_lift_bind; eauto.
  - eapply free_omega_support_lift_sample; eauto.
  - split.
    + intros P HP. dependent destruction HP.
      apply (proj1 IHHq). apply H1. apply (proj1 (H Good)). exact H0.
    + intros Q HQ.
      pose proof ((proj2 IHHq) Q HQ) as Hbranch.
      eapply FOAESample with (Good := fun z => z = x).
      * apply (proj2 (H (fun z => z = x))). reflexivity.
      * intros z ->. exact Hbranch.
  - eapply free_omega_support_lift_sample_bind; eauto.
  - assumption.
  - apply free_omega_support_lift_lub. assumption.
  - apply free_omega_support_lift_lub_zero_prefix_l. assumption.
  - apply free_omega_support_lift_sym.
    apply free_omega_support_lift_lub_zero_prefix_l.
    intro n. apply free_omega_support_lift_sym. auto.
  - eapply free_omega_support_lift_sample_lub; eauto.
  - apply free_omega_support_lift_sample_zero.
  - apply free_omega_support_lift_lub_constant_r. assumption.
  - assumption.
  - assumption.
  - destruct H1 as [Hlr Hrl]. split.
    + intros P HP. dependent destruction HP. constructor. intro m.
      destruct (Hrl m) as [n Happrox].
      eapply free_omega_approx_ae_backward; [exact Happrox|]. eauto.
    + intros Q HQ. dependent destruction HQ. constructor. intro n.
      destruct (Hlr n) as [m Happrox].
      eapply free_omega_approx_ae_backward; [exact Happrox|]. eauto.
Qed.
