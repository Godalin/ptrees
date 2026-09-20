(** Role: Canonical FreeOmega measure infrastructure. Depends on generic measures; not a concrete native backend or program equivalence. *)
Set Universe Polymorphism.
From Coq.Logic Require Import ClassicalChoice.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A small native sample space with a possibly higher-universe decoder.
    The decoder may return a residual PTree; the native backend is never
    asked to carry trees.  This record is presentation data, not a new
    measure structure or behavioral relation. *)
Polymorphic Record free_omega_native_presentation@{node node_rep frontier}
    (MN : Type@{node} -> Type@{node_rep}) (A : Type@{frontier}) := {
  native_sample_type : Type@{node};
  native_sample_measure : MN native_sample_type;
  native_sample_value : native_sample_type -> A
}.

Arguments native_sample_type {MN A} _.
Arguments native_sample_measure {MN A} _.
Arguments native_sample_value {MN A} _ _.

Definition free_omega_native {MN A} (p : free_omega_native_presentation MN A) :=
  FOSample (native_sample_measure p) (fun x => FORet (native_sample_value p x)).

(** AE reflection through an explicit native presentation is valid even
    though reflection of quotient COUPLING to node lifting need not be. *)
Lemma free_omega_native_ae_iff {MN}
    `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
    {A} (p : free_omega_native_presentation MN A) (P : A -> Prop) :
  free_omega_ae P (free_omega_native p) <->
  sem_ae (native_sample_measure p) (fun x => P (native_sample_value p x)).
Proof.
  split.
  - intro Hae. apply free_omega_ae_sample_inv in Hae.
    eapply sem_ae_mono; [|exact Hae].
    intros x Hx. inversion Hx. assumption.
  - intro Hae. apply FOAESample with
      (Good := fun x => P (native_sample_value p x)); [exact Hae|].
    intros x Hx. apply FOAERet. exact Hx.
Qed.

Section DependentSampling.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}.

Lemma free_omega_ret_native_presentation {A} (x : A) :
  exists p : free_omega_native_presentation MN A,
    free_omega_qlift eq (FORet x) (free_omega_native p).
Proof.
  exists {| native_sample_type := unit; native_sample_measure := sem_ret tt;
    native_sample_value := fun _ => x |}.
  apply FOQLMono with (T := fun a b => b = a).
  - apply FOQLSym, FOQLSampleRetL.
    + apply sem_ae_ret_iff.
    + apply FOQLStructural, FOLRet. reflexivity.
  - intros a b Hba. symmetry. exact Hba.
Qed.

(** The quotient satisfies sampled left-unit even when the node interface
    exposes only exact AE laws for bind, not native monad equalities.
    Consequently native normalization is not automatically a reflection
    theorem for the node lifting. *)
Lemma free_omega_sample_bind_ret_l {X Y A} (x : X) (k : X -> MN Y)
    (decode : Y -> FreeOmega MN A) :
  free_omega_qlift eq (FOSample (sem_bind (sem_ret x) k) decode)
    (FOSample (k x) decode).
Proof.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := FOSample (sem_ret x) (fun y => FOSample (k y) decode)).
  - apply FOQLMono with (T := fun a b => b = a).
    + apply FOQLSym, FOQLSampleBind.
      * intro P. apply sem_ae_bind_iff.
      * intro y. apply free_omega_qlift_refl. intro a. reflexivity.
    + intros a b Hba. symmetry. exact Hba.
  - apply FOQLSampleRetL.
    + intro P. apply sem_ae_ret_iff.
    + apply free_omega_qlift_refl. intro a. reflexivity.
  - intros a c [b [-> ->]]. reflexivity.
Qed.

(** Push a SMALL deterministic map through native sampling; the result
    continuation may still return values in a larger universe. *)
Lemma free_omega_sample_map {X Y A} (mu : MN X) (f : X -> Y)
    (k : Y -> FreeOmega MN A) :
  free_omega_qlift eq
    (FOSample (sem_bind mu (fun x => sem_ret (f x))) k)
    (FOSample mu (fun x => k (f x))).
Proof.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := FOSample mu (fun x => FOSample (sem_ret (f x)) k)).
  - apply FOQLMono with (T := fun a b => b = a).
    + apply FOQLSym, FOQLSampleBind.
      * intro P. apply sem_ae_bind_iff.
      * intro y. apply free_omega_qlift_refl. intro a. reflexivity.
    + intros a b Hba. symmetry. exact Hba.
  - eapply FOQLSample with (T := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. apply FOQLSampleRetL.
      * intro P. apply sem_ae_ret_iff.
      * apply free_omega_qlift_refl. intro a. reflexivity.
  - intros a c [b [-> ->]]. reflexivity.
Qed.

(** Flatten DEPENDENT nested sampling by retaining the entire tagged path.
    Sampling spaces may differ between branches; no fixed-depth or finite
    branching assumption is used. *)
Theorem free_omega_sample_sigma {X} {Y : X -> Type} {A}
    (mu : MN X) (nu : forall x, MN (Y x))
    (k : forall x, Y x -> FreeOmega MN A) :
  free_omega_qlift eq (FOSample mu (fun x => FOSample (nu x) (k x)))
    (FOSample
      (sem_bind mu (fun x => sem_bind (nu x) (fun y => sem_ret (existT Y x y))))
      (fun p => k (projT1 p) (projT2 p))).
Proof.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := FOSample mu (fun x => FOSample
      (sem_bind (nu x) (fun y => sem_ret (existT Y x y)))
      (fun p => k (projT1 p) (projT2 p)))).
  - eapply FOQLSample with (T := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x x' ->.
      eapply FOQLComp with (T := eq) (U := eq)
        (mid := FOSample (nu x') (fun y => FOSample (sem_ret (existT Y x' y))
          (fun p => k (projT1 p) (projT2 p)))).
      * eapply FOQLSample with (T := eq).
        -- apply sem_lift_refl. intro y. reflexivity.
        -- intros y y' ->. apply FOQLMono with (T := fun a b => b = a).
           ++ apply FOQLSym, FOQLSampleRetL.
              ** apply sem_ae_ret_iff.
              ** apply free_omega_qlift_refl. intro a. reflexivity.
           ++ intros a b Hba. symmetry. exact Hba.
      * apply FOQLSampleBind.
        -- intro P. apply sem_ae_bind_iff.
        -- intro p. apply free_omega_qlift_refl. intro a. reflexivity.
      * intros a c [b [-> ->]]. reflexivity.
  - apply FOQLSampleBind.
    + intro P. apply sem_ae_bind_iff.
    + intro p. apply free_omega_qlift_refl. intro a. reflexivity.
  - intros a c [b [-> ->]]. reflexivity.
Qed.

Definition free_omega_native_bind {A B}
    (p : free_omega_native_presentation MN A)
    (f : A -> free_omega_native_presentation MN B) :
    free_omega_native_presentation MN B :=
  {| native_sample_type := {x : native_sample_type p &
        native_sample_type (f (native_sample_value p x))};
     native_sample_measure := sem_bind (native_sample_measure p) (fun x =>
       sem_bind (native_sample_measure (f (native_sample_value p x)))
         (fun y => sem_ret (existT
           (fun x => native_sample_type (f (native_sample_value p x))) x y)));
     native_sample_value := fun z =>
       native_sample_value (f (native_sample_value p (projT1 z))) (projT2 z) |}.

Lemma free_omega_native_bind_eq {A B}
    (p : free_omega_native_presentation MN A)
    (f : A -> free_omega_native_presentation MN B) :
  free_omega_qlift eq
    (free_omega_bind (free_omega_native p) (fun x => free_omega_native (f x)))
    (free_omega_native (free_omega_native_bind p f)).
Proof.
  unfold free_omega_native, free_omega_native_bind. cbn.
  exact (@free_omega_sample_sigma (native_sample_type p)
    (fun x => native_sample_type (f (native_sample_value p x))) B
    (native_sample_measure p)
    (fun x => native_sample_measure (f (native_sample_value p x)))
    (fun x y => FORet (native_sample_value (f (native_sample_value p x)) y))).
Qed.

(** Closure is at the level of full distribution equality, not just
    support.  Choices select proved presentations, never supported values. *)
Theorem free_omega_native_bind_presentation {A B}
    (mu : FreeOmega MN A) (k : A -> FreeOmega MN B)
    (p : free_omega_native_presentation MN A) :
  free_omega_qlift eq mu (free_omega_native p) ->
  (forall x, exists q : free_omega_native_presentation MN B,
    free_omega_qlift eq (k x) (free_omega_native q)) ->
  exists q : free_omega_native_presentation MN B,
    free_omega_qlift eq (free_omega_bind mu k) (free_omega_native q).
Proof.
  intros Hmu Hk. destruct (choice _ Hk) as [f Hf].
  exists (free_omega_native_bind p f).
  eapply FOQLComp with (T := eq) (U := eq).
  - eapply FOQLBind with (T := eq); [exact Hmu|].
    intros x y ->. apply Hf.
  - apply free_omega_native_bind_eq.
  - intros x z [y [-> ->]]. reflexivity.
Qed.
End DependentSampling.
