Set Universe Polymorphism.
From Coq Require Import Logic.ClassicalChoice.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.

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
