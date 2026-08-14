Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import FunctionalExtensionality Program.Equality Morphisms.

From PTree.Prob Require Import TwoLevelMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A universe-separated free behavior measure.  Samples remain in the
    carrier universe accepted by [MN], whereas results may inhabit a higher
    frontier universe.  [FOLub] is the formal omega completion; no HB
    measurable structure is requested for the result carrier. *)
Polymorphic Inductive FreeOmega@{node node_rep frontier}
    (MN : Type@{node} -> Type@{node_rep})
    (A : Type@{frontier}) : Type :=
  | FORet (x : A)
  | FOZero
  | FOSample {X : Type@{node}} (mu : MN X) (k : X -> FreeOmega MN A)
  | FOLub (chain : nat -> FreeOmega MN A).

Arguments FORet {MN A} _.
Arguments FOZero {MN A}.
Arguments FOSample {MN A X} _ _.
Arguments FOLub {MN A} _.

Polymorphic Fixpoint free_omega_bind {MN A B}
    (mu : FreeOmega MN A) (k : A -> FreeOmega MN B) : FreeOmega MN B :=
  match mu with
  | FORet x => k x
  | FOZero => FOZero
  | FOSample nu h => FOSample nu (fun x => free_omega_bind (h x) k)
  | FOLub chain => FOLub (fun n => free_omega_bind (chain n) k)
  end.

Polymorphic Inductive free_omega_ae {MN}
    `{NI : SemanticMeasureInterface MN} {A}
    (P : A -> Prop) : FreeOmega MN A -> Prop :=
  | FOAERet x : P x -> free_omega_ae P (FORet x)
  | FOAEZero : free_omega_ae P FOZero
  | FOAESample {X} (mu : MN X) k (Good : X -> Prop) :
      sem_ae mu Good ->
      (forall x, Good x -> free_omega_ae P (k x)) ->
      free_omega_ae P (FOSample mu k)
  | FOAELub chain :
      (forall n, free_omega_ae P (chain n)) ->
      free_omega_ae P (FOLub chain).

Polymorphic Inductive free_omega_lift {MN}
    `{NI : SemanticMeasureInterface MN} {A B}
    (R : A -> B -> Prop) : FreeOmega MN A -> FreeOmega MN B -> Prop :=
  | FOLRet x y : R x y ->
      free_omega_lift R (FORet x) (FORet y)
  | FOLZero : free_omega_lift R FOZero FOZero
  | FOLSample {X Y} (S : X -> Y -> Prop)
      (mu : MN X) (nu : MN Y) k h :
      sem_lift S mu nu ->
      (forall x y, S x y -> free_omega_lift R (k x) (h y)) ->
      free_omega_lift R (FOSample mu k) (FOSample nu h)
  | FOLLub c d :
      (forall n, free_omega_lift R (c n) (d n)) ->
      free_omega_lift R (FOLub c) (FOLub d).

#[global] Polymorphic Instance FreeOmegaSemanticMeasureInterface {MN}
    `{NI : SemanticMeasureInterface MN} :
    SemanticMeasureInterface (FreeOmega MN) := {
  sem_ret := @FORet MN;
  sem_bind := @free_omega_bind MN;
  sem_eq := fun A => @eq (FreeOmega MN A);
  sem_ae := fun A mu P => @free_omega_ae MN NI A P mu;
  sem_lift := @free_omega_lift MN NI
}.

Lemma free_omega_sem_retE {MN} `{NI : SemanticMeasureInterface MN}
    {A} (x : A) :
  @sem_ret (FreeOmega MN)
    (FreeOmegaSemanticMeasureInterface (NI := NI)) A x = FORet x.
Proof. reflexivity. Qed.

Section FreeOmegaLaws.
Context {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}.

Lemma free_omega_ae_mono {A} (P Q : A -> Prop) mu :
  (forall x, P x -> Q x) -> free_omega_ae P mu -> free_omega_ae Q mu.
Proof.
  intros HPQ Hae. induction Hae.
  - constructor. exact (HPQ _ H).
  - constructor.
  - eapply FOAESample; [exact H|]. intros x Hx. exact (H1 x Hx).
  - constructor. exact H0.
Qed.

Lemma free_omega_ae_conj {A} (P Q : A -> Prop) mu :
  free_omega_ae P mu -> free_omega_ae Q mu ->
  free_omega_ae (fun x => P x /\ Q x) mu.
Proof.
  intros HP. revert Q. induction HP; intros Q HQ; dependent destruction HQ.
  - constructor. split; assumption.
  - constructor.
  - eapply FOAESample with (Good := fun x => Good x /\ Good0 x).
    + eapply sem_ae_conj; eassumption.
    + intros x [Hx Hx0]. eapply H1; eauto.
  - constructor. intro n. eapply H0. exact (H1 n).
Qed.

Lemma free_omega_lift_mono {A B} (R T : A -> B -> Prop) mu nu :
  (forall x y, R x y -> T x y) ->
  free_omega_lift R mu nu -> free_omega_lift T mu nu.
Proof.
  intros HRT Hl. induction Hl.
  - apply FOLRet. exact (HRT _ _ H).
  - apply FOLZero.
  - eapply FOLSample; [exact H|exact H1].
  - apply FOLLub. exact H0.
Qed.

Lemma free_omega_lift_refl {A} (R : A -> A -> Prop) mu :
  Reflexive R -> free_omega_lift R mu mu.
Proof.
  intros HR. induction mu.
  - constructor. apply HR.
  - constructor.
  - eapply FOLSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. exact (H y).
  - constructor. exact H.
Qed.

Lemma free_omega_lift_sym {A B} (R : A -> B -> Prop) mu nu :
  free_omega_lift R mu nu ->
  free_omega_lift (fun y x => R x y) nu mu.
Proof.
  intros Hl. induction Hl.
  - constructor. exact H.
  - constructor.
  - eapply FOLSample with (S := fun y x => S x y).
    + exact (sem_lift_sym H).
    + intros y x Hyx. exact (H1 x y Hyx).
  - constructor. exact H0.
Qed.

Lemma free_omega_lift_comp {A B C}
    (R : A -> B -> Prop) (T : B -> C -> Prop) mu nu xi :
  free_omega_lift R mu nu -> free_omega_lift T nu xi ->
  free_omega_lift (fun x z => exists y, R x y /\ T y z) mu xi.
Proof.
  intros H12. revert C T xi.
  induction H12; intros C T xi H23; dependent destruction H23.
  - constructor. eexists. split; eassumption.
  - constructor.
  - eapply FOLSample with
      (S := fun x z => exists y, S x y /\ S0 y z).
    + eapply sem_lift_comp; eassumption.
    + intros x z [y [Hxy Hyz]]. eapply H1; eauto.
  - constructor. intro n. eapply H0. exact (H1 n).
Qed.

#[global] Polymorphic Instance FreeOmegaSemanticMeasureCoreLaws :
    @SemanticMeasureCoreLaws (FreeOmega MN)
      (FreeOmegaSemanticMeasureInterface (NI := NI)).
Proof.
  constructor.
  - intros A x. reflexivity.
  - intros A x y. apply eq_sym.
  - intros A x y z. apply eq_trans.
  - intros A mu. induction mu.
    + apply FOAERet. exact I.
    + apply FOAEZero.
    + eapply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros x _. exact (H x).
    + apply FOAELub. exact H.
  - intros A mu P Q. exact (free_omega_ae_mono (P := P) (Q := Q) (mu := mu)).
  - intros A mu P Q. exact (free_omega_ae_conj (P := P) (Q := Q) (mu := mu)).
  - exact @free_omega_lift_mono.
  - exact @free_omega_lift_refl.
  - intros A B R x y Hxy. constructor. exact Hxy.
  - intros A B R mu mu' nu -> H. exact H.
  - intros A B R mu nu nu' -> H. exact H.
  - exact @free_omega_lift_sym.
  - exact @free_omega_lift_comp.
Qed.

Lemma free_omega_bind_assoc {A B C} (mu : FreeOmega MN A)
    (k : A -> FreeOmega MN B) (h : B -> FreeOmega MN C) :
  free_omega_bind (free_omega_bind mu k) h =
  free_omega_bind mu (fun x => free_omega_bind (k x) h).
Proof.
  induction mu; cbn; try reflexivity.
  - f_equal. apply functional_extensionality. exact H.
  - f_equal. apply functional_extensionality. exact H.
Qed.

Lemma free_omega_lift_bind {A B C D}
    (R : A -> B -> Prop) (T : C -> D -> Prop)
    (mu : FreeOmega MN A) (nu : FreeOmega MN B)
    (k : A -> FreeOmega MN C) (h : B -> FreeOmega MN D) :
  free_omega_lift R mu nu ->
  (forall x y, R x y -> free_omega_lift T (k x) (h y)) ->
  free_omega_lift T (free_omega_bind mu k) (free_omega_bind nu h).
Proof.
  intros Hl Hkh. induction Hl; cbn.
  - exact (Hkh _ _ H).
  - constructor.
  - eapply FOLSample; [exact H|]. intros x y Hxy. exact (H1 x y Hxy).
  - constructor. exact H0.
Qed.

#[global] Polymorphic Instance FreeOmegaMixedMeasureInterface :
    MixedMeasureInterface MN (FreeOmega MN) := {
  mixed_bind := fun A B mu k => @FOSample MN B A mu k
}.

Lemma free_omega_mixed_bindE {A B} (mu : MN A)
    (k : A -> FreeOmega MN B) :
  @mixed_bind MN (FreeOmega MN) FreeOmegaMixedMeasureInterface
    A B mu k = FOSample mu k.
Proof. reflexivity. Qed.

(** The free completion has a canonical formal lub.  [sem_total] is kept
    explicit and conservative: totality certificates for analytic limits
    belong to an observable interpretation, not to the syntax alone. *)
#[global] Polymorphic Instance FreeOmegaSemanticOmegaInterface :
    @SemanticOmegaInterface (FreeOmega MN)
      (FreeOmegaSemanticMeasureInterface (NI := NI)) := {
  sem_zero := @FOZero MN;
  sem_le := fun A _ _ => True;
  sem_lub := fun A chain out => out = FOLub chain;
  sem_total := fun A mu => exists x : A, mu = FORet x
}.

#[global] Polymorphic Instance FreeOmegaSemanticOmegaLaws :
    @SemanticOmegaLaws (FreeOmega MN)
      (FreeOmegaSemanticMeasureInterface (NI := NI))
      FreeOmegaSemanticOmegaInterface.
Proof.
  constructor.
  - intros A chain _. exists (FOLub chain). reflexivity.
  - intros A chain mu nu -> ->. reflexivity.
  - intros A B chain mu k _ ->. reflexivity.
Qed.

End FreeOmegaLaws.
