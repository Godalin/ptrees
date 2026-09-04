Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Require Import List.

From mathcomp Require Import ssreflect ssrbool seq ssralg ssrnum order rat.
From PTree.Prob Require Import RatSubTypes DiscreteMC EnumBindFacts
  MeasureIterationEnum TwoLevelMeasure TwoLevelMeasureEnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import RatSubTypes.
Import GRing.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

(** Raw [Enum] is a finite nonnegative-weight representation: neither its
    type nor its legacy [Discrete] instance bounds the total weight.  This
    predicate records the probability-specific invariant without changing
    the reusable weighted representation. *)
Definition enum_mass {A} (mu : Enum A) : rat :=
  enum_expect (fun _ : A => 1) mu.

Definition enum_subprob {A} (mu : Enum A) : Prop :=
  enum_mass mu <= 1.

Lemma Qval_nnQ_ge0 (p : nnQ) : 0 <= Qval p.
Proof. by case: p=> q Hq. Qed.

Lemma enum_subprob_ret {A} (x : A) :
  enum_subprob (ret_Enum x).
Proof. by rewrite /enum_subprob /enum_mass enum_expect_ret. Qed.

Lemma enum_subprob_zero {A} :
  enum_subprob (@nil (nnQ * A)).
Proof. by rewrite /enum_subprob /enum_mass enum_expect_nil. Qed.

(** Integrating a pointwise-[<= 1] observable cannot exceed the raw total
    weight.  Nonnegativity of Enum coefficients is the only analytic fact
    needed here. *)
Lemma enum_expect_le_mass {A} (mu : Enum A) (f : A -> rat) :
  (forall p x, List.In (p, x) mu -> f x <= 1) ->
  enum_expect f mu <= enum_mass mu.
Proof.
  elim: mu=> [|[p x] tl IH] Hf //=.
  have Hhead : f x <= 1 := Hf p x (or_introl (eq_refl (p, x))).
  have Htail : forall q y, List.In (q, y) tl -> f y <= 1.
  { move=> q y Hy. exact (Hf q y (or_intror Hy)). }
  clear Hf.
  apply: ssrnum.Num.Theory.lerD.
  - rewrite mulr1.
    exact (ssrnum.Num.Theory.ler_piMr (Qval_nnQ_ge0 p) Hhead).
  - exact (IH Htail).
Qed.

Lemma enum_subprob_bind {A B} (mu : Enum A) (k : A -> Enum B) :
  enum_subprob mu ->
  (forall x, enum_subprob (k x)) ->
  enum_subprob (bind_Enum mu k).
Proof.
  move=> Hmu Hk.
  rewrite /enum_subprob /enum_mass enum_expect_bind.
  apply: le_trans Hmu.
  apply: enum_expect_le_mass=> p x _.
  exact (Hk x).
Qed.

(** A finite subdistribution is a raw finite weighting together with the
    invariant required by native [Prob] nodes.  The proof field is erased;
    semantic equality and coupling continue to compare only raw measures. *)
Record SubEnum (A : Type) := {
  subenum_raw : Enum A;
  subenum_bound : enum_subprob subenum_raw
}.

Arguments subenum_raw {A} _.
Arguments subenum_bound {A} _.

Definition subenum_ret {A} (x : A) : SubEnum A :=
  {| subenum_raw := ret_Enum x;
     subenum_bound := enum_subprob_ret x |}.

Definition subenum_zero {A} : SubEnum A :=
  {| subenum_raw := [::];
     subenum_bound := enum_subprob_zero |}.

Definition subenum_bind {A B}
    (mu : SubEnum A) (k : A -> SubEnum B) : SubEnum B :=
  {| subenum_raw := bind_Enum (subenum_raw mu)
        (fun x => subenum_raw (k x));
     subenum_bound := enum_subprob_bind (subenum_bound mu)
        (fun x => subenum_bound (k x)) |}.

Definition subenum_eq {A} (mu nu : SubEnum A) : Prop :=
  @sem_eq Enum Enum_SemanticMeasure A
    (subenum_raw mu) (subenum_raw nu).

Definition subenum_ae {A} (mu : SubEnum A) (P : A -> Prop) : Prop :=
  @sem_ae Enum Enum_SemanticMeasure A (subenum_raw mu) P.

Definition subenum_lift {A B} (R : A -> B -> Prop)
    (mu : SubEnum A) (nu : SubEnum B) : Prop :=
  @sem_lift Enum Enum_SemanticMeasure A B R
    (subenum_raw mu) (subenum_raw nu).

#[global] Instance SubEnum_SemanticMeasure :
    SemanticMeasure SubEnum := {
  sem_ret := @subenum_ret;
  sem_bind := @subenum_bind;
  sem_eq := @subenum_eq;
  sem_ae := @subenum_ae;
  sem_lift := @subenum_lift
}.

#[global] Instance SubEnum_SemanticMeasureCoreLaws :
    @SemanticMeasureCoreLaws SubEnum SubEnum_SemanticMeasure.
Proof.
  constructor; cbn.
  - intros A mu. exact (@sem_eq_refl Enum Enum_SemanticMeasure
      Enum_SemanticMeasureCoreLaws A (subenum_raw mu)).
  - intros A mu nu Hmn. exact (@sem_eq_sym Enum Enum_SemanticMeasure
      Enum_SemanticMeasureCoreLaws A _ _ Hmn).
  - intros A mu nu xi Hmn Hnx. exact (@sem_eq_trans Enum
      Enum_SemanticMeasure Enum_SemanticMeasureCoreLaws A _ _ _ Hmn Hnx).
  - intros A mu. exact (@sem_ae_true Enum Enum_SemanticMeasure
      Enum_SemanticMeasureCoreLaws A (subenum_raw mu)).
  - intros A mu P Q HPQ HP. exact (@sem_ae_mono Enum
      Enum_SemanticMeasure Enum_SemanticMeasureCoreLaws
      A (subenum_raw mu) P Q HPQ HP).
  - intros A mu P Q HP HQ. exact (@sem_ae_conj Enum
      Enum_SemanticMeasure Enum_SemanticMeasureCoreLaws
      A (subenum_raw mu) P Q HP HQ).
  - intros A B R T mu nu HRT Hlift. exact (@sem_lift_mono Enum
      Enum_SemanticMeasure Enum_SemanticMeasureCoreLaws
      A B R T (subenum_raw mu) (subenum_raw nu) HRT Hlift).
  - intros A R mu HR. exact (@sem_lift_refl Enum Enum_SemanticMeasure
      Enum_SemanticMeasureCoreLaws A R (subenum_raw mu) HR).
  - intros A B R x y Hxy. exact (@sem_lift_ret Enum Enum_SemanticMeasure
      Enum_SemanticMeasureCoreLaws A B R x y Hxy).
  - intros A B R mu mu' nu Heq Hlift.
    exact (@sem_lift_proper_l Enum Enum_SemanticMeasure
      Enum_SemanticMeasureCoreLaws A B R
      (subenum_raw mu) (subenum_raw mu') (subenum_raw nu) Heq Hlift).
  - intros A B R mu nu nu' Heq Hlift.
    exact (@sem_lift_proper_r Enum Enum_SemanticMeasure
      Enum_SemanticMeasureCoreLaws A B R
      (subenum_raw mu) (subenum_raw nu) (subenum_raw nu') Heq Hlift).
  - intros A B R mu nu Hlift. exact (@sem_lift_sym Enum
      Enum_SemanticMeasure Enum_SemanticMeasureCoreLaws
      A B R (subenum_raw mu) (subenum_raw nu) Hlift).
  - intros A B C R T mu nu xi Hmn Hnx.
    exact (@sem_lift_comp Enum Enum_SemanticMeasure
      Enum_SemanticMeasureCoreLaws A B C R T
      (subenum_raw mu) (subenum_raw nu) (subenum_raw xi) Hmn Hnx).
Qed.

#[global] Instance SubEnum_SemanticMeasureBindLaws :
    @SemanticMeasureBindLaws SubEnum SubEnum_SemanticMeasure.
Proof.
  constructor; cbn.
  - intros A B x k. exact (@sem_bind_ret_l Enum Enum_SemanticMeasure
      Enum_SemanticMeasureBindLaws A B x (fun y => subenum_raw (k y))).
  - intros A B C mu k h. exact (@sem_bind_assoc Enum
      Enum_SemanticMeasure Enum_SemanticMeasureBindLaws A B C
      (subenum_raw mu) (fun x => subenum_raw (k x))
      (fun y => subenum_raw (h y))).
  - intros A B mu k h Hae. exact (@sem_bind_ae_proper Enum
      Enum_SemanticMeasure Enum_SemanticMeasureBindLaws A B
      (subenum_raw mu) (fun x => subenum_raw (k x))
      (fun x => subenum_raw (h x)) Hae).
  - intros A B C D R T mu nu k h Hmn Hkh.
    exact (@sem_lift_bind Enum Enum_SemanticMeasure
      Enum_SemanticMeasureBindLaws A B C D R T
      (subenum_raw mu) (subenum_raw nu)
      (fun x => subenum_raw (k x)) (fun y => subenum_raw (h y)) Hmn Hkh).
Qed.

#[global] Instance SubEnum_SemanticMeasureAELiftLaws :
    @SemanticMeasureAELiftLaws SubEnum SubEnum_SemanticMeasure.
Proof.
  constructor. intros A mu P Hae.
  exact (@sem_lift_refl_ae Enum Enum_SemanticMeasure
    Enum_SemanticMeasureAELiftLaws A (subenum_raw mu) P Hae).
Qed.

#[global] Instance SubEnum_SemanticMeasureAEKleisliLaws :
    @SemanticMeasureAEKleisliLaws SubEnum SubEnum_SemanticMeasure.
Proof.
  constructor; cbn.
  - exact (@sem_ae_ret Enum Enum_SemanticMeasure
      Enum_SemanticMeasureAEKleisliLaws).
  - intros A B mu k P Q HP HK. exact (@sem_ae_bind Enum
      Enum_SemanticMeasure Enum_SemanticMeasureAEKleisliLaws
      A B (subenum_raw mu) (fun x => subenum_raw (k x)) P Q HP HK).
Qed.

#[global] Instance SubEnum_SemanticMeasureDiracAELaws :
    @SemanticMeasureDiracAELaws SubEnum SubEnum_SemanticMeasure.
Proof.
  constructor. exact (@sem_ae_ret_iff Enum Enum_SemanticMeasure
    Enum_SemanticMeasureDiracAELaws).
Qed.

#[global] Instance SubEnum_SemanticMeasureCountableAELaws :
    @SemanticMeasureCountableAELaws SubEnum SubEnum_SemanticMeasure.
Proof.
  constructor. intros A mu P HP. exact (@sem_ae_countable Enum
    Enum_SemanticMeasure Enum_SemanticMeasureCountableAELaws
    A (subenum_raw mu) P HP).
Qed.

#[global] Instance SubEnum_SemanticMeasureCouplingAELaws :
    @SemanticMeasureCouplingAELaws SubEnum SubEnum_SemanticMeasure.
Proof.
  constructor; cbn.
  - intros A B R mu nu P Hlift HP. exact
      (@sem_lift_ae_transport_r Enum Enum_SemanticMeasure
        Enum_SemanticMeasureCouplingAELaws A B R
        (subenum_raw mu) (subenum_raw nu) P Hlift HP).
  - intros A B R mu nu P Q Hlift HP HQ. exact
      (@sem_lift_ae_restrict Enum Enum_SemanticMeasure
        Enum_SemanticMeasureCouplingAELaws A B R
        (subenum_raw mu) (subenum_raw nu) P Q Hlift HP HQ).
Qed.

#[global] Instance SubEnum_SemanticMeasureBindAEExactLaws :
    @SemanticMeasureBindAEExactLaws SubEnum SubEnum_SemanticMeasure.
Proof.
  constructor. intros A B mu k P. exact (@sem_ae_bind_iff Enum
    Enum_SemanticMeasure Enum_SemanticMeasureBindAEExactLaws
    A B (subenum_raw mu) (fun x => subenum_raw (k x)) P).
Qed.

Definition subenum_sem_le {A} (mu nu : SubEnum A) : Prop :=
  enum_sem_le (subenum_raw mu) (subenum_raw nu).

Definition subenum_sem_lub {A}
    (chain : nat -> SubEnum A) (mu : SubEnum A) : Prop :=
  enum_converges (fun n => subenum_raw (chain n)) (subenum_raw mu).

Definition subenum_total {A} (mu : SubEnum A) : Prop :=
  enum_mass (subenum_raw mu) = 1.

#[global] Instance SubEnum_SemanticOmega :
    @SemanticOmega SubEnum SubEnum_SemanticMeasure := {
  sem_zero := @subenum_zero;
  sem_le := @subenum_sem_le;
  sem_lub := @subenum_sem_lub;
  sem_total := @subenum_total
}.

(** Constructor for public examples: the caller supplies precisely the
    missing probability-side obligation and receives a carrier that cannot
    later be used as an arbitrary weighting. *)
Definition enum_as_subprob {A} (mu : Enum A)
    (Hmu : enum_subprob mu) : SubEnum A :=
  {| subenum_raw := mu; subenum_bound := Hmu |}.
