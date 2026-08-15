Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import FunctionalExtensionality Program.Equality Morphisms Arith.

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

(** [Anchor] pins the otherwise minimizable result universe.  This is useful
    when a low type such as [bool] must inhabit the same [MF] instance as a
    high recursive frontier head. *)
Polymorphic Definition FreeOmegaAt@{node node_rep frontier}
    (MN : Type@{node} -> Type@{node_rep})
    (Anchor A : Type@{frontier}) : Type@{frontier} :=
  @FreeOmega@{node node_rep frontier} MN A.

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

(** Finite subbehavior order.  Unlike the earlier placeholder [sem_le :=
    True], this relation records the concrete information needed for
    cofinality arguments: missing mass is bottom, and existing Ret/Sample/Lub
    structure must be preserved relationally. *)
Polymorphic Inductive free_omega_approx {MN}
    `{NI : SemanticMeasureInterface MN} {A B}
    (R : A -> B -> Prop) : FreeOmega MN A -> FreeOmega MN B -> Prop :=
  | FOApproxZero nu : free_omega_approx R FOZero nu
  | FOApproxRet x y : R x y ->
      free_omega_approx R (FORet x) (FORet y)
  | FOApproxSample {X Y} (S : X -> Y -> Prop)
      (mu : MN X) (nu : MN Y) k h :
      sem_lift S mu nu ->
      (forall x y, S x y -> free_omega_approx R (k x) (h y)) ->
      free_omega_approx R (FOSample mu k) (FOSample nu h)
  | FOApproxLub c d :
      (forall n, free_omega_approx R (c n) (d n)) ->
      free_omega_approx R (FOLub c) (FOLub d).

Lemma free_omega_lift_to_approx {MN}
    `{NI : SemanticMeasureInterface MN} {A B}
    (R : A -> B -> Prop) (mu : FreeOmega MN A) (nu : FreeOmega MN B) :
  free_omega_lift R mu nu -> free_omega_approx R mu nu.
Proof.
  intro Hlift. induction Hlift.
  - constructor. exact H.
  - constructor.
  - eapply FOApproxSample with (S := S).
    + exact H.
    + intros x y Hxy. exact (H1 x y Hxy).
  - constructor. exact H0.
Qed.

Definition free_omega_chains_cofinal {MN}
    `{NI : SemanticMeasureInterface MN} {A B} (R : A -> B -> Prop)
    (left : nat -> FreeOmega MN A) (right : nat -> FreeOmega MN B) : Prop :=
  (forall n, exists m, free_omega_approx R (left n) (right m)) /\
  (forall m, exists n, free_omega_approx (fun y x => R x y)
    (right m) (left n)).

Lemma free_omega_approx_bind {MN}
    `{NI : SemanticMeasureInterface MN} {A B C D}
    (R : A -> B -> Prop) (T : C -> D -> Prop)
    (mu : FreeOmega MN A) (nu : FreeOmega MN B)
    (k : A -> FreeOmega MN C) (h : B -> FreeOmega MN D) :
  free_omega_approx R mu nu ->
  (forall x y, R x y -> free_omega_approx T (k x) (h y)) ->
  free_omega_approx T (free_omega_bind mu k) (free_omega_bind nu h).
Proof.
  intros Happrox Hkh. induction Happrox; cbn.
  - constructor.
  - exact (Hkh _ _ H).
  - eapply FOApproxSample; [exact H|].
    intros x y Hxy. exact (H1 x y Hxy).
  - apply FOApproxLub. exact H0.
Qed.

(** Relational interpretation into a low-universe observable distribution.
    It is relational because an abstract omega interface specifies limits by
    [sem_lub] rather than by a choice function. *)
Polymorphic Inductive free_omega_observes {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NO : @SemanticOmegaInterface MN NI}
    {A O} (obs : A -> O) : FreeOmega MN A -> MN O -> Prop :=
  | FOOObserveRet x :
      free_omega_observes obs (FORet x) (sem_ret (obs x))
  | FOOObserveZero :
      free_omega_observes obs FOZero sem_zero
  | FOOObserveSample {X} (mu : MN X) k (front : X -> MN O) :
      (forall x, free_omega_observes obs (k x) (front x)) ->
      free_omega_observes obs (FOSample mu k) (sem_bind mu front)
  | FOOObserveLub chain outs out :
      (forall n, free_omega_observes obs (chain n) (outs n)) ->
      sem_lub outs out ->
      free_omega_observes obs (FOLub chain) out.

(** Quotient-closed observable meaning.  The inductive observation relation
    records a concrete representative generated by the FreeOmega syntax;
    clients should normally reason through [free_omega_denotes], because a
    measure backend may identify several such representatives by [sem_eq]. *)
Definition free_omega_denotes {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NO : @SemanticOmegaInterface MN NI} {A O}
    (obs : A -> O) (mu : FreeOmega MN A) (out : MN O) : Prop :=
  exists represented,
    free_omega_observes obs mu represented /\ sem_eq represented out.

Section FreeOmegaDenotationBasics.
Context {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.

Lemma free_omega_observes_denotes {A O} (obs : A -> O)
    (mu : FreeOmega MN A) out :
  free_omega_observes obs mu out -> free_omega_denotes obs mu out.
Proof.
  intro Hobs. exists out. split; [exact Hobs|apply sem_eq_refl].
Qed.

Lemma free_omega_denotes_proper {A O} (obs : A -> O)
    (mu : FreeOmega MN A) out1 out2 :
  free_omega_denotes obs mu out1 -> sem_eq out1 out2 ->
  free_omega_denotes obs mu out2.
Proof.
  intros [represented [Hobs Heq1]] Heq2.
  exists represented. split; [exact Hobs|].
  eapply sem_eq_trans; eassumption.
Qed.

End FreeOmegaDenotationBasics.

(** These two capabilities isolate the analytic content needed to compose
    low-level observations of nested unbounded programs.  They are not
    consequences of the raw [free_omega_observes] constructors: bind needs
    monotone continuity, while lub needs a coherent choice of equivalent
    representatives.  Quotient measure models normally satisfy both;
    concrete list models must prove them extensionally. *)
Polymorphic Class FreeOmegaDenotationBindLaws {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NO : @SemanticOmegaInterface MN NI} := {
  free_omega_denotes_bind : forall {A B OA OB}
      (obsA : A -> OA) (obsB : B -> OB)
      (mu : FreeOmega MN A) (out : MN OA)
      (k : A -> FreeOmega MN B) (front : OA -> MN OB),
    free_omega_denotes obsA mu out ->
    (forall x, free_omega_denotes obsB (k x) (front (obsA x))) ->
    free_omega_denotes obsB (free_omega_bind mu k)
      (sem_bind out front)
}.

Polymorphic Class FreeOmegaDenotationOmegaLaws {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NO : @SemanticOmegaInterface MN NI} := {
  free_omega_denotes_lub : forall {A O} (obs : A -> O)
      (chain : nat -> FreeOmega MN A) (outs : nat -> MN O) out,
    (forall n, free_omega_denotes obs (chain n) (outs n)) ->
    sem_lub outs out ->
    free_omega_denotes obs (FOLub chain) out
}.

Lemma free_omega_observes_bind_ret {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NO : @SemanticOmegaInterface MN NI}
    {A B O} (obsA : A -> O) (obsB : B -> O) (f : A -> B)
    (mu : FreeOmega MN A) (out : MN O) :
  free_omega_observes obsA mu out ->
  (forall x, obsB (f x) = obsA x) ->
  free_omega_observes obsB
    (free_omega_bind mu (fun x => FORet (f x))) out.
Proof.
  intros Hobs Hf. induction Hobs; cbn.
  - rewrite <- Hf. constructor.
  - constructor.
  - eapply FOOObserveSample. exact H0.
  - eapply FOOObserveLub; eauto.
Qed.

Section FreeOmegaObservationLaws.
Context {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NB : @SemanticMeasureBindLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}
  `{NOL : @SemanticOmegaLaws MN NI NO}.

(** Observation is relational only because [sem_lub] need not choose a
    concrete representative.  Once the node backend supplies extensional lub
    uniqueness, the denoted low-universe distribution is deterministic up to
    [sem_eq]. *)
Lemma free_omega_observes_unique {A O} (obs : A -> O)
    (mu : FreeOmega MN A) out1 out2 :
  free_omega_observes obs mu out1 ->
  free_omega_observes obs mu out2 ->
  sem_eq out1 out2.
Proof.
  intros H1. revert out2. induction H1; intros out2 H2;
    dependent destruction H2.
  - apply sem_eq_refl.
  - apply sem_eq_refl.
  - apply sem_bind_ae_proper.
    eapply sem_ae_mono; [|apply sem_ae_true].
    intros x _. exact (H0 x _ (H1 x)).
  - eapply sem_lub_proper.
    + intros n. exact (H0 n _ (H2 n)).
    + exact H1.
    + exact H3.
Qed.

End FreeOmegaObservationLaws.

#[global] Polymorphic Instance FreeOmegaSemanticMeasureInterface {MN}
    `{NI : SemanticMeasureInterface MN} :
    SemanticMeasureInterface (FreeOmega MN) := {
  sem_ret := @FORet MN;
  sem_bind := @free_omega_bind MN;
  sem_eq := fun A => @free_omega_lift MN NI A A eq;
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

Lemma free_omega_ae_bind {A B} (mu : FreeOmega MN A)
    (k : A -> FreeOmega MN B) (P : A -> Prop) (Q : B -> Prop) :
  free_omega_ae P mu ->
  (forall x, P x -> free_omega_ae Q (k x)) ->
  free_omega_ae Q (free_omega_bind mu k).
Proof.
  intros Hae Hk. induction Hae; cbn.
  - exact (Hk x H).
  - constructor.
  - eapply FOAESample; [exact H|].
    intros x Hx. exact (H1 x Hx).
  - constructor. exact H0.
Qed.

Lemma free_omega_ae_bind_inv {A B} (mu : FreeOmega MN A)
    (k : A -> FreeOmega MN B) (P : B -> Prop) :
  free_omega_ae P (free_omega_bind mu k) ->
  free_omega_ae (fun x => free_omega_ae P (k x)) mu.
Proof.
  induction mu; cbn; intro Hae.
  - constructor. exact Hae.
  - constructor.
  - dependent destruction Hae. eapply FOAESample; [exact H0|].
    intros x Hx. exact (H x (H1 x Hx)).
  - dependent destruction Hae. constructor. intro n.
    exact (H n (H0 n)).
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

Lemma free_omega_approx_refl {A} (R : A -> A -> Prop) mu :
  Reflexive R -> free_omega_approx R mu mu.
Proof.
  intros HR. induction mu.
  - constructor. apply HR.
  - constructor.
  - eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. exact (H y).
  - constructor. exact H.
Qed.

Lemma free_omega_approx_mono {A B} (R T : A -> B -> Prop) mu nu :
  (forall x y, R x y -> T x y) ->
  free_omega_approx R mu nu -> free_omega_approx T mu nu.
Proof.
  intros HRT Happrox. induction Happrox.
  - constructor.
  - constructor. exact (HRT _ _ H).
  - eapply FOApproxSample; [exact H|exact H1].
  - constructor. exact H0.
Qed.

Lemma free_omega_approx_comp {A B C}
    (R : A -> B -> Prop) (T : B -> C -> Prop) mu nu xi :
  free_omega_approx R mu nu -> free_omega_approx T nu xi ->
  free_omega_approx (fun x z => exists y, R x y /\ T y z) mu xi.
Proof.
  intros H12. revert C T xi.
  induction H12; intros C T xi H23.
  - constructor.
  - dependent destruction H23. constructor. eexists. split; eassumption.
  - dependent destruction H23.
    eapply FOApproxSample with
      (S := fun x z => exists y, S x y /\ S0 y z).
    + eapply sem_lift_comp; eassumption.
    + intros x z [y [Hxy Hyz]]. eapply H1; eauto.
  - dependent destruction H23. constructor. intro n.
    eapply H0. exact (H1 n).
Qed.

Lemma free_omega_approx_trans {A}
    (mu nu xi : FreeOmega MN A) :
  free_omega_approx eq mu nu -> free_omega_approx eq nu xi ->
  free_omega_approx eq mu xi.
Proof.
  intros Hmn Hnx. eapply free_omega_approx_mono with
    (R := fun x z => exists mid, x = mid /\ mid = z).
  - intros x z [mid [-> ->]]. reflexivity.
  - exact (free_omega_approx_comp (R := eq) (T := eq) Hmn Hnx).
Qed.

Lemma free_omega_approx_steps {A} (c : nat -> FreeOmega MN A) :
  (forall n, free_omega_approx eq (c n) (c (S n))) ->
  forall n k, free_omega_approx eq (c n) (c (n + k)).
Proof.
  intros Hinc n k. induction k.
  - replace (n + 0) with n by exact (plus_n_O n).
    apply free_omega_approx_refl. intros x. exact eq_refl.
  - replace (n + S k) with (S (n + k)) by
      exact (plus_n_Sm n k).
    eapply free_omega_approx_trans; eauto.
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
  - intros A mu. apply free_omega_lift_refl. intros x. reflexivity.
  - intros A mu nu Hmn.
    eapply free_omega_lift_mono; [|exact (free_omega_lift_sym Hmn)].
    intros x y Hyx. symmetry. exact Hyx.
  - intros A mu nu xi Hmn Hnx.
    eapply free_omega_lift_mono;
      [|exact (free_omega_lift_comp (R := eq) (T := eq) Hmn Hnx)].
    intros x z [y [-> ->]]. reflexivity.
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
  - intros A B R mu mu' nu Hmm Hmn.
    assert (Hmm' : free_omega_lift eq mu' mu).
    { eapply free_omega_lift_mono; [|exact (free_omega_lift_sym Hmm)].
      intros x y Hyx. symmetry. exact Hyx. }
    eapply free_omega_lift_mono;
      [|exact (free_omega_lift_comp (R := eq) (T := R) Hmm' Hmn)].
    intros x z [y [-> Hyz]]. exact Hyz.
  - intros A B R mu nu nu' Hnn Hmn.
    eapply free_omega_lift_mono;
      [|exact (free_omega_lift_comp (R := R) (T := eq) Hmn Hnn)].
    intros x z [y [Hxy ->]]. exact Hxy.
  - exact @free_omega_lift_sym.
  - exact @free_omega_lift_comp.
Qed.

#[global] Polymorphic Instance FreeOmegaSemanticMeasureAEKleisliLaws :
    @SemanticMeasureAEKleisliLaws (FreeOmega MN)
      (FreeOmegaSemanticMeasureInterface (NI := NI)).
Proof.
  constructor.
  - intros A P x Hx. constructor. exact Hx.
  - intros A B mu k P Q Hmu Hk.
    cbn in Hmu, Hk |- *. exact (free_omega_ae_bind Hmu Hk).
Qed.

Lemma free_omega_ae_countable
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A} (mu : FreeOmega MN A) (P : nat -> A -> Prop) :
  (forall n, free_omega_ae (P n) mu) ->
  free_omega_ae (fun x => forall n, P n x) mu.
Proof.
  revert P. induction mu as [x| |X node k IH|chain IH]; intros P HP.
  - constructor. intro n. specialize (HP n). dependent destruction HP.
    assumption.
  - constructor.
  - eapply FOAESample with
      (Good := fun x => forall n, free_omega_ae (P n) (k x)).
    + apply sem_ae_countable. intro n.
      specialize (HP n). dependent destruction HP.
      eapply sem_ae_mono; [|eassumption]. intros y Hy. eauto.
    + intros x Hx. apply IH. exact Hx.
  - constructor. intro m. apply IH. intro n. specialize (HP n).
    dependent destruction HP. eauto.
Qed.

#[global] Polymorphic Instance FreeOmegaSemanticMeasureCountableAELaws
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI} :
    @SemanticMeasureCountableAELaws (FreeOmega MN)
      (FreeOmegaSemanticMeasureInterface (NI := NI)).
Proof.
  constructor. intros A mu P HP. apply free_omega_ae_countable. exact HP.
Qed.

Lemma free_omega_lift_ae_restrict
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    {A B} (R : A -> B -> Prop) (mu : FreeOmega MN A)
    (nu : FreeOmega MN B) (P : A -> Prop) (Q : B -> Prop) :
  free_omega_lift R mu nu ->
  free_omega_ae P mu -> free_omega_ae Q nu ->
  free_omega_lift (fun x y => R x y /\ P x /\ Q y) mu nu.
Proof.
  intros Hlift. induction Hlift; intros HP HQ;
    dependent destruction HP; dependent destruction HQ.
  - constructor. repeat split; assumption.
  - constructor.
  - eapply FOLSample with
      (S := fun x y => S x y /\ Good x /\ Good0 y).
    + eapply sem_lift_ae_restrict; eassumption.
    + intros x y [Hxy [Hx Hy]]. eapply H1; eauto.
  - constructor. intro n. eapply H0; eauto.
Qed.

Lemma free_omega_lift_ae_transport_r
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    {A B} (R : A -> B -> Prop) (mu : FreeOmega MN A)
    (nu : FreeOmega MN B) (P : A -> Prop) :
  free_omega_lift R mu nu -> free_omega_ae P mu ->
  free_omega_ae (fun y => exists x, R x y /\ P x) nu.
Proof.
  intros Hlift HP. induction Hlift; dependent destruction HP.
  - constructor. exists x. split; assumption.
  - constructor.
  - eapply FOAESample with
      (Good := fun y => exists x, S x y /\ Good x).
    + eapply sem_lift_ae_transport_r; eassumption.
    + intros y [x [Hxy Hx]]. eapply H1; eauto.
  - constructor. intro n. exact (H0 n (H1 n)).
Qed.

#[global] Polymorphic Instance FreeOmegaSemanticMeasureCouplingAELaws
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI} :
    @SemanticMeasureCouplingAELaws (FreeOmega MN)
      (FreeOmegaSemanticMeasureInterface (NI := NI)).
Proof.
  constructor.
  - intros A B R mu nu P Hlift HP.
    exact (free_omega_lift_ae_transport_r
      (NCAE := NCAE) Hlift HP).
  - intros A B R mu nu P Q Hlift HP HQ.
    exact (free_omega_lift_ae_restrict
      (NCAE := NCAE) Hlift HP HQ).
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

Lemma free_omega_bind_ae_proper
    `{NAE : @SemanticMeasureAELiftLaws MN NI}
    {A B} (mu : FreeOmega MN A) (k h : A -> FreeOmega MN B) :
  free_omega_ae (fun x => free_omega_lift eq (k x) (h x)) mu ->
  free_omega_lift eq (free_omega_bind mu k) (free_omega_bind mu h).
Proof.
  intros Hae. induction Hae; cbn.
  - exact H.
  - constructor.
  - eapply FOLSample with (S := fun x y => x = y /\ Good x).
    + exact (sem_lift_refl_ae H).
    + intros x y [-> Hy]. exact (H1 y Hy).
  - constructor. exact H0.
Qed.

#[global] Polymorphic Instance FreeOmegaSemanticMeasureBindLaws
    `{NAE : @SemanticMeasureAELiftLaws MN NI} :
    @SemanticMeasureBindLaws (FreeOmega MN)
      (FreeOmegaSemanticMeasureInterface (NI := NI)).
Proof.
  constructor.
  - intros A B x k. apply free_omega_lift_refl. intros y. reflexivity.
  - intros A B C mu k h.
    change (free_omega_lift eq
      (free_omega_bind (free_omega_bind mu k) h)
      (free_omega_bind mu (fun x => free_omega_bind (k x) h))).
    rewrite free_omega_bind_assoc.
    apply free_omega_lift_refl. intros y. reflexivity.
  - intros A B mu k h Hae. exact (free_omega_bind_ae_proper Hae).
  - exact @free_omega_lift_bind.
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

#[global] Polymorphic Instance FreeOmegaMixedMeasureLaws
    `{NAE : @SemanticMeasureAELiftLaws MN NI} :
    @MixedMeasureLaws MN (FreeOmega MN) NI
      (FreeOmegaSemanticMeasureInterface (NI := NI))
      FreeOmegaMixedMeasureInterface.
Proof.
  constructor.
  - intros A B mu k h Hae.
    eapply FOLSample with (S := fun x y => x = y /\
      free_omega_lift eq (k x) (h x)).
    + exact (sem_lift_refl_ae Hae).
    + intros x y [-> Hxy]. exact Hxy.
  - intros A B C mu k h.
    apply free_omega_lift_refl. intros x. reflexivity.
  - intros A B C D R T mu nu k h Hmn Hkh.
    eapply FOLSample with (S := R); eauto.
Qed.

(** The free completion has a canonical formal lub.  [sem_total] is kept
    explicit and conservative: totality certificates for analytic limits
    belong to an observable interpretation, not to the syntax alone. *)
#[global] Polymorphic Instance FreeOmegaSemanticOmegaInterface :
    forall `{NO : @SemanticOmegaInterface MN NI},
    @SemanticOmegaInterface (FreeOmega MN)
      (FreeOmegaSemanticMeasureInterface (NI := NI)).
Proof.
  intros NO. refine {| sem_zero := @FOZero MN;
    sem_le := fun A => @free_omega_approx MN NI A A eq;
    sem_lub := fun A chain out =>
      @sem_eq (FreeOmega MN)
        (FreeOmegaSemanticMeasureInterface (NI := NI)) A
        out (FOLub chain);
    sem_total := fun A mu => exists (O : Type) (obs : A -> O) (out : MN O),
      free_omega_observes obs mu out /\ sem_total out |}.
Defined.

(** The old syntactic-total design would accept only [FORet].  Observable
    totality instead permits a formal omega limit exactly when it denotes a
    total low-universe node distribution. *)

#[global] Polymorphic Instance FreeOmegaSemanticOmegaLaws :
    forall `{NO : @SemanticOmegaInterface MN NI},
    @SemanticOmegaLaws (FreeOmega MN)
      (FreeOmegaSemanticMeasureInterface (NI := NI))
      (FreeOmegaSemanticOmegaInterface (NO := NO)).
Proof.
  intros NO. constructor.
  - intros A chain _. exists (FOLub chain).
    apply free_omega_lift_refl. intros x. reflexivity.
  - intros A chain mu nu Hmu Hnu.
    eapply sem_eq_trans; [exact Hmu|].
    eapply sem_eq_sym. exact Hnu.
  - intros A chain chain' mu nu Hcc Hmu Hnu.
    eapply sem_eq_trans; [exact Hmu|].
    eapply sem_eq_trans.
    + apply FOLLub. exact Hcc.
    + eapply sem_eq_sym. exact Hnu.
  - intros A chain chain' mu Hcc Hmu.
    eapply sem_eq_trans; [exact Hmu|].
    apply FOLLub. exact Hcc.
  - intros A B chain mu k _ Hmu.
    cbn in Hmu |- *.
    change (free_omega_lift eq (free_omega_bind mu k)
      (free_omega_bind (FOLub chain) k)).
    eapply free_omega_lift_bind with (R := eq) (T := eq);
      [exact Hmu|].
    intros x y ->. apply free_omega_lift_refl.
    intros z. reflexivity.
Qed.

#[global] Polymorphic Instance FreeOmegaSemanticMeasureOrderLaws :
    forall `{NO : @SemanticOmegaInterface MN NI},
    @SemanticMeasureOrderLaws (FreeOmega MN)
      (FreeOmegaSemanticMeasureInterface (NI := NI))
      (FreeOmegaSemanticOmegaInterface (NO := NO)).
Proof.
  intros NO. constructor.
  - intros A mu. apply free_omega_approx_refl. intros x. reflexivity.
  - intros A mu nu xi Hmn Hnx.
    eapply free_omega_approx_mono with
      (R := fun x z => exists mid, x = mid /\ mid = z).
    + intros x z [mid [-> ->]]. reflexivity.
    + exact (free_omega_approx_comp (R := eq) (T := eq) Hmn Hnx).
  - intros A mu. constructor.
  - intros A B mu nu k Hmn.
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + exact Hmn.
    + intros x y ->. apply free_omega_approx_refl.
      intros z. reflexivity.
  - intros A B mu k h Hkh.
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply free_omega_approx_refl. intros x. reflexivity.
    + intros x y ->. apply Hkh.
Qed.

End FreeOmegaLaws.

(** High-universe support transport, stated without choosing a concrete
    measure on the result carrier.  This is the information that an
    observation-level coupling must retain in addition to its low-universe
    denotation: every AE-good set on one representation is transported to
    the relational image on the other. *)
Polymorphic Definition free_omega_support_lift {MN}
    `{NI : SemanticMeasureInterface MN} {A B}
    (R : A -> B -> Prop) (mu : FreeOmega MN A) (nu : FreeOmega MN B) : Prop :=
  (forall P, free_omega_ae P mu ->
    free_omega_ae (fun y => exists x, R x y /\ P x) nu) /\
  (forall Q, free_omega_ae Q nu ->
    free_omega_ae (fun x => exists y, R x y /\ Q y) mu).

Lemma free_omega_lift_support_lift {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    {A B} (R : A -> B -> Prop) mu nu :
  free_omega_lift R mu nu -> free_omega_support_lift R mu nu.
Proof.
  intro Hlift. split.
  - intro P. exact (free_omega_lift_ae_transport_r Hlift).
  - intro Q. apply free_omega_lift_ae_transport_r.
    exact (free_omega_lift_sym Hlift).
Qed.

(** Almost-everywhere predicates are downward closed along the finite
    subbehavior order.  This is the support fact needed by diagonal and
    cofinal quotient laws: a finite approximation cannot introduce a return
    outside the support of the behavior which contains it. *)
Lemma free_omega_approx_ae_backward {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    {A B} (R : A -> B -> Prop) mu nu (Q : B -> Prop) :
  free_omega_approx R mu nu -> free_omega_ae Q nu ->
  free_omega_ae (fun x => exists y, R x y /\ Q y) mu.
Proof.
  intros Happrox. induction Happrox; intro HQ.
  - constructor.
  - dependent destruction HQ. constructor. exists y. split; assumption.
  - dependent destruction HQ.
    eapply FOAESample with
      (Good := fun x => exists y, S x y /\ Good y).
    + apply sem_lift_ae_transport_r with
        (R := fun y x => S x y) (mu := nu) (nu := mu).
      * apply sem_lift_sym. exact H.
      * exact H2.
    + intros x [y [Hxy Hy]]. eapply H1; eauto.
  - dependent destruction HQ. constructor. intro n. eapply H0; eauto.
Qed.

Lemma free_omega_support_lift_mono {MN}
    `{NI : SemanticMeasureInterface MN} {A B}
    (R T : A -> B -> Prop) mu nu :
  free_omega_support_lift R mu nu ->
  (forall x y, R x y -> T x y) ->
  free_omega_support_lift T mu nu.
Proof.
  intros [Hright Hleft] HRT. split.
  - intros P HP. eapply free_omega_ae_mono; [|exact (Hright P HP)].
    intros y [x [Hxy Hx]]. exists x. split; [apply HRT|]; assumption.
  - intros Q HQ. eapply free_omega_ae_mono; [|exact (Hleft Q HQ)].
    intros x [y [Hxy Hy]]. exists y. split; [apply HRT|]; assumption.
Qed.

Lemma free_omega_support_lift_sym {MN}
    `{NI : SemanticMeasureInterface MN} {A B}
    (R : A -> B -> Prop) mu nu :
  free_omega_support_lift R mu nu ->
  free_omega_support_lift (fun y x => R x y) nu mu.
Proof. intros [Hright Hleft]. split; assumption. Qed.

Lemma free_omega_support_lift_comp {MN}
    `{NI : SemanticMeasureInterface MN} {A B C}
    (R : A -> B -> Prop) (T : B -> C -> Prop) mu mid nu :
  free_omega_support_lift R mu mid ->
  free_omega_support_lift T mid nu ->
  free_omega_support_lift
    (fun x z => exists y, R x y /\ T y z) mu nu.
Proof.
  intros [HRr HRl] [HTr HTl]. split.
  - intros P HP. specialize (HRr P HP). specialize (HTr _ HRr).
    eapply free_omega_ae_mono; [|exact HTr].
    intros z [y [Hyz [x [Hxy Hx]]]].
    exists x. split; [exists y; split|]; assumption.
  - intros Q HQ. specialize (HTl Q HQ). specialize (HRl _ HTl).
    eapply free_omega_ae_mono; [|exact HRl].
    intros x [y [Hxy [z [Hyz Hz]]]].
    exists z. split; [exists y; split|]; assumption.
Qed.

Lemma free_omega_support_lift_restrict {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    {A B} (R : A -> B -> Prop) mu nu (P : A -> Prop) (Q : B -> Prop) :
  free_omega_support_lift R mu nu ->
  free_omega_ae P mu -> free_omega_ae Q nu ->
  free_omega_support_lift (fun x y => R x y /\ P x /\ Q y) mu nu.
Proof.
  intros [Hright Hleft] HP HQ. split.
  - intros P0 HP0.
    pose proof (free_omega_ae_conj (P := P0) (Q := P)
      (mu := mu) HP0 HP) as HPboth.
    pose proof (Hright _ HPboth) as Himage.
    pose proof (free_omega_ae_conj (P := _ ) (Q := Q)
      (mu := nu) Himage HQ) as Hboth.
    eapply free_omega_ae_mono; [|exact Hboth].
    intros y [[x [Hxy [HP0x HPx]]] HQy].
    exists x. repeat split; assumption.
  - intros Q0 HQ0.
    pose proof (free_omega_ae_conj (P := Q0) (Q := Q)
      (mu := nu) HQ0 HQ) as HQboth.
    pose proof (Hleft _ HQboth) as Himage.
    pose proof (free_omega_ae_conj (P := _) (Q := P)
      (mu := mu) Himage HP) as Hboth.
    eapply free_omega_ae_mono; [|exact Hboth].
    intros x [[y [Hxy [HQ0y HQy]]] HPx].
    exists y. repeat split; assumption.
Qed.

Lemma free_omega_support_lift_bind {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    {A B C D} (T : C -> D -> Prop) (R : A -> B -> Prop)
    mu nu (k : C -> FreeOmega MN A) (h : D -> FreeOmega MN B) :
  free_omega_support_lift T mu nu ->
  (forall x y, T x y -> free_omega_support_lift R (k x) (h y)) ->
  free_omega_support_lift R
    (free_omega_bind mu k) (free_omega_bind nu h).
Proof.
  intros [HTRight HTLeft] Hkh. split.
  - intros P HP. apply free_omega_ae_bind_inv in HP.
    specialize (HTRight _ HP).
    eapply free_omega_ae_bind; [exact HTRight|].
    intros y [x [Hxy Hpx]].
    exact ((proj1 (Hkh x y Hxy)) P Hpx).
  - intros Q HQ. apply free_omega_ae_bind_inv in HQ.
    specialize (HTLeft _ HQ).
    eapply free_omega_ae_bind; [exact HTLeft|].
    intros x [y [Hxy Hqy]].
    exact ((proj2 (Hkh x y Hxy)) Q Hqy).
Qed.

Lemma free_omega_support_lift_sample {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    {A B C D} (T : C -> D -> Prop) (R : A -> B -> Prop)
    (mu : MN C) (nu : MN D)
    (k : C -> FreeOmega MN A) (h : D -> FreeOmega MN B) :
  sem_lift T mu nu ->
  (forall x y, T x y -> free_omega_support_lift R (k x) (h y)) ->
  free_omega_support_lift R (FOSample mu k) (FOSample nu h).
Proof.
  intros HT Hkh. split.
  - intros P HP. dependent destruction HP.
    eapply FOAESample with
      (Good := fun y => exists x, T x y /\ Good x).
    + eapply sem_lift_ae_transport_r; eassumption.
    + intros y [x [Hxy Hx]].
      apply (proj1 (Hkh x y Hxy) P). eauto.
  - intros Q HQ. dependent destruction HQ.
    eapply FOAESample with
      (Good := fun x => exists y, T x y /\ Good y).
    + eapply sem_lift_ae_transport_r with
        (R := fun y x => T x y) (mu := nu) (nu := mu).
      * apply sem_lift_sym. exact HT.
      * eassumption.
    + intros x [y [Hxy Hy]].
      apply (proj2 (Hkh x y Hxy) Q). eauto.
Qed.

Lemma free_omega_ae_sample_inv {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    {A C} (mu : MN C) (k : C -> FreeOmega MN A) (P : A -> Prop) :
  free_omega_ae P (FOSample mu k) ->
  sem_ae mu (fun x => free_omega_ae P (k x)).
Proof.
  intro HP. dependent destruction HP.
  eapply sem_ae_mono; [|eassumption]. intros x Hx. eauto.
Qed.

Lemma free_omega_support_lift_sample_lub {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A B C} (R : A -> B -> Prop) (mu : MN C) (Good : C -> Prop)
    (chain : C -> nat -> FreeOmega MN B)
    (out : C -> FreeOmega MN A) :
  sem_ae mu Good ->
  (forall x, Good x ->
    free_omega_support_lift R (out x) (FOLub (chain x))) ->
  free_omega_support_lift R
    (FOSample mu out)
    (FOLub (fun n => FOSample mu (fun x => chain x n))).
Proof.
  intros HGood Hout. split.
  - intros P HP. apply free_omega_ae_sample_inv in HP. constructor. intro n.
    eapply FOAESample with
      (Good := fun x => Good x /\ free_omega_ae P (out x)).
    + apply sem_ae_conj; assumption.
    + intros x [HxGood HxP].
      pose proof ((proj1 (Hout x HxGood)) P HxP) as Hlub.
      dependent destruction Hlub. eauto.
  - intros Q HQ. dependent destruction HQ.
    eapply FOAESample with
      (Good := fun x => Good x /\
        forall n, free_omega_ae Q (chain x n)).
    + apply sem_ae_conj; [exact HGood|].
      apply sem_ae_countable. intro n.
      apply free_omega_ae_sample_inv. eauto.
    + intros x [HxGood HxQ].
      apply (proj2 (Hout x HxGood) Q). constructor. exact HxQ.
Qed.

Lemma free_omega_support_lift_lub {MN}
    `{NI : SemanticMeasureInterface MN} {A B}
    (R : A -> B -> Prop) (c : nat -> FreeOmega MN A)
    (d : nat -> FreeOmega MN B) :
  (forall n, free_omega_support_lift R (c n) (d n)) ->
  free_omega_support_lift R (FOLub c) (FOLub d).
Proof.
  intro Hcd. split; intros P HP; dependent destruction HP; constructor;
    intro n; [apply (proj1 (Hcd n))|apply (proj2 (Hcd n))]; auto.
Qed.

Lemma free_omega_support_lift_lub_zero_prefix_l {MN}
    `{NI : SemanticMeasureInterface MN} {A B}
    (R : A -> B -> Prop) (c : nat -> FreeOmega MN A)
    (d : nat -> FreeOmega MN B) :
  (forall n, free_omega_support_lift R (c n) (d n)) ->
  free_omega_support_lift R
    (FOLub (fun n => match n with O => FOZero
      | Datatypes.S n' => c n' end)) (FOLub d).
Proof.
  intro Hcd. split.
  - intros P HP. dependent destruction HP. constructor. intro n.
    apply (proj1 (Hcd n) P).
    match goal with
    | Hchain : forall i : nat, _ |- _ =>
        exact (Hchain (S n))
    end.
  - intros P HP. dependent destruction HP. constructor. intros [|n].
    + constructor.
    + apply (proj2 (Hcd n) P).
      match goal with
      | Hchain : forall i : nat, _ |- _ =>
          exact (Hchain n)
      end.
Qed.

Lemma free_omega_support_lift_sample_zero {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    {A B C} (R : A -> B -> Prop) (mu : MN C) :
  free_omega_support_lift R (FOSample mu (fun _ => @FOZero MN A))
    (@FOZero MN B).
Proof.
  split; intros P HP.
  - constructor.
  - eapply FOAESample with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros. constructor.
Qed.

Lemma free_omega_support_lift_lub_constant_r {MN}
    `{NI : SemanticMeasureInterface MN} {A B}
    (R : A -> B -> Prop) mu nu :
  free_omega_support_lift R mu nu ->
  free_omega_support_lift R mu (FOLub (fun _ => nu)).
Proof.
  intros [Hright Hleft]. split.
  - intros P HP. constructor. intro n. exact (Hright P HP).
  - intros Q HQ. dependent destruction HQ. apply Hleft.
    match goal with
    | Hchain : forall i : nat, _ |- _ => exact (Hchain 0)
    end.
Qed.

Lemma free_omega_support_lift_bind_diagonal {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A B} (R : B -> B -> Prop)
    (source : nat -> FreeOmega MN A) (source_out : FreeOmega MN A)
    (kernels : A -> nat -> FreeOmega MN B)
    (kernel_out : A -> FreeOmega MN B) :
  (forall n, free_omega_approx eq (source n) (source (S n))) ->
  (forall x n,
    free_omega_approx eq (kernels x n) (kernels x (S n))) ->
  free_omega_support_lift eq source_out (FOLub source) ->
  (forall x, free_omega_support_lift R
    (kernel_out x) (FOLub (kernels x))) ->
  free_omega_support_lift R
    (free_omega_bind source_out kernel_out)
    (FOLub (fun n => free_omega_bind (source n)
      (fun x => kernels x n))).
Proof.
  intros Hsource_inc Hkernels_inc Hsource Hkernels. split.
  - intros P HP. apply free_omega_ae_bind_inv in HP.
    pose proof ((proj1 Hsource) _ HP) as HsourceP.
    eapply free_omega_ae_mono in HsourceP.
    2: { intros x [y [-> Hy]]. exact Hy. }
    dependent destruction HsourceP. constructor. intro n.
    eapply free_omega_ae_bind; [eauto|]. intros x Hx.
    pose proof ((proj1 (Hkernels x)) P Hx) as HkernelP.
    dependent destruction HkernelP. eauto.
  - intros Q HQ. dependent destruction HQ.
    apply free_omega_ae_bind with
      (P := fun x => forall j, free_omega_ae Q (kernels x j)).
    + eapply free_omega_ae_mono.
      2: { apply (proj2 Hsource). constructor. intro i.
        apply free_omega_ae_countable. intro j.
      pose (fuel := i + j).
      assert (Hdiag : free_omega_ae Q
          (free_omega_bind (source fuel)
            (fun x => kernels x fuel))) by eauto.
      apply free_omega_ae_bind_inv in Hdiag.
      pose proof (free_omega_approx_steps Hsource_inc i j) as Hsrc.
      pose proof (free_omega_approx_ae_backward
        (R := eq) Hsrc Hdiag) as Hsrc_ae.
      eapply free_omega_ae_mono in Hsrc_ae.
      2: { intros x [y [-> Hy]]. exact Hy. }
      eapply free_omega_ae_mono; [|exact Hsrc_ae]. intros x Hfuel.
      pose proof (free_omega_approx_steps (Hkernels_inc x) j i) as Hkernel.
      replace (j + i) with fuel in Hkernel by
        (unfold fuel; apply Nat.add_comm).
      pose proof (free_omega_approx_ae_backward
        (R := eq) Hkernel Hfuel) as Hj.
      eapply free_omega_ae_mono; [|exact Hj].
      intros y [z [-> Hz]]. exact Hz. }
      intros x [y [-> Hy]]. exact Hy.
    + intros x Hx. apply (proj2 (Hkernels x) Q). constructor. exact Hx.
Qed.

Lemma free_omega_support_lift_double_diagonal {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    {A} (grid : nat -> nat -> FreeOmega MN A) :
  (forall outer inner,
    free_omega_approx eq (grid outer inner) (grid outer (S inner))) ->
  (forall outer inner,
    free_omega_approx eq (grid outer inner) (grid (S outer) inner)) ->
  free_omega_support_lift eq
    (FOLub (fun outer => FOLub (grid outer)))
    (FOLub (fun fuel => grid fuel fuel)).
Proof.
  intros Hrows Hcols. split.
  - intros P HP. dependent destruction HP. constructor. intro fuel.
    match goal with
    | Houter : forall i : nat, _ |- _ =>
      specialize (Houter fuel); dependent destruction Houter
    end.
    eapply free_omega_ae_mono; [|eauto].
    intros x Hx. exists x. split; [reflexivity|exact Hx].
  - intros P HP. dependent destruction HP. constructor. intro outer.
    constructor. intro inner. pose (fuel := outer + inner).
    assert (Hfuel : free_omega_ae P (grid fuel fuel)) by eauto.
    pose proof (free_omega_approx_steps (Hrows outer) inner outer) as Hrow.
    replace (inner + outer) with fuel in Hrow by
      (unfold fuel; apply Nat.add_comm).
    pose proof (free_omega_approx_steps
      (fun n => Hcols n fuel) outer inner) as Hcol.
    pose proof (free_omega_approx_trans Hrow Hcol) as Happrox.
    pose proof (free_omega_approx_ae_backward
      (R := eq) Happrox Hfuel) as Hback.
    eapply free_omega_ae_mono; [|exact Hback].
    intros x [y [-> Hy]]. exists y. split; [reflexivity|exact Hy].
Qed.

(** An observation-closed coupling for the free omega completion.  The
    structural lifting above remains useful for syntax-directed proofs, but
    it deliberately cannot identify, for example, a formal omega limit with
    a single sampling node.  [free_omega_qlift] is the least relation which
    also admits couplings between low-universe observations and is closed
    under the algebraic operations needed by the generic development. *)
Polymorphic Inductive free_omega_qlift {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NO : @SemanticOmegaInterface MN NI}
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
      free_omega_chains_cofinal R left right ->
      free_omega_qlift R (FOLub left) (FOLub right).

Theorem free_omega_qlift_support {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    `{NO : @SemanticOmegaInterface MN NI}
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
  - destruct H as [Hlr Hrl]. split.
    + intros P HP. dependent destruction HP. constructor. intro m.
      destruct (Hrl m) as [n Happrox].
      eapply free_omega_approx_ae_backward; [exact Happrox|]. eauto.
    + intros Q HQ. dependent destruction HQ. constructor. intro n.
      destruct (Hlr n) as [m Happrox].
      eapply free_omega_approx_ae_backward; [exact Happrox|]. eauto.
Qed.

#[global] Polymorphic Instance FreeOmegaObservableSemanticMeasureInterface
    {MN} `{NI : SemanticMeasureInterface MN}
    `{NO : @SemanticOmegaInterface MN NI} :
    SemanticMeasureInterface (FreeOmega MN) := {
  sem_ret := @FORet MN;
  sem_bind := @free_omega_bind MN;
  sem_eq := fun A => @free_omega_qlift MN NI NO A A eq;
  sem_ae := fun A mu P => @free_omega_ae MN NI A P mu;
  sem_lift := @free_omega_qlift MN NI NO
}.

Lemma free_omega_observable_sem_retE {MN}
    `{NI : SemanticMeasureInterface MN}
    `{NO : @SemanticOmegaInterface MN NI} {A} (x : A) :
  @sem_ret (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    A x = FORet x.
Proof. reflexivity. Qed.

Section FreeOmegaObservableLaws.
Context {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.

Lemma free_omega_qlift_refl {A} (R : A -> A -> Prop) mu :
  Reflexive R -> free_omega_qlift R mu mu.
Proof. intro HR. apply FOQLStructural, free_omega_lift_refl, HR. Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureCoreLaws :
    @SemanticMeasureCoreLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO)).
Proof.
  constructor.
  - intros A mu. apply free_omega_qlift_refl. intros x. reflexivity.
  - intros A mu nu H. apply FOQLSym.
    eapply FOQLMono; [exact H|]. intros x y ->. reflexivity.
  - intros A mu nu xi Hmn Hnx.
    refine (FOQLComp (R := eq) Hmn Hnx _).
    intros x z [y [-> ->]]. reflexivity.
  - intros A mu. induction mu.
    + constructor. exact I.
    + constructor.
    + eapply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros x _. exact (H x).
    + constructor. exact H.
  - intros A mu P Q HPQ Hae.
    exact (free_omega_ae_mono (P := P) (Q := Q) (mu := mu) HPQ Hae).
  - intros A mu P Q HP HQ.
    exact (free_omega_ae_conj (P := P) (Q := Q) (mu := mu) HP HQ).
  - intros A B R T mu nu HRT H.
    eapply FOQLMono; eauto.
  - intros A R mu HR. apply free_omega_qlift_refl. exact HR.
  - intros A B R x y Hxy. apply FOQLStructural. constructor. exact Hxy.
  - intros A B R mu mu' nu Hmm Hmn.
    assert (Hmm' : free_omega_qlift eq mu' mu).
    { apply FOQLSym. eapply FOQLMono; [exact Hmm|].
      intros x y ->. reflexivity. }
    refine (FOQLComp (R := R) Hmm' Hmn _).
    intros x z [y [-> Hyz]]. exact Hyz.
  - intros A B R mu nu nu' Hnn Hmn.
    refine (FOQLComp (R := R) Hmn Hnn _).
    intros x z [y [Hxy ->]]. exact Hxy.
  - intros A B R mu nu H. apply FOQLSym. exact H.
  - intros A B C R T mu nu xi Hmn Hnx.
    refine (FOQLComp (R := fun x z => exists y, R x y /\ T y z)
      Hmn Hnx _).
    intros x z Hxz. exact Hxz.
Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureAEKleisliLaws :
    @SemanticMeasureAEKleisliLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO)).
Proof.
  constructor.
  - intros A P x Hx. constructor. exact Hx.
  - intros A B mu k P Q Hmu Hk.
    cbn in Hmu, Hk |- *. exact (free_omega_ae_bind Hmu Hk).
Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureCountableAELaws
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI} :
    @SemanticMeasureCountableAELaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO)).
Proof.
  constructor. intros A mu P HP. apply free_omega_ae_countable. exact HP.
Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureCouplingAELaws
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI} :
    @SemanticMeasureCouplingAELaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO)).
Proof.
  constructor.
  - intros A B R mu nu P Hlift HP.
    exact (proj1 (free_omega_qlift_support Hlift) P HP).
  - intros A B R mu nu P Q Hlift HP HQ.
    eapply FOQLAERestrict with (T := R) (P := P) (Q := Q).
    + exact Hlift.
    + exact HP.
    + exact HQ.
    + intros x y Hxy. exact Hxy.
Qed.

Lemma free_omega_qlift_bind_ae
    `{NAE : @SemanticMeasureAELiftLaws MN NI}
    {A B} (mu : FreeOmega MN A) (k h : A -> FreeOmega MN B) :
  free_omega_ae (fun x => free_omega_qlift eq (k x) (h x)) mu ->
  free_omega_qlift eq (free_omega_bind mu k) (free_omega_bind mu h).
Proof.
  intro Hae. induction Hae; cbn.
  - exact H.
  - apply FOQLStructural. constructor.
  - eapply FOQLSample with (T := fun x y => x = y /\ Good x).
    + exact (sem_lift_refl_ae H).
    + intros x y [-> Hy]. exact (H1 y Hy).
  - apply FOQLLub. exact H0.
Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureBindLaws
    `{NAE : @SemanticMeasureAELiftLaws MN NI} :
    @SemanticMeasureBindLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO)).
Proof.
  constructor.
  - intros A B x k. apply free_omega_qlift_refl. intros y. reflexivity.
  - intros A B C mu k h.
    change (free_omega_qlift eq
      (free_omega_bind (free_omega_bind mu k) h)
      (free_omega_bind mu (fun x => free_omega_bind (k x) h))).
    rewrite free_omega_bind_assoc.
    apply free_omega_qlift_refl. intros y. reflexivity.
  - intros A B mu k h Hae. exact (free_omega_qlift_bind_ae Hae).
  - intros A B C D R T mu nu k h Hmn Hkh.
    eapply FOQLBind; eauto.
Qed.

#[global] Instance FreeOmegaObservableMixedMeasureLaws
    `{NAE : @SemanticMeasureAELiftLaws MN NI} :
    @MixedMeasureLaws MN (FreeOmega MN) NI
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface.
Proof.
  constructor.
  - intros A B mu k h Hae.
    eapply FOQLSample with (T := fun x y => x = y /\
      free_omega_qlift eq (k x) (h x)).
    + exact (sem_lift_refl_ae Hae).
    + intros x y [-> Hxy]. exact Hxy.
  - intros A B C mu k h.
    apply free_omega_qlift_refl. intros x. reflexivity.
  - intros A B C D R T mu nu k h Hmn Hkh.
    eapply FOQLSample; eauto.
Qed.

#[global] Polymorphic Instance FreeOmegaObservableSemanticOmegaInterface :
    @SemanticOmegaInterface (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO)) := {
  sem_zero := @FOZero MN;
  sem_le := fun A => @free_omega_approx MN NI A A eq;
  sem_lub := fun A chain out =>
    @sem_eq (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO)) A
      out (FOLub chain);
  sem_total := fun A mu => exists (O : Type) (obs : A -> O) (out : MN O),
    free_omega_observes obs mu out /\ sem_total out
}.

Lemma free_omega_cofinal_lub_iff {A}
    (left right : nat -> FreeOmega MN A) out :
  free_omega_chains_cofinal eq left right ->
  @sem_lub (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface A left out <->
  @sem_lub (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface A right out.
Proof.
  intro Hcofinal. cbn. split; intro Hlim.
  - refine (FOQLComp (R := eq) Hlim (FOQLCofinal Hcofinal) _).
    intros x z [y [-> ->]]. reflexivity.
  - refine (FOQLComp (R := eq) Hlim (FOQLSym (FOQLCofinal Hcofinal)) _).
    intros x z [y [-> ->]]. reflexivity.
Qed.

#[global] Instance FreeOmegaObservableSemanticOmegaLaws :
    @SemanticOmegaLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmegaInterface.
Proof.
  constructor.
  - intros A chain _. exists (FOLub chain).
    cbn.
    apply free_omega_qlift_refl. intros x. reflexivity.
  - intros A chain mu nu Hmu Hnu.
    cbn in Hmu, Hnu |- *.
    eapply (@sem_eq_trans _
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A); [exact Hmu|].
    eapply (@sem_eq_sym _
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A). exact Hnu.
  - intros A chain chain' mu nu Hcc Hmu Hnu.
    cbn in Hcc, Hmu, Hnu |- *.
    eapply (@sem_eq_trans _
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A); [exact Hmu|].
    eapply (@sem_eq_trans _
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A).
    + apply FOQLLub. exact Hcc.
    + eapply (@sem_eq_sym _
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws A). exact Hnu.
  - intros A chain chain' mu Hcc Hmu.
    cbn in Hcc, Hmu |- *.
    eapply (@sem_eq_trans _
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A); [exact Hmu|].
    apply FOQLLub. exact Hcc.
  - intros A B chain mu k _ Hmu.
    cbn in Hmu |- *.
    change (free_omega_qlift eq (free_omega_bind mu k)
      (free_omega_bind (FOLub chain) k)).
    eapply FOQLBind with (T := eq); [exact Hmu|].
    intros x y ->. apply free_omega_qlift_refl.
    intros z. reflexivity.
Qed.

#[global] Instance FreeOmegaObservableSemanticOmegaAELaws
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI} :
    @SemanticOmegaAELaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmegaInterface.
Proof.
  constructor.
  - intros A P. constructor.
  - intros A chain out P Hlub HP. cbn in Hlub.
    pose proof (free_omega_qlift_support Hlub) as Hsupport.
    assert (Hchain : free_omega_ae P (FOLub chain)).
    { constructor. exact HP. }
    pose proof ((proj2 Hsupport) P Hchain) as Himage.
    eapply free_omega_ae_mono; [|exact Himage].
    intros x [y [Hxy Hy]]. subst y. exact Hy.
Qed.

#[global] Instance FreeOmegaObservableSemanticOmegaCofinalityLaws :
    @SemanticOmegaCofinalityLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmegaInterface.
Proof.
  constructor.
  - intros A chain out. cbn. split; intro Hlim.
    + eapply (@sem_eq_trans _
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A); [exact Hlim|].
      apply FOQLLubZeroPrefixR. intro n.
      apply free_omega_qlift_refl. intros x. reflexivity.
    + eapply (@sem_eq_trans _
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws A); [exact Hlim|].
      apply FOQLLubZeroPrefixL. intro n.
      apply free_omega_qlift_refl. intros x. reflexivity.
  - intros A mu. cbn. apply FOQLLubConstantR.
    apply free_omega_qlift_refl. intros x. reflexivity.
Qed.

#[global] Instance FreeOmegaObservableMixedMeasureOmegaLaws :
    @MixedMeasureOmegaLaws MN (FreeOmega MN) NI
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface.
Proof.
  constructor.
  - intros A B mu. cbn. apply FOQLSampleZero.
  - intros A B mu Good chain out Hae _ Hlim.
    cbn in Hlim |- *.
    eapply FOQLSampleLub; eauto.
Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureDiagonalLaws
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI} :
    @SemanticMeasureDiagonalLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmegaInterface.
Proof.
  constructor. intros A B source source_out kernels kernel_out
    Hsource_inc Hkernels_inc Hsource Hkernels.
  cbn in Hsource, Hkernels |- *.
  eapply FOQLBindLub; [exact Hsource|exact Hkernels|].
  eapply free_omega_support_lift_bind_diagonal; eauto.
  - apply free_omega_qlift_support. exact Hsource.
  - intro x. apply free_omega_qlift_support. exact (Hkernels x).
Qed.

#[global] Instance FreeOmegaObservableSemanticOmegaFubiniLaws
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI} :
    @SemanticOmegaFubiniLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmegaInterface.
Proof.
  constructor. intros A grid row_out out Hrows_inc Hcols_inc Hrows Hout.
  cbn in Hrows, Hout |- *.
  eapply (@sem_eq_trans _
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws A); [exact Hout|].
  eapply (@sem_eq_trans _
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws A).
  - apply FOQLLub. exact Hrows.
  - eapply FOQLDoubleDiagonal with (HAB := eq_refl) (grid := grid).
    + intros outer inner. exact (Hrows_inc outer inner).
    + intros outer inner. exact (Hcols_inc inner outer).
    + intros x. reflexivity.
    + apply free_omega_support_lift_double_diagonal.
      * intros outer inner. exact (Hrows_inc outer inner).
      * intros outer inner. exact (Hcols_inc inner outer).
Qed.

#[global] Instance FreeOmegaObservableSemanticMeasureOrderLaws :
    @SemanticMeasureOrderLaws (FreeOmega MN)
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmegaInterface.
Proof.
  constructor.
  - intros A mu. apply free_omega_approx_refl. intros x. reflexivity.
  - intros A mu nu xi Hmn Hnx.
    eapply free_omega_approx_mono with
      (R := fun x z => exists mid, x = mid /\ mid = z).
    + intros x z [mid [-> ->]]. reflexivity.
    + exact (free_omega_approx_comp (R := eq) (T := eq) Hmn Hnx).
  - intros A mu. constructor.
  - intros A B mu nu k Hmn.
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + exact Hmn.
    + intros x y ->. apply free_omega_approx_refl.
      intros z. reflexivity.
  - intros A B mu k h Hkh.
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply free_omega_approx_refl. intros x. reflexivity.
    + intros x y ->. apply Hkh.
Qed.

End FreeOmegaObservableLaws.
