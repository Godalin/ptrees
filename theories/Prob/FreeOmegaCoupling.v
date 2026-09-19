Set Universe Polymorphism.
From Coq Require Import Logic.ClassicalChoice.
From PTree.Prob Require Import TwoLevelMeasure SemanticCoupling FreeOmegaMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section StructuralRealization.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation SI := (FreeOmegaSemanticMeasure (NI := NI)).

(** A concrete witness-extraction theorem for the node backend, not an
    added law of the measure interface.  Enum/SubEnum discharge this premise
    by their existing position-indexed joint weights. *)
Hypothesis node_realizes : forall {X Y} (S : X -> Y -> Prop)
    (mu : MN X) (nu : MN Y), sem_lift S mu nu ->
    exists joint, semantic_coupling S mu nu joint.

(** Structural couplings, including their Lub case, have actual joint
    FreeOmega measures.  This theorem deliberately does not replace its
    premise by the larger quotient relation [free_omega_qlift].  In
    particular, realization of its observation and composition rules is
    not inferred just from the support-transport theorem.  In the Lub case
    the selected row joints are not asserted to form an increasing chain;
    their graph marginals and AE support suffice for this certificate, but
    not for a later use of cofinality or diagonalization. *)
Theorem free_omega_lift_structural_realization {A B} (R : A -> B -> Prop)
    (mu : MF A) (nu : MF B) :
  free_omega_lift R mu nu ->
  exists joint, @semantic_coupling MF SI A B R mu nu joint.
Proof.
  intro Hlift. induction Hlift as
    [x y Hxy | | X Y S mu nu k h Hnode Hbranches IH | c d Hbranches IH].
  - exists (FORet (x,y)). split.
    + apply FOLRet. reflexivity.
    + split.
      * apply FOLRet. reflexivity.
      * apply FOAERet. exact Hxy.
  - exists FOZero. split.
    + apply FOLZero.
    + split; [apply FOLZero|apply FOAEZero].
  - destruct (node_realizes Hnode) as [node_joint Hjoint].
    assert (Hex : forall p : X * Y, exists joint : MF (A * B),
      S (fst p) (snd p) ->
      @semantic_coupling MF SI A B R (k (fst p)) (h (snd p)) joint).
    { intros [x y]. destruct (classic (S x y)) as [Hxy|Hnot].
      - destruct (IH x y Hxy) as [joint Hgood].
        exists joint. intros _. exact Hgood.
      - exists FOZero. intro Hxy. contradiction. }
    destruct (choice _ Hex) as [next_joint Hnext].
    exists (FOSample node_joint next_joint). split.
    + eapply FOLSample.
      * exact (semantic_coupling_left_supported Hjoint).
      * intros [x y] z [<- Hxy]. exact (proj1 (Hnext (x,y) Hxy)).
    + split.
      * eapply FOLSample.
        -- exact (semantic_coupling_right_supported Hjoint).
        -- intros [x y] z [<- Hxy]. exact (proj1 (proj2 (Hnext (x,y) Hxy))).
      * apply FOAESample with (Good := fun p => S (fst p) (snd p)).
        -- exact (proj2 (proj2 Hjoint)).
        -- intros [x y] Hxy. exact (proj2 (proj2 (Hnext (x,y) Hxy))).
  - destruct (choice _ IH) as [joint Hjoint].
    exists (FOLub joint). split.
    + apply FOLLub. intro n. exact (proj1 (Hjoint n)).
    + split.
      * apply FOLLub. intro n. exact (proj1 (proj2 (Hjoint n))).
      * apply FOAELub. intro n. exact (proj2 (proj2 (Hjoint n))).
Qed.

(** The observable endpoint follows by embedding the two structural graph
    couplings.  Retaining the stronger certificate above also permits raw
    approximation arguments without quotient/order transport. *)
Theorem free_omega_lift_realization {A B} (R : A -> B -> Prop)
    (mu : MF A) (nu : MF B) :
  free_omega_lift R mu nu ->
  exists joint, @semantic_coupling MF FI A B R mu nu joint.
Proof.
  intro Hlift.
  destruct (free_omega_lift_structural_realization Hlift)
    as [joint [Hl [Hr Hae]]].
  exists joint. split; [apply FOQLStructural; exact Hl|].
  split; [apply FOQLStructural; exact Hr|exact Hae].
Qed.

(** A many-to-many structural coupling remains realizable after arbitrary
    quotient EQUALITY rewrites of its marginals.  This is more general than
    graph realization, but does not assert that every relational quotient
    derivation has a structural core up to equality. *)
Theorem free_omega_lift_realization_mod_eq {A B} (R : A -> B -> Prop)
    (mu mu' : MF A) (nu nu' : MF B) :
  free_omega_lift R mu nu ->
  free_omega_qlift eq mu mu' -> free_omega_qlift eq nu nu' ->
  exists joint, @semantic_coupling MF FI A B R mu' nu' joint.
Proof.
  intros Hlift Hmu Hnu.
  destruct (free_omega_lift_realization Hlift) as [joint Hjoint].
  exists joint. eapply semantic_coupling_transport; eassumption.
Qed.

End StructuralRealization.

Section GraphRealization.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

Lemma free_omega_bind_return_lift {A} (mu : MF A) :
  free_omega_lift eq (free_omega_bind mu (fun x => FORet x)) mu.
Proof.
  induction mu as [x| |X mu k IH|chain IH]; cbn.
  - apply FOLRet. reflexivity.
  - apply FOLZero.
  - apply FOLSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. apply IH.
  - apply FOLLub. exact IH.
Qed.

Definition free_omega_graph_joint {A B} (f : A -> B) (mu : MF A) : MF (A * B) :=
  free_omega_bind mu (fun x => FORet (x, f x)).

Lemma free_omega_graph_joint_left {A B} (f : A -> B) (mu : MF A) :
  free_omega_lift (fun p x => fst p = x) (free_omega_graph_joint f mu) mu.
Proof.
  unfold free_omega_graph_joint. induction mu as [x| |X mu k IH|chain IH]; cbn.
  - apply FOLRet. reflexivity.
  - apply FOLZero.
  - apply FOLSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. apply IH.
  - apply FOLLub. exact IH.
Qed.

Lemma free_omega_graph_joint_support {A B} (f : A -> B) (mu : MF A) :
  free_omega_ae (fun p => f (fst p) = snd p) (free_omega_graph_joint f mu).
Proof.
  unfold free_omega_graph_joint. induction mu as [x| |X mu k IH|chain IH]; cbn.
  - apply FOAERet. reflexivity.
  - apply FOAEZero.
  - apply FOAESample with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros x _. apply IH.
  - apply FOAELub. exact IH.
Qed.

(** Unlike the structural theorem, this handles the FULL quotient lifting.
    The graph premise supplies the functional correspondence explicitly;
    arbitrary relational couplings are not assumed to be functional. *)
Theorem free_omega_qlift_graph_realization {A B} (f : A -> B)
    (mu : MF A) (nu : MF B) :
  free_omega_qlift (fun x y => f x = y) mu nu ->
  @semantic_coupling MF FI A B (fun x y => f x = y) mu nu
    (free_omega_graph_joint f mu).
Proof.
  intro Hlift. split.
  - apply FOQLStructural. apply free_omega_graph_joint_left.
  - split.
    + eapply FOQLComp with (T := fun p y => snd p = y) (U := eq)
        (mid := free_omega_bind nu (fun y => FORet y)).
      * unfold free_omega_graph_joint. eapply FOQLBind; [exact Hlift|].
        intros x y Hxy. apply FOQLStructural, FOLRet. exact Hxy.
      * apply FOQLStructural. apply free_omega_bind_return_lift.
      * intros p y [z [Hp ->]]. exact Hp.
    + apply free_omega_graph_joint_support.
Qed.

Corollary free_omega_qlift_eq_realization {A} (mu nu : MF A) :
  free_omega_qlift eq mu nu ->
  @semantic_coupling MF FI A A eq mu nu
    (free_omega_graph_joint (fun x => x) mu).
Proof.
  intro H. exact (free_omega_qlift_graph_realization (f := fun x => x) H).
Qed.

End GraphRealization.
