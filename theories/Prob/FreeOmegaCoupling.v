Set Universe Polymorphism.
From Coq Require Import Logic.ClassicalChoice Program.Equality.
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

(** The sample constructor does not require structural branch couplings:
    any already-realized quotient couplings can be composed underneath it. *)
Theorem free_omega_sample_coupling_realization {X Y A B}
    (S : X -> Y -> Prop) (R : A -> B -> Prop)
    (mu : MN X) (nu : MN Y) (k : X -> MF A) (h : Y -> MF B) :
  sem_lift S mu nu ->
  (forall x y, S x y ->
    exists joint, @semantic_coupling MF FI A B R (k x) (h y) joint) ->
  exists joint, @semantic_coupling MF FI A B R (FOSample mu k) (FOSample nu h) joint.
Proof.
  intros Hnode Hbranches. destruct (node_realizes Hnode) as [node_joint Hjoint].
  assert (Hex : forall p : X * Y, exists branch : MF (A * B),
    S (fst p) (snd p) ->
    @semantic_coupling MF FI A B R (k (fst p)) (h (snd p)) branch).
  { intros [x y]. destruct (classic (S x y)) as [Hxy|Hnot].
    - destruct (Hbranches x y Hxy) as [branch Hbranch].
      exists branch. intros _. exact Hbranch.
    - exists FOZero. intro Hxy. contradiction. }
  destruct (choice _ Hex) as [next_joint Hnext].
  exists (FOSample node_joint next_joint). split.
  - eapply FOQLSample; [exact (semantic_coupling_left_supported Hjoint)|].
    intros [x y] z [<- Hxy]. exact (proj1 (Hnext (x,y) Hxy)).
  - split.
    + eapply FOQLSample; [exact (semantic_coupling_right_supported Hjoint)|].
      intros [x y] z [<- Hxy]. exact (proj1 (proj2 (Hnext (x,y) Hxy))).
    + apply FOAESample with (Good := fun p => S (fst p) (snd p)).
      * exact (proj2 (proj2 Hjoint)).
      * intros [x y] Hxy. exact (proj2 (proj2 (Hnext (x,y) Hxy))).
Qed.

(** This realizes the FORMAL Lub constructor.  No monotonicity of the
    selected joint rows is asserted; the theorem must not be used as a
    monotone joint-limit selection result in an adequacy argument. *)
Theorem free_omega_lub_coupling_realization {A B} (R : A -> B -> Prop)
    (left : nat -> MF A) (right : nat -> MF B) :
  (forall n, exists joint, @semantic_coupling MF FI A B R (left n) (right n) joint) ->
  exists joint, @semantic_coupling MF FI A B R (FOLub left) (FOLub right) joint.
Proof.
  intro Hrows. destruct (choice _ Hrows) as [joint Hjoint].
  exists (FOLub joint). split.
  - apply FOQLLub. intro n. exact (proj1 (Hjoint n)).
  - split.
    + apply FOQLLub. intro n. exact (proj1 (proj2 (Hjoint n))).
    + apply FOAELub. intro n. exact (proj2 (proj2 (Hjoint n))).
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

(** A native sample of total mass may be forgotten when each branch has
    the same related behavior.  The native coupling to a Dirac measure
    proves the mass premise; it is not inferred merely from AE support.
    Results may live above the native carrier universe. *)
Theorem free_omega_sample_to_constant {X Y A B}
    (mu : MN X) (point : Y) (R : A -> B -> Prop)
    (k : X -> MF A) (nu : MF B) :
  (forall P, sem_ae (sem_ret point) P <-> P point) ->
  sem_same_mass mu (sem_ret point) ->
  (forall x, free_omega_qlift R (k x) nu) ->
  free_omega_qlift R (FOSample mu k) nu.
Proof.
  intros Hdirac Hmass Hbranches.
  eapply FOQLComp with (T := R) (U := eq)
    (mid := FOSample (sem_ret point) (fun _ => nu)).
  - eapply FOQLSample; [exact Hmass|]. intros x y _. apply Hbranches.
  - apply FOQLSampleRetL; [exact Hdirac|].
    apply free_omega_qlift_refl. intro b. reflexivity.
  - intros a b [c [Hac ->]]. exact Hac.
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

(** Converse is realized by swapping the sampled pair.  Marginal bind/Ret
    normalization is proved for FreeOmega, not assumed as an additional
    generic right-unit capability. *)
Theorem free_omega_coupling_converse {A B} (R : A -> B -> Prop)
    (mu : MF A) (nu : MF B) joint :
  @semantic_coupling MF FI A B R mu nu joint ->
  @semantic_coupling MF FI B A (fun y x => R x y) nu mu
    (free_omega_bind joint (fun p => FORet (snd p, fst p))).
Proof.
  intros [Hl [Hr Hae]]. split.
  - eapply FOQLComp with (T := fun p y => fst p = y) (U := eq)
      (mid := free_omega_bind nu (fun y => FORet y)).
    + eapply FOQLBind; [exact Hr|].
      intros p y Hpy. apply FOQLStructural, FOLRet. exact Hpy.
    + apply FOQLStructural, free_omega_bind_return_lift.
    + intros p y [z [Hp ->]]. exact Hp.
  - split.
    + eapply FOQLComp with (T := fun p x => snd p = x) (U := eq)
        (mid := free_omega_bind mu (fun x => FORet x)).
      * eapply FOQLBind; [exact Hl|].
        intros p x Hpx. apply FOQLStructural, FOLRet. exact Hpx.
      * apply FOQLStructural, free_omega_bind_return_lift.
      * intros p x [z [Hp ->]]. exact Hp.
    + eapply free_omega_ae_bind; [exact Hae|].
      intros [x y] Hxy. apply FOAERet. exact Hxy.
Qed.

End GraphRealization.

(** Gluing is factored through a concrete equality-fiber witness.  This
    section neither assumes a new gluing class nor asserts that arbitrary
    quotient couplings have realizations. *)
Section Gluing.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

Lemma free_omega_qlift_map_left {A B C} (f : A -> B) (R : B -> C -> Prop)
    (mu : MF A) (nu : MF C) :
  free_omega_qlift (fun x y => R (f x) y) mu nu ->
  free_omega_qlift R (free_omega_bind mu (fun x => FORet (f x))) nu.
Proof.
  intro Hlift. eapply FOQLComp with (T := R) (U := eq)
    (mid := free_omega_bind nu (fun y => FORet y)).
  - eapply FOQLBind; [exact Hlift|].
    intros x y Hxy. apply FOQLStructural, FOLRet. exact Hxy.
  - apply FOQLStructural, free_omega_bind_return_lift.
  - intros x z [y [Hxy ->]]. exact Hxy.
Qed.

(** Once a joint of the two existing witnesses matches the middle values,
    project away those values.  Its outer marginals are the ORIGINAL mu/nu,
    and its support is relational composition. *)
Theorem free_omega_coupling_glue {A B C}
    (R : A -> B -> Prop) (T : B -> C -> Prop)
    (mu : MF A) (mid : MF B) (nu : MF C) left_joint right_joint fiber_joint :
  @semantic_coupling MF FI A B R mu mid left_joint ->
  @semantic_coupling MF FI B C T mid nu right_joint ->
  @semantic_coupling MF FI (A * B) (B * C)
    (fun p q => snd p = fst q) left_joint right_joint fiber_joint ->
  @semantic_coupling MF FI A C (fun x z => exists y, R x y /\ T y z) mu nu
    (free_omega_bind fiber_joint (fun w => FORet (fst (fst w), snd (snd w)))).
Proof.
  intros Hl Hr Hfiber. split.
  - apply free_omega_qlift_map_left.
    eapply FOQLComp with (T := fun w p => fst w = p)
      (U := fun p x => fst p = x) (mid := left_joint).
    + exact (proj1 Hfiber).
    + exact (proj1 Hl).
    + intros w x [p [<- Hp]]. exact Hp.
  - split.
    + apply free_omega_qlift_map_left.
      eapply FOQLComp with (T := fun w q => snd w = q)
        (U := fun q z => snd q = z) (mid := right_joint).
      * exact (proj1 (proj2 Hfiber)).
      * exact (proj1 (proj2 Hr)).
      * intros w z [q [<- Hq]]. exact Hq.
    + eapply free_omega_ae_bind.
      * exact (semantic_coupling_fiber_support Hl Hr Hfiber).
      * intros [[x y] [y' z]] [Heq [HR HT]]. cbn in *.
        apply FOAERet. exists y. split; [exact HR|now rewrite Heq].
Qed.

(** This proved case supplies the fiber witness by structural extraction,
    while the two given marginal certificates may be quotient-level.  The
    structural premise is explicit, not inferred from [fiber_lift]. *)
Theorem free_omega_coupling_glue_structural {A B C}
    (R : A -> B -> Prop) (T : B -> C -> Prop)
    (mu : MF A) (mid : MF B) (nu : MF C) left_joint right_joint
    (node_realizes : forall {X Y} (S : X -> Y -> Prop)
      (mu : MN X) (nu : MN Y), sem_lift S mu nu ->
      exists joint, semantic_coupling S mu nu joint) :
  @semantic_coupling MF FI A B R mu mid left_joint ->
  @semantic_coupling MF FI B C T mid nu right_joint ->
  free_omega_lift (fun p q => snd p = fst q) left_joint right_joint ->
  exists joint, @semantic_coupling MF FI A C
    (fun x z => exists y, R x y /\ T y z) mu nu joint.
Proof.
  intros Hl Hr Hfiber.
  destruct (free_omega_lift_realization node_realizes Hfiber) as [joint Hjoint].
  eexists. exact (free_omega_coupling_glue Hl Hr Hjoint).
Qed.

End Gluing.

(** A single quotient joint certificate need not expose structural
    marginals.  These TWO equivalent presentations retain one structural
    marginal each.  This is proof data, not another lifting or a new law:
    no converse from arbitrary quotient lifting is asserted. *)
Section ReferenceCertificates.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation SI := (FreeOmegaSemanticMeasure (NI := NI)).

Definition free_omega_coupling_references {A B} (R : A -> B -> Prop)
    (mu : MF A) (nu : MF B) (left right : MF (A * B)) : Prop :=
  free_omega_qlift eq left right /\
  free_omega_lift (fun p x => fst p = x) left mu /\
  free_omega_lift (fun p y => snd p = y) right nu /\
  free_omega_ae (fun p => R (fst p) (snd p)) left.

Lemma free_omega_coupling_references_right_ae {A B} (R : A -> B -> Prop)
    (mu : MF A) (nu : MF B) left right :
  free_omega_coupling_references R mu nu left right ->
  free_omega_ae (fun p => R (fst p) (snd p)) right.
Proof.
  intros [Heq [_ [_ Hae]]].
  pose proof (proj1 (free_omega_qlift_support Heq) _ Hae) as Hsupport.
  eapply free_omega_ae_mono; [|exact Hsupport].
  intros p [q [-> Hq]]. exact Hq.
Qed.

Lemma free_omega_coupling_references_left_supported {A B} (R : A -> B -> Prop)
    (mu : MF A) (nu : MF B) left right :
  free_omega_coupling_references R mu nu left right ->
  free_omega_lift (fun p x => fst p = x /\ R (fst p) (snd p)) left mu.
Proof.
  intros [_ [Hl [_ Hae]]].
  eapply free_omega_lift_mono;
    [|eapply free_omega_lift_ae_restrict;
      [exact Hl|exact Hae|apply (@sem_ae_true MF FI FreeOmegaObservableSemanticMeasureCoreLaws)]].
  intros p x [Hp [HR _]]. split; assumption.
Qed.

Lemma free_omega_coupling_references_right_supported {A B} (R : A -> B -> Prop)
    (mu : MF A) (nu : MF B) left right :
  free_omega_coupling_references R mu nu left right ->
  free_omega_lift (fun p y => snd p = y /\ R (fst p) (snd p)) right nu.
Proof.
  intro H. pose proof (free_omega_coupling_references_right_ae H) as Hright.
  destruct H as [Heq [Hl [Hr Hae]]].
  eapply free_omega_lift_mono;
    [|eapply free_omega_lift_ae_restrict;
      [exact Hr|exact Hright|apply (@sem_ae_true MF FI FreeOmegaObservableSemanticMeasureCoreLaws)]].
  intros p y [Hp [HR _]]. split; assumption.
Qed.

Theorem free_omega_coupling_references_realize {A B} (R : A -> B -> Prop)
    (mu : MF A) (nu : MF B) left right :
  free_omega_coupling_references R mu nu left right ->
  @semantic_coupling MF FI A B R mu nu left.
Proof.
  intros [Heq [Hl [Hr Hae]]]. split; [apply FOQLStructural; exact Hl|].
  split; [|exact Hae].
  eapply FOQLComp with (T := eq) (U := fun p y => snd p = y).
  - exact Heq.
  - apply FOQLStructural. exact Hr.
  - intros p y [q [-> Hq]]. exact Hq.
Qed.

Lemma free_omega_structural_coupling_references {A B} (R : A -> B -> Prop)
    (mu : MF A) (nu : MF B) joint :
  @semantic_coupling MF SI A B R mu nu joint ->
  free_omega_coupling_references R mu nu joint joint.
Proof.
  intro H. split; [apply free_omega_qlift_refl; intro p; reflexivity|exact H].
Qed.

(** Equality always has such a witness, even if its proof uses arbitrary
    quotient rules: keep the diagonal graph of EACH original measure. *)
Theorem free_omega_eq_coupling_references {A} (mu nu : MF A) :
  free_omega_qlift eq mu nu ->
  free_omega_coupling_references eq mu nu
    (free_omega_graph_joint (fun x => x) mu)
    (free_omega_graph_joint (fun x => x) nu).
Proof.
  intro H. split.
  - unfold free_omega_graph_joint. eapply FOQLBind; [exact H|].
    intros x y ->. apply FOQLStructural, FOLRet. reflexivity.
  - split; [apply free_omega_graph_joint_left|]. split.
    + eapply free_omega_lift_mono;
        [|eapply free_omega_lift_ae_restrict;
          [apply free_omega_graph_joint_left|
           apply free_omega_graph_joint_support|
           apply (@sem_ae_true MF FI FreeOmegaObservableSemanticMeasureCoreLaws)]].
      intros p y [Hp [Hdiag _]]. cbn in Hdiag. now rewrite <- Hdiag.
    + exact (free_omega_graph_joint_support (fun x : A => x) mu).
Qed.

(** Both branch presentations depend on the full sampled pair.  No
    deterministic partner is chosen and no independence is assumed. *)
Theorem free_omega_coupling_references_bind {A B C D}
    (R : A -> B -> Prop) (T : C -> D -> Prop)
    (mu : MF A) (nu : MF B) left right
    (k : A -> MF C) (h : B -> MF D)
    (branch_left branch_right : A * B -> MF (C * D)) :
  free_omega_coupling_references R mu nu left right ->
  (forall x y, R x y -> free_omega_coupling_references T (k x) (h y)
    (branch_left (x,y)) (branch_right (x,y))) ->
  free_omega_coupling_references T
    (free_omega_bind mu k) (free_omega_bind nu h)
    (free_omega_bind left branch_left) (free_omega_bind right branch_right).
Proof.
  intros Hsource Hbranch. split.
  - eapply FOQLBind with (T := fun p q => p = q /\ R (fst p) (snd p)).
    + eapply FOQLAERestrict with (T := eq)
        (P := fun p => R (fst p) (snd p)) (Q := fun _ => True).
      * exact (proj1 Hsource).
      * exact (proj2 (proj2 (proj2 Hsource))).
      * apply (@sem_ae_true MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
      * intros p q [Hp [HR _]]. split; assumption.
    + intros [x y] q [<- Hxy]. exact (proj1 (Hbranch x y Hxy)).
  - split.
    + eapply free_omega_lift_bind;
        [exact (free_omega_coupling_references_left_supported Hsource)|].
      intros [x y] z [<- Hxy]. exact (proj1 (proj2 (Hbranch x y Hxy))).
    + split.
      * eapply free_omega_lift_bind;
          [exact (free_omega_coupling_references_right_supported Hsource)|].
        intros [x y] z [<- Hxy]. exact (proj1 (proj2 (proj2 (Hbranch x y Hxy)))).
      * eapply free_omega_ae_bind; [exact (proj2 (proj2 (proj2 Hsource)))|].
        intros [x y] Hxy. exact (proj2 (proj2 (proj2 (Hbranch x y Hxy)))).
Qed.

(** Limitation of structural reference marginals: if the right marginal
    is literally Ret, its reference cannot carry hidden randomness.  An
    arbitrary quotient coupling has no such restriction.  In particular,
    these certificates must NOT be assumed to realize every qlift. *)
Theorem free_omega_reference_marginals_ret_deterministic {A B J}
    (project_left : J -> A) (project_right : J -> B)
    (mu : MF A) (b : B) left right :
  free_omega_qlift eq left right ->
  free_omega_lift (fun p x => project_left p = x) left mu ->
  free_omega_lift (fun p y => project_right p = y) right (FORet b) ->
  exists a, free_omega_ae (fun x => x = a) mu.
Proof.
  intros Heq Hl Hr. dependent destruction Hr.
  exists (project_left x).
  assert (Hright : free_omega_ae (fun p : J => project_left p = project_left x) (FORet x)).
  { apply FOAERet. reflexivity. }
  pose proof (proj2 (free_omega_qlift_support Heq) _ Hright) as Hleft.
  assert (Hleft' : free_omega_ae (fun p : J => project_left p = project_left x) left).
  { eapply free_omega_ae_mono; [|exact Hleft].
    intros p [q [-> Hq]]. exact Hq. }
  pose proof (free_omega_lift_ae_transport_r Hl Hleft') as Hmu.
  eapply free_omega_ae_mono; [|exact Hmu].
  intros a [p [<- Hp]]. exact Hp.
Qed.

Corollary free_omega_coupling_references_ret_deterministic {A B}
    (R : A -> B -> Prop) (mu : MF A) (b : B) left right :
  free_omega_coupling_references R mu (FORet b) left right ->
  exists a, free_omega_ae (fun x => x = a) mu.
Proof.
  intros [Heq [Hl [Hr Hae]]].
  exact (free_omega_reference_marginals_ret_deterministic Heq Hl Hr).
Qed.

End ReferenceCertificates.
