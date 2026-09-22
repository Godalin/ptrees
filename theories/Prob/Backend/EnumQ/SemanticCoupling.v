(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From Coq Require Import List.
From Coq.Logic Require Import ClassicalDescription.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg order rat.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling PTree.Prob.Backend.EnumQ.IndexedCoupling PTree.Prob.Backend.EnumQ.FrontierLift.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure.
From PTree.Prob.Interface Require Import SemanticCoupling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling IndexedCoupling.
Import GRing.Theory Order.Theory.
Local Open Scope ring_scope.

(** A proof-local carrier wrapper avoids both a client equality constraint
    and the stronger propositional-extensionality dependency of boolp's
    general-purpose classical carrier. *)
Module EnumQCouplingClassical.
Definition carrier (A : Type) := A.
Definition equal {A} (x y : carrier A) : bool :=
  if excluded_middle_informative (x = y) then true else false.
Lemma equalP A : Equality.axiom (@equal A).
Proof.
  intros x y. unfold equal.
  destruct (excluded_middle_informative (x = y)) as [H|H]; constructor; exact H.
Qed.
HB.instance Definition _ A := hasDecEq.Build (carrier A) (@equalP A).
End EnumQCouplingClassical.
Import EnumQCouplingClassical.

(** Recover values from the existing position-indexed coupling.  This is
    the inverse of [indexed_coupling_of_coupling] once value equality is
    available; callers over arbitrary types use local classical equality,
    without adding an eqType requirement to the public statement. *)
Lemma indexed_coupling_to_coupling {A B : eqType}
    (R : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B) :
  indexed_coupling R mu nu -> coupling R mu nu.
Proof.
  intro Hidx.
  pose proof (coupling_comp (coupling_value_index mu) Hidx) as Hleft.
  pose proof (coupling_comp Hleft
    (coupling_sym (coupling_value_index nu))) as Hboth.
  eapply coupling_mono; [|exact Hboth].
  intros x y [j [[i [[p Hi] [Hforward Hbackward]]] [q Hj]]].
  destruct (Hforward p x Hi) as [q' [y' [Hj' Hxy']]].
  rewrite Hj in Hj'. inversion Hj'. subst y'. exact Hxy'.
Qed.

Lemma enumQ_sem_lift_to_coupling {A B : eqType}
    (R : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B) :
  @sem_lift EnumQ EnumQ_SemanticMeasure A B R mu nu -> coupling R mu nu.
Proof.
  intro Hlift. apply indexed_coupling_to_coupling in Hlift.
  eapply coupling_proper_l; [apply enumQ_prune_eqenum|].
  eapply coupling_proper_r; [apply enumQ_prune_eqenum|exact Hlift].
Qed.

Lemma enumQ_sem_lift_of_coupling {A B : eqType}
    (R : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B) :
  coupling R mu nu -> @sem_lift EnumQ EnumQ_SemanticMeasure A B R mu nu.
Proof.
  intro Hlift. apply indexed_coupling_of_coupling.
  eapply coupling_proper_l with (mu := mu).
  - apply enumQ_eq_sym. apply enumQ_prune_eqenum.
  - eapply coupling_proper_r with (nu := nu).
    + apply enumQ_eq_sym. apply enumQ_prune_eqenum.
    + exact Hlift.
Qed.

Lemma enumQ_entry_mass_nonzero {A : eqType} (mu : EnumQ A) p x :
  List.In (p,x) mu -> p <> nnQ_0 -> acc_mass x mu != nnQ_0.
Proof.
  intros Hin Hnz. apply/(in_supp_iff_acc_mass_ne_0 x mu).
  rewrite /supp mem_undup. apply/mapP. exists (p,x); [|reflexivity].
  rewrite mem_filter. apply/andP. split.
  - apply/eqP. intro Hz. apply Hnz.
    transitivity (0 : nnQ); [exact Hz|]. apply val_inj. reflexivity.
  - induction mu as [|z tl IH]; [contradiction|].
    destruct Hin as [->|Hin]; rewrite in_cons.
    + by rewrite eq_refl.
    + apply/orP. right. apply IH. exact Hin.
Qed.

Lemma enumQ_coupling_realization_eqtype {A B : eqType}
    (R : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B) :
  @sem_lift EnumQ EnumQ_SemanticMeasure A B R mu nu ->
  exists joint, @semantic_coupling EnumQ EnumQ_SemanticMeasure A B R mu nu joint.
Proof.
  intro Hlift. destruct (enumQ_sem_lift_to_coupling Hlift) as [j Hl Hr Hsupport].
  exists j. split.
  - apply enumQ_sem_lift_of_coupling.
    eapply coupling_proper_r; [exact Hl|].
    rewrite <- (emap_id j) at 1.
    eapply coupling_emap; [|apply coupling_refl].
    intros x y ->. reflexivity.
  - split.
    + apply enumQ_sem_lift_of_coupling.
      eapply coupling_proper_r; [exact Hr|].
      rewrite <- (emap_id j) at 1.
      eapply coupling_emap; [|apply coupling_refl].
      intros x y ->. reflexivity.
    + intros p [x y] Hin Hnz. apply Hsupport.
      exact (enumQ_entry_mass_nonzero Hin Hnz).
Qed.

(** No decidable-equality hypothesis on return values (which may include
    functions or trees).  Classical equality is confined to this proof. *)
Theorem enumQ_coupling_realization {A B : Type}
    (R : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B) :
  @sem_lift EnumQ EnumQ_SemanticMeasure A B R mu nu ->
  exists joint, @semantic_coupling EnumQ EnumQ_SemanticMeasure A B R mu nu joint.
Proof.
  exact (@enumQ_coupling_realization_eqtype
    (@Equality.Pack (EnumQCouplingClassical.carrier A)
      (Equality.on (EnumQCouplingClassical.carrier A)))
    (@Equality.Pack (EnumQCouplingClassical.carrier B)
      (Equality.on (EnumQCouplingClassical.carrier B))) R mu nu).
Qed.

(** Native subprobability witnesses remain within the SubEnumQ carrier:
    the joint has the mass of its first marginal, hence at most one. *)
Theorem subenumQ_coupling_realization {A B : Type}
    (R : A -> B -> Prop) (mu : SubEnumQ A) (nu : SubEnumQ B) :
  @sem_lift SubEnumQ SubEnumQ_SemanticMeasure A B R mu nu ->
  exists joint, @semantic_coupling SubEnumQ SubEnumQ_SemanticMeasure A B R mu nu joint.
Proof.
  intro Hlift. destruct (enumQ_coupling_realization Hlift) as [j Hj].
  assert (Hmass : enumQ_mass j = enumQ_mass (subenumQ_raw mu)).
  { apply enumQ_sem_same_mass_expect_one.
    apply sem_lift_same_mass with (R := fun p x => fst p = x).
    exact (proj1 Hj). }
  assert (Hbound : enumQ_subprob j).
  { unfold enumQ_subprob. rewrite Hmass. exact (subenumQ_bound mu). }
  exists {| subenumQ_raw := j; subenumQ_bound := Hbound |}. exact Hj.
Qed.
