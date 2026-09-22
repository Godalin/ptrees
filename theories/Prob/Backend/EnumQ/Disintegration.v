(** Conditional resampling of an actual rational joint. The complete pair
    is retained, positive fibers are normalized, and null fibers stay zero. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrfun ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteAtoms FiniteListAlgebra.
From PTree.Prob.Backend.EnumQ Require Import Representation Map Bind Coupling FrontierLift Iteration Measure SemanticCoupling.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Interface Require Import Measure Subprobability AE Coupling Omega Mixed SemanticCoupling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Import EnumQCouplingClassical.
Local Open Scope ring_scope.

Definition enumQ_fiber_row {A B : eqType} (marginal : EnumQ A)
    (joint : EnumQ (A*B)) (a : A) : EnumQ (A*B).
Proof.
  refine (enumQ_of_list (mu := [seq (ab.1 / acc_mass a marginal,ab.2)
    | ab <- enumQ_raw joint & ab.2.1 == a]) _).
  move=> w ab /List.in_map_iff [[p xy] [He Hin]].
  move/List.filter_In: Hin=> [Hin _]; inversion He; subst w ab.
  apply divr_ge0; [exact (enumQ_nonnegative joint p xy Hin)|exact: acc_mass_nonnegative].
Defined.
Definition enumQ_fiber_kernel {A B : eqType} (joint : EnumQ (A*B)) :=
  enumQ_fiber_row (emap fst joint) joint.

Lemma enumQ_fiber_row_glue {A B : eqType} (marginal : EnumQ A)
    (joint : EnumQ (A*B)) a p (Hp : 0 <= p) :
  enumQ_raw (scale_EnumQ Hp (enumQ_fiber_row marginal joint a)) =
  List.map (fun px => (px.1,px.2.2))
    (glue_row marginal (emap (fun ab => (ab.1,ab)) joint) (p,(tt,a))).
Proof.
  change (finite_weight_map p [seq (ab.1 / acc_mass a marginal,ab.2)
    | ab <- enumQ_raw joint & ab.2.1 == a] =
    List.map (fun px => (px.1,px.2.2))
      (glue_row marginal (emap (fun ab => (ab.1,ab)) joint) (p,(tt,a)))).
  rewrite /glue_row /enumQ_raw /emap /enumQ_map /finite_enum_map /=.
  elim: (finite_enum_raw joint)=> [|[q [x y]] tl IH] //=.
  case: (x == a)=> /=; by rewrite ?mulrA IH.
Qed.
Lemma enumQ_fiber_bind_glue {A B : eqType} (marginal outer : EnumQ A)
    (joint : EnumQ (A*B)) :
  enumQ_raw (bind_EnumQ outer (enumQ_fiber_row marginal joint)) =
  enumQ_raw (emap snd (glue marginal (emap (fun a => (tt,a)) outer)
    (emap (fun ab => (ab.1,ab)) joint))).
Proof.
  apply (enumQ_ind_raw (P := fun outer =>
    enumQ_raw (bind_EnumQ outer (enumQ_fiber_row marginal joint)) =
    enumQ_raw (emap snd (glue marginal (emap (fun a => (tt,a)) outer)
      (emap (fun ab => (ab.1,ab)) joint))))).
  - reflexivity.
  - move=> p Hp a mu IH.
    rewrite enumQ_cons_bind /enumQ_app /enumQ_raw /=.
    change (finite_enum_raw (scale_EnumQ Hp (enumQ_fiber_row marginal joint a)) ++
      finite_enum_raw (bind_EnumQ mu (enumQ_fiber_row marginal joint)) =
      List.map (fun px => (px.1,px.2.2))
        (glue_row marginal (emap (fun ab => (ab.1,ab)) joint) (p,(tt,a)) ++
        List.flat_map (glue_row marginal (emap (fun ab => (ab.1,ab)) joint))
          [seq (px.1,(tt,px.2)) | px <- enumQ_raw mu])).
    rewrite List.map_app -enumQ_fiber_row_glue; congr (_ ++ _); exact IH.
  - move=> mu nu H IH.
    unfold enumQ_raw in H; move: IH.
    by rewrite /enumQ_raw /bind_EnumQ /finite_enum_bind /emap /enumQ_map
      /finite_enum_map /glue /= H.
Qed.

Theorem enumQ_fiber_kernel_reconstruct {A B : eqType} (joint : EnumQ (A*B)) :
  bind_EnumQ (emap fst joint) (enumQ_fiber_kernel joint) ==EnumQ joint.
Proof.
  have Hleft : emap snd (emap (fun a : A => (tt,a)) (emap fst joint)) ==EnumQ emap fst joint.
  { apply enumQ_eq_eq; rewrite emap_comp; exact: emap_id. }
  have Hright : emap fst (emap (fun ab : A*B => (ab.1,ab)) joint) ==EnumQ emap fst joint.
  { apply enumQ_eq_eq; by rewrite emap_comp. }
  eapply enumQ_eq_trans; first (apply enumQ_eq_eq; exact: enumQ_fiber_bind_glue).
  eapply enumQ_eq_trans; first exact (glue_right_marginal Hleft Hright).
  apply enumQ_eq_eq; rewrite emap_comp; exact: emap_id.
Qed.
Lemma enumQ_mass_sumq {A} (mu : EnumQ A) :
  enumQ_mass mu = sumq (unzip1 (enumQ_raw mu)).
Proof.
  change (finite_expect (fun _ => 1) (enumQ_raw mu) = sumq (unzip1 (enumQ_raw mu))).
  by elim: (enumQ_raw mu)=> [|[p x] tl IH] //=; rewrite mulr1 IH.
Qed.
Lemma enumQ_fiber_row_mass {A B : eqType} (marginal : EnumQ A)
    (joint : EnumQ (A*B)) a :
  enumQ_mass (enumQ_fiber_row marginal joint a) = acc_mass a (emap fst joint) / acc_mass a marginal.
Proof.
  have Ha : acc_mass a (emap fst joint) =
    finite_expect (fun xy => if xy.1 == a then 1 else 0) (enumQ_raw joint).
  { exact: finite_expect_map. }
  rewrite Ha.
  change (finite_expect (fun _ => 1)
    [seq (ab.1 / acc_mass a marginal,ab.2) | ab <- enumQ_raw joint & ab.2.1 == a] =
    finite_expect (fun xy => if xy.1 == a then 1 else 0) (enumQ_raw joint) / acc_mass a marginal).
  elim: (enumQ_raw joint)=> [|[p [x y]] tl IH] /=; first by rewrite mul0r.
  case: (x == a)=> /=.
  - by rewrite !mulr1 IH mulrDl.
  - by rewrite mulr0 add0r.
Qed.
Theorem enumQ_fiber_kernel_mass {A B : eqType} (joint : EnumQ (A*B)) a :
  enumQ_mass (enumQ_fiber_kernel joint a) =
  if acc_mass a (emap fst joint) == 0 then 0 else 1.
Proof.
  rewrite /enumQ_fiber_kernel enumQ_fiber_row_mass.
  case H: (acc_mass a (emap fst joint) == 0).
  - by rewrite (eqP H) mul0r.
  - by rewrite divff // H.
Qed.

Lemma enumQ_fiber_kernel_subprob {A B : eqType} (joint : EnumQ (A * B)) a :
  enumQ_subprob (enumQ_fiber_kernel joint a).
Proof.
  rewrite /enumQ_subprob enumQ_fiber_kernel_mass.
  case: (acc_mass a (emap fst joint) == 0); exact: lexx || exact: Num.Theory.ler01.
Qed.

Definition subenumQ_fiber_kernel {A B : eqType} (joint : SubEnumQ (A * B)) a : SubEnumQ (A * B) :=
  @enumQ_as_subprob _ (enumQ_fiber_kernel (subenumQ_raw joint) a)
    (enumQ_fiber_kernel_subprob (subenumQ_raw joint) a).

Theorem subenumQ_fiber_kernel_reconstruct {A B : eqType} (joint : SubEnumQ (A * B)) :
  @sem_eq EnumQ EnumQ_SemanticMeasure (A * B)
    (bind_EnumQ (emap fst (subenumQ_raw joint))
      (fun a => subenumQ_raw (subenumQ_fiber_kernel joint a)))
    (subenumQ_raw joint).
Proof. apply enumQ_meas_eq_of_eqenum. apply enumQ_fiber_kernel_reconstruct. Qed.

Definition subenumQ_first_marginal {A B : Type} (joint : SubEnumQ (A * B)) : SubEnumQ A :=
  subenumQ_bind joint (fun ab => subenumQ_ret (fst ab)).

Theorem subenumQ_disintegration_reconstruct {A B : eqType} (joint : SubEnumQ (A * B)) :
  @sem_eq SubEnumQ SubEnumQ_SemanticMeasure (A * B)
    (subenumQ_bind (subenumQ_first_marginal joint) (subenumQ_fiber_kernel joint)) joint.
Proof.
  change (enumQ_meas_eq
    (bind_EnumQ (bind_EnumQ (subenumQ_raw joint) (fun ab => ret_EnumQ (fst ab)))
      (enumQ_fiber_kernel (subenumQ_raw joint))) (subenumQ_raw joint)).
  apply enumQ_meas_eq_of_eqenum.
  eapply enumQ_eq_trans; last exact: enumQ_fiber_kernel_reconstruct.
  apply bind_EnumQ_outer_proper; apply enumQ_eq_eq; exact: bind_ret_emap.
Qed.

Lemma enumQ_fiber_row_fiber {A B : eqType}
    (marginal : EnumQ A) (joint : EnumQ (A * B)) a :
  enumQ_ae (enumQ_fiber_row marginal joint a) (fun ab => fst ab = a).
Proof.
  intros w ab Hin Hnz. unfold enumQ_fiber_row in Hin.
  apply List.in_map_iff in Hin. destruct Hin as [entry [Heq Hin]].
  apply List.filter_In in Hin. destruct Hin as [Hin Hfiber].
  injection Heq as Hw Hab. subst ab. exact (eqP Hfiber).
Qed.

Lemma enumQ_fiber_row_ae {A B : eqType}
    (marginal : EnumQ A) (joint : EnumQ (A * B)) a (P : A * B -> Prop) :
  enumQ_ae joint P -> enumQ_ae (enumQ_fiber_row marginal joint a) P.
Proof.
  intros HP w ab Hin Hnz. unfold enumQ_fiber_row in Hin.
  apply List.in_map_iff in Hin. destruct Hin as [[p xy] [Heq Hin]].
  apply List.filter_In in Hin. destruct Hin as [Hin Hfiber].
  injection Heq as Hw Hab. subst ab w.
  apply (HP p xy Hin). intro Hp. apply Hnz.
  by rewrite Hp mul0r.
Qed.

Theorem subenumQ_disintegration_fiber {A B : eqType}
    (joint : SubEnumQ (A * B)) a :
  @sem_ae SubEnumQ SubEnumQ_SemanticMeasure (A * B)
    (subenumQ_fiber_kernel joint a) (fun ab => fst ab = a).
Proof. apply enumQ_fiber_row_fiber. Qed.

Theorem subenumQ_disintegration_support {A B : eqType}
    (joint : SubEnumQ (A * B)) (P : A * B -> Prop) :
  @sem_ae SubEnumQ SubEnumQ_SemanticMeasure (A * B) joint P ->
  forall a, @sem_ae SubEnumQ SubEnumQ_SemanticMeasure (A * B)
    (subenumQ_fiber_kernel joint a) P.
Proof. intros H a. apply enumQ_fiber_row_ae. exact H. Qed.

Theorem subenumQ_disintegration_total_ae {A B : eqType} (joint : SubEnumQ (A * B)) :
  @sem_ae SubEnumQ SubEnumQ_SemanticMeasure A (subenumQ_first_marginal joint)
    (fun a => subenumQ_total (subenumQ_fiber_kernel joint a)).
Proof.
  change (enumQ_ae (bind_EnumQ (subenumQ_raw joint) (fun ab => ret_EnumQ (fst ab)))
    (fun a => enumQ_mass (enumQ_fiber_kernel (subenumQ_raw joint) a) = 1)).
  unfold enumQ_ae; rewrite bind_ret_emap. intros p a Hin Hnz.
  rewrite enumQ_fiber_kernel_mass.
  have Hmass := enumQ_entry_mass_nonzero Hin Hnz.
  by rewrite (negbTE Hmass).
Qed.

(** This endpoint does not require clients to equip values (in particular
    function-valued states) with decidable equality.  Classical equality is
    used only to construct the conditional kernel.  The statement preserves
    the full joint distribution, including its possibly missing mass. *)
Theorem subenumQ_disintegration {A B : Type} (joint : SubEnumQ (A * B)) :
  exists conditional : A -> SubEnumQ (A * B),
    sem_eq (subenumQ_bind (subenumQ_first_marginal joint) conditional) joint /\
    (forall a, sem_ae (conditional a) (fun ab => fst ab = a)) /\
    (forall P : A * B -> Prop, sem_ae joint P ->
      forall a, sem_ae (conditional a) P) /\
    sem_ae (subenumQ_first_marginal joint)
      (fun a => subenumQ_total (conditional a)).
Proof.
  pose EA := @Equality.Pack (EnumQCouplingClassical.carrier A)
    (Equality.on (EnumQCouplingClassical.carrier A)).
  pose EB := @Equality.Pack (EnumQCouplingClassical.carrier B)
    (Equality.on (EnumQCouplingClassical.carrier B)).
  exists (@subenumQ_fiber_kernel EA EB joint).
  split; [exact (@subenumQ_disintegration_reconstruct EA EB joint)|].
  split; [exact (@subenumQ_disintegration_fiber EA EB joint)|].
  split; [exact (@subenumQ_disintegration_support EA EB joint)|].
  exact (@subenumQ_disintegration_total_ae EA EB joint).
Qed.

Lemma subenumQ_bind_ret_r {A} (mu : SubEnumQ A) :
  sem_eq (subenumQ_bind mu subenumQ_ret) mu.
Proof.
  change (enumQ_meas_eq (bind_EnumQ (subenumQ_raw mu) ret_EnumQ) (subenumQ_raw mu)).
  apply enumQ_repr_eq_implies_meas_eq.
  by rewrite /enumQ_repr_eq (@bind_ret_emap _ _ (fun x => x) (subenumQ_raw mu)) emap_id.
Qed.

(** Numeric totality supplies an actual mass-preserving coupling to a
    Dirac measure.  AE support alone would not justify this step. *)
Lemma subenumQ_total_same_mass {A} (mu : SubEnumQ A) :
  subenumQ_total mu -> sem_same_mass mu (subenumQ_ret tt).
Proof.
  intro Htotal.
  assert (Hunit : sem_eq (subenumQ_bind mu (fun _ => subenumQ_ret tt))
    (subenumQ_ret tt)).
  { change (enumQ_meas_eq
      (bind_EnumQ (subenumQ_raw mu) (fun _ => ret_EnumQ tt)) (ret_EnumQ tt)).
    apply enumQ_meas_eq_of_eqenum; intros [].
    change (enumQ_expect (fun _ : unit => 1)
      (bind_EnumQ (subenumQ_raw mu) (fun _ => ret_EnumQ tt)) =
      enumQ_expect (fun _ : unit => 1) (ret_EnumQ tt)).
    rewrite enumQ_expect_bind enumQ_expect_ret.
    transitivity (enumQ_mass (subenumQ_raw mu)); last exact Htotal.
    apply finite_expect_ext=> x; reflexivity. }
  eapply sem_lift_proper_l; [apply subenumQ_bind_ret_r|].
  eapply sem_lift_proper_r; [exact Hunit|].
  eapply (@sem_lift_bind SubEnumQ SubEnumQ_SemanticMeasure
    SubEnumQ_SemanticMeasureBindLaws A A A unit eq (fun _ _ => True)
    mu mu subenumQ_ret (fun _ => subenumQ_ret tt)).
  - apply sem_lift_refl. intro x. reflexivity.
  - intros x y _. apply (@sem_lift_ret SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticMeasureCoreLaws). exact I.
Qed.

(** A graph coupling identifies the actual marginal, even when the caller's
    measure has a different list representation (split/reordered weights). *)
Lemma subenumQ_graph_marginal {A B} (f : A -> B)
    (joint : SubEnumQ A) (mu : SubEnumQ B) :
  sem_lift (fun x y => f x = y) joint mu ->
  sem_eq (subenumQ_bind joint (fun x => subenumQ_ret (f x))) mu.
Proof.
  intro Hgraph.
  change (sem_lift eq (subenumQ_bind joint (fun x => subenumQ_ret (f x))) mu).
  eapply sem_lift_proper_r; [apply subenumQ_bind_ret_r|].
  eapply (@sem_lift_bind SubEnumQ SubEnumQ_SemanticMeasure
    SubEnumQ_SemanticMeasureBindLaws A B B B (fun x y => f x = y) eq
    joint mu (fun x => subenumQ_ret (f x)) subenumQ_ret).
  - exact Hgraph.
  - intros x y Hxy. apply (@sem_lift_ret SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticMeasureCoreLaws). exact Hxy.
Qed.

(** Disintegrate over the SPECIFIED marginal rather than only the list
    obtained by mapping fst.  Equality lifting transports the law and AE
    normalization; support-only partner selection would not suffice. *)
Theorem subenumQ_disintegration_over {A B : Type}
    (joint : SubEnumQ (A * B)) (mu : SubEnumQ A) :
  sem_lift (fun p x => fst p = x) joint mu ->
  exists conditional : A -> SubEnumQ (A * B),
    sem_eq (subenumQ_bind mu conditional) joint /\
    (forall a, sem_ae (conditional a) (fun ab => fst ab = a)) /\
    (forall P : A * B -> Prop, sem_ae joint P ->
      forall a, sem_ae (conditional a) P) /\
    sem_ae mu (fun a => subenumQ_total (conditional a)).
Proof.
  intro Hgraph.
  pose proof (subenumQ_graph_marginal Hgraph) as Hmarginal.
  destruct (subenumQ_disintegration joint) as [k [Hreconstruct [Hfiber [Hsupport Htotal]]]].
  exists k. split.
  - eapply sem_eq_trans; [|exact Hreconstruct].
    change (sem_lift eq (subenumQ_bind mu k)
      (subenumQ_bind (subenumQ_first_marginal joint) k)).
    eapply (@sem_lift_bind SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticMeasureBindLaws A A (A * B) (A * B) eq eq).
    + change (sem_eq mu (subenumQ_first_marginal joint)).
      apply sem_eq_sym. exact Hmarginal.
    + intros x y ->. apply sem_lift_refl. intro p. reflexivity.
  - split; [exact Hfiber|]. split; [exact Hsupport|].
    eapply sem_ae_mono; [|exact (sem_lift_ae_transport_r Hmarginal Htotal)].
    intros y [x [-> Hx]]. exact Hx.
Qed.

(** Turn a native coupling into conditional RANDOM resampling on its left
    marginal.  The original joint and both marginals are retained. *)
Theorem subenumQ_coupling_disintegration {A B : Type}
    (R : A -> B -> Prop) (mu : SubEnumQ A) (nu : SubEnumQ B) :
  sem_lift R mu nu ->
  exists joint conditional,
    semantic_coupling R mu nu joint /\
    sem_eq (subenumQ_bind mu conditional) joint /\
    (forall a, sem_ae (conditional a) (fun p => fst p = a /\ R a (snd p))) /\
    sem_ae mu (fun a => subenumQ_total (conditional a)).
Proof.
  intro Hlift. destruct (subenumQ_coupling_realization Hlift) as [j Hj].
  destruct (subenumQ_disintegration_over (proj1 Hj))
    as [k [Hreconstruct [Hfiber [Hsupport Htotal]]]].
  exists j, k. split; [exact Hj|]. split; [exact Hreconstruct|].
  split; [|exact Htotal]. intro a.
  eapply sem_ae_mono with (P := fun p => fst p = a /\ R (fst p) (snd p)).
  - intros p [Hp HR]. split; [exact Hp|]. rewrite <- Hp. exact HR.
  - apply sem_ae_conj; [apply Hfiber|].
    apply Hsupport. exact (proj2 (proj2 Hj)).
Qed.
