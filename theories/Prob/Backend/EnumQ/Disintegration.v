(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrfun ssralg ssrnum order rat.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Bind PTree.Prob.Backend.EnumQ.Coupling PTree.Prob.Backend.EnumQ.FrontierLift PTree.Prob.Backend.EnumQ.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure.
From PTree.Prob.Interface Require Import SemanticCoupling.
Require Import PTree.Prob.Backend.EnumQ.SemanticCoupling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling RatSubTypes GRing.Theory Order.Theory.
Import EnumQCouplingClassical.
Local Open Scope ring_scope.
Local Open Scope order_scope.

(** Conditional resampling retains the WHOLE pair, including latent
    randomness, rather than selecting an arbitrary related partner.
    A null fiber has zero mass; a positive fiber is normalized. *)
Definition enumQ_fiber_row {A B : eqType}
    (marginal : EnumQ A) (joint : EnumQ (A * B)) (a : A) : EnumQ (A * B) :=
  [seq (nnq_div (fst ab) (acc_mass a marginal), snd ab)
    | ab <- joint & fst (snd ab) == a].

Definition enumQ_fiber_kernel {A B : eqType} (joint : EnumQ (A * B)) :=
  enumQ_fiber_row (emap fst joint) joint.

Lemma nnq_scale_div p q m :
  p * nnq_div q m = nnq_div (p * q) m.
Proof. apply val_inj. by rewrite /nnq_div /= mulrA. Qed.

Lemma enumQ_fiber_row_glue {A B : eqType}
    (marginal : EnumQ A) (joint : EnumQ (A * B)) a p :
  scale_EnumQ p (enumQ_fiber_row marginal joint a) =
  emap snd (glue_row marginal (emap (fun ab => (fst ab, ab)) joint) (p, (tt,a))).
Proof.
  elim: joint => [|[q [x y]] joint IH] //=.
  rewrite /enumQ_fiber_row /glue_row /emap /=.
  case Hxa: (x == a) => /=; rewrite -/enumQ_fiber_row -/glue_row -/emap in IH *.
  - by rewrite nnq_scale_div IH.
  - exact IH.
Qed.

Lemma enumQ_fiber_bind_glue {A B : eqType}
    (marginal outer : EnumQ A) (joint : EnumQ (A * B)) :
  bind_EnumQ outer (enumQ_fiber_row marginal joint) =
  emap snd (glue marginal (emap (fun a => (tt,a)) outer)
    (emap (fun ab => (fst ab,ab)) joint)).
Proof.
  elim: outer => [|[p a] outer IH]; first reflexivity.
  rewrite enumQ_cons_bind.
  rewrite /glue /= emap_app enumQ_fiber_row_glue IH. reflexivity.
Qed.

(** Reconstruct the original joint, not merely its support or one
    marginal.  Existing finite gluing supplies the probability calculation. *)
Theorem enumQ_fiber_kernel_reconstruct {A B : eqType} (joint : EnumQ (A * B)) :
  bind_EnumQ (emap fst joint) (enumQ_fiber_kernel joint) ==EnumQ joint.
Proof.
  rewrite /enumQ_fiber_kernel enumQ_fiber_bind_glue.
  have Hleft : emap snd (emap (fun a : A => (tt,a)) (emap fst joint)) ==EnumQ emap fst joint.
  { rewrite emap_comp emap_id. exact: enumQ_eq_refl. }
  have Hright : emap fst (emap (fun ab : A * B => (fst ab,ab)) joint) ==EnumQ emap fst joint.
  { rewrite emap_comp. exact: enumQ_eq_refl. }
  eapply enumQ_eq_trans; [exact (glue_right_marginal Hleft Hright)|].
  rewrite emap_comp. apply enumQ_eq_eq. exact (emap_id joint).
Qed.

Lemma enumQ_mass_sumq {A} (mu : EnumQ A) :
  enumQ_mass mu = Qval (sumq (unzip1 mu)).
Proof.
  elim: mu => [|[p x] mu IH]; first reflexivity.
  change (Qval p * 1 + enumQ_mass mu = Qval (p + sumq (unzip1 mu))).
  rewrite mulr1 IH. reflexivity.
Qed.

Lemma enumQ_fiber_row_mass {A B : eqType}
    (marginal : EnumQ A) (joint : EnumQ (A * B)) a :
  enumQ_mass (enumQ_fiber_row marginal joint a) =
  Qval (nnq_div (acc_mass a (emap fst joint)) (acc_mass a marginal)).
Proof.
  have Hscale : scale_EnumQ 1 (enumQ_fiber_row marginal joint a) = enumQ_fiber_row marginal joint a.
  { elim: (enumQ_fiber_row marginal joint a) => [|[p v] xs IH] //=.
    by rewrite mul1r IH. }
  rewrite -Hscale enumQ_fiber_row_glue.
  unfold enumQ_mass at 1. rewrite enumQ_expect_one_emap.
  change (enumQ_mass (glue_row marginal
    (emap (fun ab : A * B => (fst ab, ab)) joint) (1, (tt,a))) =
    Qval (nnq_div (acc_mass a (emap fst joint)) (acc_mass a marginal))).
  rewrite enumQ_mass_sumq glue_row_sum /= emap_comp mul1r.
  reflexivity.
Qed.

Theorem enumQ_fiber_kernel_mass {A B : eqType} (joint : EnumQ (A * B)) a :
  enumQ_mass (enumQ_fiber_kernel joint a) =
  if acc_mass a (emap fst joint) == 0 then 0 else 1.
Proof.
  rewrite /enumQ_fiber_kernel enumQ_fiber_row_mass.
  case Hmass: (acc_mass a (emap fst joint) == 0).
  - move/eqP: Hmass => ->. by rewrite nnq_div_zero_l.
  - have Hnz : acc_mass a (emap fst joint) != 0 by rewrite /negb Hmass.
    rewrite nnq_divE divff //.
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
  rewrite bind_ret_emap. apply enumQ_meas_eq_of_eqenum, enumQ_fiber_kernel_reconstruct.
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
  rewrite Hp. apply val_inj. by rewrite /nnq_div /= mul0r.
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
  rewrite bind_ret_emap. intros p a Hin Hnz.
  rewrite enumQ_fiber_kernel_mass.
  have Hmass := enumQ_entry_mass_nonzero Hin Hnz.
  have Hz : (0 : nnQ) = nnQ_0 by apply val_inj.
  by rewrite Hz (negbTE Hmass).
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
  rewrite (@bind_ret_emap _ _ (fun x => x) (subenumQ_raw mu)) emap_id.
  apply enumQ_repr_eq_implies_meas_eq. reflexivity.
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
    rewrite bind_ret_emap. apply enumQ_meas_eq_of_eqenum. intros [].
    apply val_inj.
    have Hmass : forall xs : EnumQ A,
      Qval (acc_mass tt (emap (fun _ => tt) xs)) = enumQ_mass xs.
    { elim=> [|[p x] xs IH] //=.
      rewrite /acc_mass /emap /= -/acc_mass in IH *.
      by rewrite IH /enumQ_mass /= mulr1. }
    change (Qval (acc_mass tt (emap (fun _ => tt) (subenumQ_raw mu))) =
      Qval (acc_mass tt (ret_EnumQ tt))).
    rewrite Hmass. exact Htotal. }
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
