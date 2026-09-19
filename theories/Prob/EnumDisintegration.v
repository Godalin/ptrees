Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrfun ssralg ssrnum order rat.
From PTree.Prob Require Import RatSubTypes DiscreteMC EnumMap EnumBindFacts
  Coupling FrontierLiftEnum MeasureIterationEnum TwoLevelMeasure
  TwoLevelMeasureEnum TwoLevelMeasureSubEnum SemanticCoupling SemanticCouplingEnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum EnumMap Coupling RatSubTypes GRing.Theory Order.Theory.
Import EnumCouplingClassical.
Local Open Scope ring_scope.
Local Open Scope order_scope.

(** Conditional resampling retains the WHOLE pair, including latent
    randomness, rather than selecting an arbitrary related partner.
    A null fiber has zero mass; a positive fiber is normalized. *)
Definition enum_fiber_row {A B : eqType}
    (marginal : Enum A) (joint : Enum (A * B)) (a : A) : Enum (A * B) :=
  [seq (nnq_div (fst ab) (acc_mass a marginal), snd ab)
    | ab <- joint & fst (snd ab) == a].

Definition enum_fiber_kernel {A B : eqType} (joint : Enum (A * B)) :=
  enum_fiber_row (emap fst joint) joint.

Lemma nnq_scale_div p q m :
  p * nnq_div q m = nnq_div (p * q) m.
Proof. apply val_inj. by rewrite /nnq_div /= mulrA. Qed.

Lemma enum_fiber_row_glue {A B : eqType}
    (marginal : Enum A) (joint : Enum (A * B)) a p :
  scale_Enum p (enum_fiber_row marginal joint a) =
  emap snd (glue_row marginal (emap (fun ab => (fst ab, ab)) joint) (p, (tt,a))).
Proof.
  elim: joint => [|[q [x y]] joint IH] //=.
  rewrite /enum_fiber_row /glue_row /emap /=.
  case Hxa: (x == a) => /=; rewrite -/enum_fiber_row -/glue_row -/emap in IH *.
  - by rewrite nnq_scale_div IH.
  - exact IH.
Qed.

Lemma enum_fiber_bind_glue {A B : eqType}
    (marginal outer : Enum A) (joint : Enum (A * B)) :
  bind_Enum outer (enum_fiber_row marginal joint) =
  emap snd (glue marginal (emap (fun a => (tt,a)) outer)
    (emap (fun ab => (fst ab,ab)) joint)).
Proof.
  elim: outer => [|[p a] outer IH] //=.
  rewrite /glue /= emap_app enum_fiber_row_glue IH. reflexivity.
Qed.

(** Reconstruct the original joint, not merely its support or one
    marginal.  Existing finite gluing supplies the probability calculation. *)
Theorem enum_fiber_kernel_reconstruct {A B : eqType} (joint : Enum (A * B)) :
  bind_Enum (emap fst joint) (enum_fiber_kernel joint) ==Enum joint.
Proof.
  rewrite /enum_fiber_kernel enum_fiber_bind_glue.
  have Hleft : emap snd (emap (fun a : A => (tt,a)) (emap fst joint)) ==Enum emap fst joint.
  { rewrite emap_comp emap_id. exact: enum_eq_refl. }
  have Hright : emap fst (emap (fun ab : A * B => (fst ab,ab)) joint) ==Enum emap fst joint.
  { rewrite emap_comp. exact: enum_eq_refl. }
  eapply enum_eq_trans; [exact (glue_right_marginal Hleft Hright)|].
  rewrite emap_comp. apply enum_eq_eq. exact (emap_id joint).
Qed.

Lemma enum_mass_sumq {A} (mu : Enum A) :
  enum_mass mu = Qval (sumq (unzip1 mu)).
Proof.
  elim: mu => [|[p x] mu IH]; first reflexivity.
  change (Qval p * 1 + enum_mass mu = Qval (p + sumq (unzip1 mu))).
  rewrite mulr1 IH. reflexivity.
Qed.

Lemma enum_fiber_row_mass {A B : eqType}
    (marginal : Enum A) (joint : Enum (A * B)) a :
  enum_mass (enum_fiber_row marginal joint a) =
  Qval (nnq_div (acc_mass a (emap fst joint)) (acc_mass a marginal)).
Proof.
  have Hscale : scale_Enum 1 (enum_fiber_row marginal joint a) = enum_fiber_row marginal joint a.
  { elim: (enum_fiber_row marginal joint a) => [|[p v] xs IH] //=.
    by rewrite mul1r IH. }
  rewrite -Hscale enum_fiber_row_glue.
  unfold enum_mass at 1. rewrite enum_expect_one_emap.
  change (enum_mass (glue_row marginal
    (emap (fun ab : A * B => (fst ab, ab)) joint) (1, (tt,a))) =
    Qval (nnq_div (acc_mass a (emap fst joint)) (acc_mass a marginal))).
  rewrite enum_mass_sumq glue_row_sum /= emap_comp mul1r.
  reflexivity.
Qed.

Theorem enum_fiber_kernel_mass {A B : eqType} (joint : Enum (A * B)) a :
  enum_mass (enum_fiber_kernel joint a) =
  if acc_mass a (emap fst joint) == 0 then 0 else 1.
Proof.
  rewrite /enum_fiber_kernel enum_fiber_row_mass.
  case Hmass: (acc_mass a (emap fst joint) == 0).
  - move/eqP: Hmass => ->. by rewrite nnq_div_zero_l.
  - have Hnz : acc_mass a (emap fst joint) != 0 by rewrite /negb Hmass.
    rewrite nnq_divE divff //.
Qed.

Lemma enum_fiber_kernel_subprob {A B : eqType} (joint : Enum (A * B)) a :
  enum_subprob (enum_fiber_kernel joint a).
Proof.
  rewrite /enum_subprob enum_fiber_kernel_mass.
  case: (acc_mass a (emap fst joint) == 0); exact: lexx || exact: Num.Theory.ler01.
Qed.

Definition subenum_fiber_kernel {A B : eqType} (joint : SubEnum (A * B)) a : SubEnum (A * B) :=
  @enum_as_subprob _ (enum_fiber_kernel (subenum_raw joint) a)
    (enum_fiber_kernel_subprob (subenum_raw joint) a).

Theorem subenum_fiber_kernel_reconstruct {A B : eqType} (joint : SubEnum (A * B)) :
  @sem_eq Enum Enum_SemanticMeasure (A * B)
    (bind_Enum (emap fst (subenum_raw joint))
      (fun a => subenum_raw (subenum_fiber_kernel joint a)))
    (subenum_raw joint).
Proof. apply enum_meas_eq_of_eqenum. apply enum_fiber_kernel_reconstruct. Qed.

Definition subenum_first_marginal {A B : Type} (joint : SubEnum (A * B)) : SubEnum A :=
  subenum_bind joint (fun ab => subenum_ret (fst ab)).

Theorem subenum_disintegration_reconstruct {A B : eqType} (joint : SubEnum (A * B)) :
  @sem_eq SubEnum SubEnum_SemanticMeasure (A * B)
    (subenum_bind (subenum_first_marginal joint) (subenum_fiber_kernel joint)) joint.
Proof.
  change (enum_meas_eq
    (bind_Enum (bind_Enum (subenum_raw joint) (fun ab => ret_Enum (fst ab)))
      (enum_fiber_kernel (subenum_raw joint))) (subenum_raw joint)).
  rewrite bind_ret_emap. apply enum_meas_eq_of_eqenum, enum_fiber_kernel_reconstruct.
Qed.

Lemma enum_fiber_row_fiber {A B : eqType}
    (marginal : Enum A) (joint : Enum (A * B)) a :
  enum_ae (enum_fiber_row marginal joint a) (fun ab => fst ab = a).
Proof.
  intros w ab Hin Hnz. unfold enum_fiber_row in Hin.
  apply List.in_map_iff in Hin. destruct Hin as [entry [Heq Hin]].
  apply List.filter_In in Hin. destruct Hin as [Hin Hfiber].
  injection Heq as Hw Hab. subst ab. exact (eqP Hfiber).
Qed.

Lemma enum_fiber_row_ae {A B : eqType}
    (marginal : Enum A) (joint : Enum (A * B)) a (P : A * B -> Prop) :
  enum_ae joint P -> enum_ae (enum_fiber_row marginal joint a) P.
Proof.
  intros HP w ab Hin Hnz. unfold enum_fiber_row in Hin.
  apply List.in_map_iff in Hin. destruct Hin as [[p xy] [Heq Hin]].
  apply List.filter_In in Hin. destruct Hin as [Hin Hfiber].
  injection Heq as Hw Hab. subst ab w.
  apply (HP p xy Hin). intro Hp. apply Hnz.
  rewrite Hp. apply val_inj. by rewrite /nnq_div /= mul0r.
Qed.

Theorem subenum_disintegration_fiber {A B : eqType}
    (joint : SubEnum (A * B)) a :
  @sem_ae SubEnum SubEnum_SemanticMeasure (A * B)
    (subenum_fiber_kernel joint a) (fun ab => fst ab = a).
Proof. apply enum_fiber_row_fiber. Qed.

Theorem subenum_disintegration_support {A B : eqType}
    (joint : SubEnum (A * B)) (P : A * B -> Prop) :
  @sem_ae SubEnum SubEnum_SemanticMeasure (A * B) joint P ->
  forall a, @sem_ae SubEnum SubEnum_SemanticMeasure (A * B)
    (subenum_fiber_kernel joint a) P.
Proof. intros H a. apply enum_fiber_row_ae. exact H. Qed.

Theorem subenum_disintegration_total_ae {A B : eqType} (joint : SubEnum (A * B)) :
  @sem_ae SubEnum SubEnum_SemanticMeasure A (subenum_first_marginal joint)
    (fun a => subenum_total (subenum_fiber_kernel joint a)).
Proof.
  change (enum_ae (bind_Enum (subenum_raw joint) (fun ab => ret_Enum (fst ab)))
    (fun a => enum_mass (enum_fiber_kernel (subenum_raw joint) a) = 1)).
  rewrite bind_ret_emap. intros p a Hin Hnz.
  rewrite enum_fiber_kernel_mass.
  have Hmass := enum_entry_mass_nonzero Hin Hnz.
  have Hz : (0 : nnQ) = nnQ_0 by apply val_inj.
  by rewrite Hz (negbTE Hmass).
Qed.

(** This endpoint does not require clients to equip values (in particular
    function-valued states) with decidable equality.  Classical equality is
    used only to construct the conditional kernel.  The statement preserves
    the full joint distribution, including its possibly missing mass. *)
Theorem subenum_disintegration {A B : Type} (joint : SubEnum (A * B)) :
  exists conditional : A -> SubEnum (A * B),
    sem_eq (subenum_bind (subenum_first_marginal joint) conditional) joint /\
    (forall a, sem_ae (conditional a) (fun ab => fst ab = a)) /\
    (forall P : A * B -> Prop, sem_ae joint P ->
      forall a, sem_ae (conditional a) P) /\
    sem_ae (subenum_first_marginal joint)
      (fun a => subenum_total (conditional a)).
Proof.
  pose EA := @Equality.Pack (EnumCouplingClassical.carrier A)
    (Equality.on (EnumCouplingClassical.carrier A)).
  pose EB := @Equality.Pack (EnumCouplingClassical.carrier B)
    (Equality.on (EnumCouplingClassical.carrier B)).
  exists (@subenum_fiber_kernel EA EB joint).
  split; [exact (@subenum_disintegration_reconstruct EA EB joint)|].
  split; [exact (@subenum_disintegration_fiber EA EB joint)|].
  split; [exact (@subenum_disintegration_support EA EB joint)|].
  exact (@subenum_disintegration_total_ae EA EB joint).
Qed.

Lemma subenum_bind_ret_r {A} (mu : SubEnum A) :
  sem_eq (subenum_bind mu subenum_ret) mu.
Proof.
  change (enum_meas_eq (bind_Enum (subenum_raw mu) ret_Enum) (subenum_raw mu)).
  rewrite (@bind_ret_emap _ _ (fun x => x) (subenum_raw mu)) emap_id.
  apply enum_repr_eq_implies_meas_eq. reflexivity.
Qed.

(** A graph coupling identifies the actual marginal, even when the caller's
    measure has a different list representation (split/reordered weights). *)
Lemma subenum_graph_marginal {A B} (f : A -> B)
    (joint : SubEnum A) (mu : SubEnum B) :
  sem_lift (fun x y => f x = y) joint mu ->
  sem_eq (subenum_bind joint (fun x => subenum_ret (f x))) mu.
Proof.
  intro Hgraph.
  change (sem_lift eq (subenum_bind joint (fun x => subenum_ret (f x))) mu).
  eapply sem_lift_proper_r; [apply subenum_bind_ret_r|].
  eapply (@sem_lift_bind SubEnum SubEnum_SemanticMeasure
    SubEnum_SemanticMeasureBindLaws A B B B (fun x y => f x = y) eq
    joint mu (fun x => subenum_ret (f x)) subenum_ret).
  - exact Hgraph.
  - intros x y Hxy. apply (@sem_lift_ret SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureCoreLaws). exact Hxy.
Qed.

(** Disintegrate over the SPECIFIED marginal rather than only the list
    obtained by mapping fst.  Equality lifting transports the law and AE
    normalization; support-only partner selection would not suffice. *)
Theorem subenum_disintegration_over {A B : Type}
    (joint : SubEnum (A * B)) (mu : SubEnum A) :
  sem_lift (fun p x => fst p = x) joint mu ->
  exists conditional : A -> SubEnum (A * B),
    sem_eq (subenum_bind mu conditional) joint /\
    (forall a, sem_ae (conditional a) (fun ab => fst ab = a)) /\
    (forall P : A * B -> Prop, sem_ae joint P ->
      forall a, sem_ae (conditional a) P) /\
    sem_ae mu (fun a => subenum_total (conditional a)).
Proof.
  intro Hgraph.
  pose proof (subenum_graph_marginal Hgraph) as Hmarginal.
  destruct (subenum_disintegration joint) as [k [Hreconstruct [Hfiber [Hsupport Htotal]]]].
  exists k. split.
  - eapply sem_eq_trans; [|exact Hreconstruct].
    change (sem_lift eq (subenum_bind mu k)
      (subenum_bind (subenum_first_marginal joint) k)).
    eapply (@sem_lift_bind SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureBindLaws A A (A * B) (A * B) eq eq).
    + change (sem_eq mu (subenum_first_marginal joint)).
      apply sem_eq_sym. exact Hmarginal.
    + intros x y ->. apply sem_lift_refl. intro p. reflexivity.
  - split; [exact Hfiber|]. split; [exact Hsupport|].
    eapply sem_ae_mono; [|exact (sem_lift_ae_transport_r Hmarginal Htotal)].
    intros y [x [-> Hx]]. exact Hx.
Qed.

(** Turn a native coupling into conditional RANDOM resampling on its left
    marginal.  The original joint and both marginals are retained. *)
Theorem subenum_coupling_disintegration {A B : Type}
    (R : A -> B -> Prop) (mu : SubEnum A) (nu : SubEnum B) :
  sem_lift R mu nu ->
  exists joint conditional,
    semantic_coupling R mu nu joint /\
    sem_eq (subenum_bind mu conditional) joint /\
    (forall a, sem_ae (conditional a) (fun p => fst p = a /\ R a (snd p))) /\
    sem_ae mu (fun a => subenum_total (conditional a)).
Proof.
  intro Hlift. destruct (subenum_coupling_realization Hlift) as [j Hj].
  destruct (subenum_disintegration_over (proj1 Hj))
    as [k [Hreconstruct [Hfiber [Hsupport Htotal]]]].
  exists j, k. split; [exact Hj|]. split; [exact Hreconstruct|].
  split; [|exact Htotal]. intro a.
  eapply sem_ae_mono with (P := fun p => fst p = a /\ R (fst p) (snd p)).
  - intros p [Hp HR]. split; [exact Hp|]. rewrite <- Hp. exact HR.
  - apply sem_ae_conj; [apply Hfiber|].
    apply Hsupport. exact (proj2 (proj2 Hj)).
Qed.
