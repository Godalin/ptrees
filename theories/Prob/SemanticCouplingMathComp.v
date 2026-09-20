Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp classical_sets reals.
From mathcomp.analysis Require Import measure probability kernel ereal.
From PTree.Prob Require Import TwoLevelMeasure MathCompMeasure TwoLevelMeasureMathComp
  SemanticCoupling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Preserve the subprobability package when pushing a measure forward.
    In particular, this does not normalize a possibly deficient measure. *)
Section SubprobabilityPushforward.
Context {d e} {T : measurableType d} {U : measurableType e} {R : realType}.
Variable mu : subprobability T R.
Variable f : T -> U.
Hypothesis mf : measurable_fun setT f.

Definition coupling_pushforward_fun := pushforward mu f.

Lemma coupling_pushforward0 : coupling_pushforward_fun set0 = 0.
Proof. by rewrite /coupling_pushforward_fun /pushforward preimage_set0 measure0. Qed.

Lemma coupling_pushforward_ge0 V : 0 <= coupling_pushforward_fun V.
Proof. exact: measure_ge0. Qed.

Lemma coupling_pushforward_sigma_additive :
  semi_sigma_additive coupling_pushforward_fun.
Proof.
  move=> F mF tF mUF; rewrite /coupling_pushforward_fun /pushforward preimage_bigcup.
  apply: measure_semi_sigma_additive.
  - move=> n. rewrite -[X in measurable X]setTI. exact: mf.
  - apply/trivIsetP=> i j _ _ ij; rewrite -preimage_setI.
    have Hij : F i `&` F j = set0.
    { move/trivIsetP: tF=> H. exact: H i j Logic.I Logic.I ij. }
    by rewrite Hij preimage_set0.
  - rewrite -preimage_bigcup -[X in measurable X]setTI. exact: mf.
Qed.

HB.instance Definition coupling_pushforward_is_measure :=
  @measure.isMeasure.Build _ U R coupling_pushforward_fun
    coupling_pushforward0 coupling_pushforward_ge0 coupling_pushforward_sigma_additive.

Lemma coupling_pushforward_le1 : coupling_pushforward_fun setT <= 1.
Proof. change (mu setT <= 1). exact: sprobability_setT. Qed.

HB.instance Definition coupling_pushforward_is_subprobability :=
  @Measure_isSubProbability.Build _ U R coupling_pushforward_fun coupling_pushforward_le1.

Definition coupling_pushforward : subprobability U R :=
  [the subprobability U R of coupling_pushforward_fun].
End SubprobabilityPushforward.

(** The backend's coupling carrier contains two bookkeeping bottom points;
    a semantic joint instead has carrier [A * B].  Pack returned pairs and
    send bookkeeping points to bottom.  One-sided bottoms have zero mass
    in any valid coupling, so no returned mass is lost by this conversion. *)
Definition mc_joint_pack {A B} (z : mc_joint A B) : mc_carrier (A * B) :=
  match z with
  | MCJoint (MCValue a) (MCValue b) => MCValue (a, b)
  | _ => MCBottom
  end.

Section MathCompRealization.
Variable R : realType.

(** This theorem needs neither coupling gluing nor quotient reflection.
    It only repackages the witness already present in native [sem_lift]. *)
Theorem mathcomp_coupling_realization {A B} (rel : A -> B -> Prop)
    (mu : MathCompKernelMeasure R A) (nu : MathCompKernelMeasure R B) :
  @sem_lift (MathCompKernelMeasure R) (MathCompNodeSemanticMeasure R)
    A B rel mu nu ->
  exists joint, @semantic_coupling (MathCompKernelMeasure R)
    (MathCompNodeSemanticMeasure R) A B rel mu nu joint.
Proof.
  move=> [j [Hl [Hr Hrel]]].
  have mpack : measurable_fun setT (@mc_joint_pack A B) by [].
  pose packed := coupling_pushforward j mpack.
  exists (mathcomp_source_kernel packed).
  have mleft : measurable_fun setT
      (fun z : mc_joint A B => MCJoint (mc_joint_pack z) (mc_joint_fst z)) by [].
  have mright : measurable_fun setT
      (fun z : mc_joint A B => MCJoint (mc_joint_pack z) (mc_joint_snd z)) by [].
  split.
  - exists (coupling_pushforward j mleft). split.
    + move=> V _ _. reflexivity.
    + split.
      * move=> V mV nV. exact: Hl mV nV.
      * rewrite /almost_everywhere. apply/negligibleP; first by [].
        change (j ((fun z : mc_joint A B =>
          MCJoint (mc_joint_pack z) (mc_joint_fst z)) @^-1`
          (~` mc_relation (fun p x => fst p = x))) = 0).
        apply/negligibleP; first by [].
        eapply negligibleS; [|exact Hrel].
        move=> [[|a] [|b]] /=; unfold mc_relation, mc_joint_pack; simpl; tauto.
  - split.
    + exists (coupling_pushforward j mright). split.
      * move=> V _ _. reflexivity.
      * split.
        -- move=> V mV nV. exact: Hr mV nV.
        -- rewrite /almost_everywhere. apply/negligibleP; first by [].
           change (j ((fun z : mc_joint A B =>
             MCJoint (mc_joint_pack z) (mc_joint_snd z)) @^-1`
             (~` mc_relation (fun p y => snd p = y))) = 0).
           apply/negligibleP; first by [].
           eapply negligibleS; [|exact Hrel].
           move=> [[|a] [|b]] /=; unfold mc_relation, mc_joint_pack; simpl; tauto.
    + rewrite /sem_ae /MathCompNodeSemanticMeasure /mathcomp_kernel_ae
        /mathcomp_measure_ae /almost_everywhere.
      apply/negligibleP; first by [].
      change (j (@mc_joint_pack A B @^-1`
        (~` mc_predicate (fun p => rel (fst p) (snd p)))) = 0).
      apply/negligibleP; first by [].
      eapply negligibleS; [|exact Hrel].
      move=> [[|a] [|b]] /=; unfold mc_predicate, mc_relation, mc_joint_pack;
        simpl; tauto.
Qed.
End MathCompRealization.
