(** Checked relational kernel bind on the fully discrete joint carrier.
    Selection uses classical choice; measurability is proved from the discrete
    sigma-algebra. No coupling-existence capability is introduced. *)
Set Warnings "-notation-overridden,-ambiguous-paths,-redundant-canonical-projection".
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp classical_sets
  functions reals topology normedtype sequences measure probability kernel
  ereal numfun lebesgue_measure lebesgue_integral.
From PTree.Prob.Interface Require Import Measure Mixed Coupling.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws OrderLaws OmegaLaws.
From Coq.Classes Require Morphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section JointBind.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Context {A B C D : Type}.

Definition mathcomp_joint_source (j : subprobability (mc_joint A B) R)
    (_ : mc_carrier unit) : measure (mc_joint A B) R := j.
Lemma mathcomp_joint_source_measurable j U : measurable U ->
  measurable_fun setT (fun x => mathcomp_joint_source j x U).
Proof. by move=> mU mtop V mV. Qed.
HB.instance Definition _ j := @isKernel.Build _ _ _ _ R
  (mathcomp_joint_source j) (mathcomp_joint_source_measurable j).
Lemma mathcomp_joint_source_bound j :
  ereal_sup [set mathcomp_joint_source j x setT | x in setT] <= 1.
Proof. apply/(sprob_kernelP (mathcomp_joint_source j)) => x; exact: sprobability_setT. Qed.
HB.instance Definition _ j := Kernel_isSubProbability.Build _ _ _ _ R
  (mathcomp_joint_source j) (mathcomp_joint_source_bound j).

Definition mathcomp_joint_kernel
    (k : mc_joint A B -> subprobability (mc_joint C D) R)
    (x : mc_joint A B) : measure (mc_joint C D) R := k x.
Lemma mathcomp_joint_kernel_measurable k U : measurable U ->
  measurable_fun setT (fun x => mathcomp_joint_kernel k x U).
Proof. by move=> mU mtop V mV. Qed.
HB.instance Definition _ k := @isKernel.Build _ _ _ _ R
  (mathcomp_joint_kernel k) (mathcomp_joint_kernel_measurable k).
Lemma mathcomp_joint_kernel_bound k :
  ereal_sup [set mathcomp_joint_kernel k x setT | x in setT] <= 1.
Proof. apply/(sprob_kernelP (mathcomp_joint_kernel k)) => x; exact: sprobability_setT. Qed.
HB.instance Definition _ k := Kernel_isSubProbability.Build _ _ _ _ R
  (mathcomp_joint_kernel k) (mathcomp_joint_kernel_bound k).

Definition mathcomp_joint_bind_measure j k :=
  mkcomp_noparam
    [the R.-spker (mc_carrier unit) ~> (mc_joint A B) of mathcomp_joint_source j]
    [the R.-spker (mc_joint A B) ~> (mc_joint C D) of mathcomp_joint_kernel k]
    MCBottom.
Definition mathcomp_joint_bind_fun j k U := mathcomp_joint_bind_measure j k U.
Lemma mathcomp_joint_bind0 j k : mathcomp_joint_bind_fun j k set0 = 0.
Proof. exact: measure0. Qed.
Lemma mathcomp_joint_bind_ge0 j k U : 0 <= mathcomp_joint_bind_fun j k U.
Proof. exact: measure_ge0. Qed.
Lemma mathcomp_joint_bind_sigma j k : semi_sigma_additive (mathcomp_joint_bind_fun j k).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ j k := @isMeasure.Build _ (mc_joint C D) R
  (mathcomp_joint_bind_fun j k) (mathcomp_joint_bind0 j k)
  (mathcomp_joint_bind_ge0 j k) (@mathcomp_joint_bind_sigma j k).
Lemma mathcomp_joint_bind_bound j k : mathcomp_joint_bind_fun j k setT <= 1.
Proof. exact: sprob_mkcomp_noparam. Qed.
HB.instance Definition _ j k := @Measure_isSubProbability.Build _ _ R
  (mathcomp_joint_bind_fun j k) (mathcomp_joint_bind_bound j k).
Definition mathcomp_joint_bind j k : subprobability (mc_joint C D) R :=
  [the subprobability (mc_joint C D) R of mathcomp_joint_bind_fun j k].
Lemma mathcomp_joint_bindE j k U :
  mathcomp_joint_bind j k U = \int[j]_x k x U.
Proof. reflexivity. Qed.
End JointBind.

Section Projection.
Variable R : realType.
Context {A B C : Type}.
Variable j : subprobability (mc_joint A B) R.
Variable p : mc_joint A B -> mc_carrier C.
Lemma mathcomp_joint_projection_measurable : measurable_fun setT p.
Proof. by move=> mtop U mU. Qed.
HB.instance Definition _ := isMeasurableFun.Build _ _ _ _ p mathcomp_joint_projection_measurable.
Definition mathcomp_projected := pushforward j p.
Lemma mathcomp_projected0 : mathcomp_projected set0 = 0.
Proof. by rewrite /mathcomp_projected /pushforward preimage_set0 measure0. Qed.
Lemma mathcomp_projected_ge0 U : 0 <= mathcomp_projected U.
Proof. exact: measure_ge0. Qed.
Lemma mathcomp_projected_sigma : semi_sigma_additive mathcomp_projected.
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ := @isMeasure.Build _ (mc_carrier C) R
  mathcomp_projected mathcomp_projected0 mathcomp_projected_ge0 mathcomp_projected_sigma.
Lemma mathcomp_projected_bound : mathcomp_projected setT <= 1.
Proof. rewrite /mathcomp_projected /pushforward preimage_setT; exact: sprobability_setT. Qed.
HB.instance Definition _ := @Measure_isSubProbability.Build _ _ R
  mathcomp_projected mathcomp_projected_bound.
Definition mathcomp_projected_native := mathcomp_source_kernel
  [the subprobability (mc_carrier C) R of mathcomp_projected].
Lemma mathcomp_joint_integral_projection (mu : MathCompKernelMeasure R C)
    (f : mc_carrier C -> \bar R) :
  (forall U, measurable U -> ~ U MCBottom -> j (p @^-1` U) = mathcomp_kernel_root mu U) ->
  (forall x, 0 <= f x) -> f MCBottom = 0 ->
  \int[j]_x f (p x) = \int[mathcomp_kernel_root mu]_x f x.
Proof.
  move=> Hm Hp Hz.
  have Hfun : measurable_fun setT f by move=> mtop U mU.
  rewrite -[setT in LHS](@preimage_setT _ _ p).
  rewrite -(ge0_integral_pushforward mathcomp_joint_projection_measurable) //.
  change (\int[mathcomp_kernel_root mathcomp_projected_native]_x f x =
    \int[mathcomp_kernel_root mu]_x f x).
  apply/eqP; rewrite eq_le; apply/andP; split;
    apply: mathcomp_native_integral_le => // U mU Hb;
    change (pushforward j p U <= mathcomp_kernel_root mu U) ||
      change (mathcomp_kernel_root mu U <= pushforward j p U);
    by rewrite /pushforward (Hm U mU Hb).
Qed.
End Projection.

Section RelationalBind.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).

Lemma mathcomp_native_bind_zero_left {A B} (k : A -> M B) :
  mathcomp_kernel_eq (mathcomp_kernel_bind (mathcomp_kernel_zero R) k)
    (mathcomp_kernel_zero R).
Proof.
  move=> U mU Hb; rewrite mathcomp_kernel_root_bind (mathcomp_native_zero_returned R Hb).
  change (\int[dirac (@MCBottom A)]_x mathcomp_kernel_extend_measure k x U = 0).
  rewrite integral_dirac // diracT mul1e.
  exact: mathcomp_native_zero_returned.
Qed.

Lemma mathcomp_native_eq_le {A} (mu nu : M A) :
  mathcomp_kernel_eq mu nu -> mathcomp_node_le mu nu.
Proof. move=> He U mU Hb; rewrite (He U mU Hb); exact: lexx. Qed.

Lemma mathcomp_native_le_eq_r {A} (mu nu xi : M A) :
  mathcomp_kernel_eq nu xi -> mathcomp_node_le mu xi -> mathcomp_node_le mu nu.
Proof. intros He Hl U mU Hb; rewrite (He U mU Hb); exact: Hl. Qed.

Lemma mathcomp_native_le_eq_l {A} (mu nu xi : M A) :
  mathcomp_kernel_eq mu xi -> mathcomp_node_le xi nu -> mathcomp_node_le mu nu.
Proof. intros He Hl U mU Hb; rewrite (He U mU Hb); exact: Hl. Qed.

#[global] Instance mathcomp_native_eq_Equivalence {A : Type} :
  RelationClasses.Equivalence (@mathcomp_kernel_eq R A).
Proof.
  split; [exact (@mathcomp_kernel_eq_refl R A)|
    exact (@mathcomp_kernel_eq_sym R A)|exact (@mathcomp_kernel_eq_trans R A)].
Qed.

#[global] Instance mathcomp_native_le_Proper {A : Type} :
  Morphisms.Proper (Morphisms.respectful (@mathcomp_kernel_eq R A)
    (Morphisms.respectful (@mathcomp_kernel_eq R A) iff))
    (@mathcomp_node_le R A).
Proof.
  intros m m' Hm n n' Hn; split; intros H U mU Hb.
  - rewrite -(Hm U mU Hb) -(Hn U mU Hb); exact: H.
  - rewrite (Hm U mU Hb) (Hn U mU Hb); exact: H.
Qed.

#[global] Instance mathcomp_native_bind_Proper {A B : Type} :
  Morphisms.Proper (Morphisms.respectful (@mathcomp_kernel_eq R A)
    (Morphisms.respectful (Morphisms.pointwise_relation A (@mathcomp_kernel_eq R B))
      (@mathcomp_kernel_eq R B))) (@mathcomp_kernel_bind R A B).
Proof.
  intros m m' Hm k k' Hk; apply: mathcomp_native_le_antisym;
    apply: (mathcomp_native_le_trans _ _).
  - apply: mathcomp_native_bind_le_mu; exact: mathcomp_native_eq_le Hm.
  - apply: mathcomp_native_bind_le_k => x; exact: mathcomp_native_eq_le (Hk x).
  - apply: mathcomp_native_bind_le_mu; apply: mathcomp_native_eq_le.
    exact: mathcomp_kernel_eq_sym Hm.
  - apply: mathcomp_native_bind_le_k => x; apply: mathcomp_native_eq_le.
    exact: mathcomp_kernel_eq_sym (Hk x).
Qed.

Lemma mathcomp_native_lift_bind {A B C D}
    (S : A -> B -> Prop) (T : C -> D -> Prop)
    (mu : M A) (nu : M B) (k : A -> M C) (h : B -> M D) :
  mathcomp_kernel_lift S mu nu ->
  (forall x y, S x y -> mathcomp_kernel_lift T (k x) (h y)) ->
  mathcomp_kernel_lift T (mathcomp_kernel_bind mu k) (mathcomp_kernel_bind nu h).
Proof.
  move=> [j [Hleft [Hright Hrel]]] Hkh.
  pose good (xy : mc_joint A B) (v : subprobability (mc_joint C D) R) :=
    (forall U, measurable U -> ~ U MCBottom ->
      v (mc_joint_fst @^-1` U) = mathcomp_kernel_extend_measure k (mc_joint_fst xy) U) /\
    (forall V, measurable V -> ~ V MCBottom ->
      v (mc_joint_snd @^-1` V) = mathcomp_kernel_extend_measure h (mc_joint_snd xy) V) /\
    almost_everywhere v (mc_relation T).
  pose bot := [the subprobability (mc_joint C D) R of
    dirac (MCJoint MCBottom MCBottom)].
  have Hex xy : exists v, mc_relation S xy -> good xy v.
  { case: xy => [[|a] [|b]].
    - exists bot => _; split.
      + move=> U mU Hb; reflexivity.
      + split; first by move=> V mV Hb.
        apply/negligibleP; first by [].
        change (dirac (MCJoint MCBottom MCBottom) (~` mc_relation T) = (0 : \bar R)).
        rewrite /dirac indicE.
        have -> : (MCJoint MCBottom MCBottom \in ~` mc_relation T) = false.
        { by apply/asboolPn => H; apply: H. }
        reflexivity.
    - by exists bot.
    - by exists bot.
    - case: (pselect (S a b)) => H.
      + have [v Hv] := Hkh a b H; exists v => _; exact Hv.
      + by exists bot. }
  pose next xy := proj1_sig (cid (Hex xy)).
  have Hnext xy : mc_relation S xy -> good xy (next xy) := proj2_sig (cid (Hex xy)).
  exists (mathcomp_joint_bind j next); split.
  - move=> U mU Hb; rewrite mathcomp_joint_bindE mathcomp_kernel_root_bind.
    transitivity (\int[j]_xy mathcomp_kernel_extend_measure k (mc_joint_fst xy) U).
    + apply: ae_eq_integral => //.
      rewrite /ae_eq /almost_everywhere; eapply negligibleS; last exact Hrel.
      move=> xy Hbad Hxy; apply: Hbad => _; exact: (Hnext xy Hxy).1.
    + apply: mathcomp_joint_integral_projection Hleft _ _.
      * move=> x; exact: measure_ge0.
      * exact: mathcomp_native_zero_returned.
  - split.
    + move=> V mV Hb; rewrite mathcomp_joint_bindE mathcomp_kernel_root_bind.
      transitivity (\int[j]_xy mathcomp_kernel_extend_measure h (mc_joint_snd xy) V).
      * apply: ae_eq_integral => //.
        rewrite /ae_eq /almost_everywhere; eapply negligibleS; last exact Hrel.
        move=> xy Hbad Hxy; apply: Hbad => _; exact: (Hnext xy Hxy).2.1.
      * apply: mathcomp_joint_integral_projection Hright _ _.
        -- move=> x; exact: measure_ge0.
        -- exact: mathcomp_native_zero_returned.
    + apply/negligibleP; first by [].
      change (mathcomp_joint_bind j next (~` mc_relation T) = 0).
      rewrite mathcomp_joint_bindE.
      transitivity (\int[j]_xy (0 : \bar R)); last exact: integral0.
      apply: ae_eq_integral => //.
      rewrite /ae_eq /almost_everywhere; eapply negligibleS; last exact Hrel.
      move=> xy Hbad Hxy; apply: Hbad => _.
      exact: measure_negligible _ (Hnext xy Hxy).2.2.
Qed.

#[global] Instance MathCompNativeBindLaws :
  @SemanticMeasureBindLaws M (MathCompNodeSemanticMeasure R).
Proof.
  constructor.
  - exact (@mathcomp_kernel_bind_ret_l R).
  - exact (@mathcomp_kernel_bind_assoc R).
  - move=> A B mu k h H.
    exact: (@mathcomp_native_bind_ae_eq R A B mu _ k h H (fun x Hx => Hx)).
  - exact @mathcomp_native_lift_bind.
Qed.

#[global] Instance MathCompNativeMixedLaws :
  @MixedMeasureLaws M M (MathCompNodeSemanticMeasure R)
    (MathCompNodeSemanticMeasure R) (MathCompNativeMixedMeasure R).
Proof.
  constructor.
  - exact (@sem_bind_ae_proper M (MathCompNodeSemanticMeasure R) MathCompNativeBindLaws).
  - exact (@mathcomp_kernel_bind_assoc R).
  - exact @mathcomp_native_lift_bind.
Qed.
End RelationalBind.

(** Safe native specialization of generic map reflection. Gluing is used
    through CoreLaws composition; no countability or decoder injectivity is
    required, and no recursive frontier is instantiated here. *)
Theorem mathcomp_kernel_map_reflect (R : realType)
    `{G : MathCompCouplingGluing R} {X Y A B : Type}
    (mu : MathCompKernelMeasure R X) (nu : MathCompKernelMeasure R Y)
    (f : X -> A) (g : Y -> B) (T : A -> B -> Prop) :
  mathcomp_kernel_lift T
    (mathcomp_kernel_bind mu (fun x => mathcomp_kernel_ret R (f x)))
    (mathcomp_kernel_bind nu (fun y => mathcomp_kernel_ret R (g y))) ->
  mathcomp_kernel_lift (fun x y => T (f x) (g y)) mu nu.
Proof.
  exact (@sem_lift_map_reflect _ (MathCompNodeSemanticMeasure R)
    (@MathCompNodeSemanticMeasureCoreLaws R G) (@MathCompNativeBindLaws R)
    (@mathcomp_kernel_bind_ret_r R) X Y A B mu nu f g T).
Qed.
