Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum
  EnumDisintegration FreeOmegaMeasure FreeOmegaNative FreeOmegaCoupling
  FreeOmegaDisintegration FreeOmegaJointExtension.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A REALIZATION theorem, not a supplied-joint interface.  When a quotient
    coupling matches a common small label, condition the right measure on
    that label and resample it after the left sample.  All original weights
    and null fibers are retained.  The conclusion needs only quotient graph
    marginals, never reflection to native coupling. *)
Section CodedJoint.
Universe frontier.
Context {Anchor : Type@{frontier}} {X Y C : Type}.
Variable mu : SubEnum X.
Variable nu : SubEnum Y.
Variable left_code : X -> C.
Variable right_code : Y -> C.
Local Notation qlift := (@free_omega_qlift SubEnum SubEnum_SemanticMeasure
  SubEnum_SemanticOmega _ _).
Local Notation sample := (fun T (m : SubEnum T) =>
  (FOSample m (fun x => FORet x) : FreeOmegaAt SubEnum Anchor T)).

Let tagged := subenum_bind nu (fun y => subenum_ret (right_code y, y)).
Let marginal := subenum_bind nu (fun y => subenum_ret (right_code y)).

Lemma tagged_code_marginal : sem_lift (fun pair c => fst pair = c) tagged marginal.
Proof.
  unfold tagged, marginal.
  eapply (@sem_lift_bind SubEnum SubEnum_SemanticMeasure
    SubEnum_SemanticMeasureBindLaws Y Y _ _ eq).
  - apply sem_lift_refl. intro y. reflexivity.
  - intros x y ->. apply (@sem_lift_ret SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureCoreLaws). reflexivity.
Qed.

Theorem subenum_coded_quotient_joint :
  qlift (fun x y => left_code x = right_code y) (sample X mu) (sample Y nu) ->
  exists joint : SubEnum {x : X & (C * Y)%type},
    qlift (fun w x => projT1 w = x) (sample _ joint) (sample X mu) /\
    qlift (fun w y => snd (projT2 w) = y) (sample _ joint) (sample Y nu) /\
    sem_ae joint (fun w => left_code (projT1 w) = right_code (snd (projT2 w))).
Proof.
  intro Hcodes.
  destruct (subenum_disintegration_over tagged_code_marginal)
    as [conditional [Hreconstruct [Hfiber [Hsupport Htotal]]]].
  assert (Htag : sem_ae tagged (fun pair => fst pair = right_code (snd pair))).
  { unfold tagged. apply (@sem_ae_bind_iff SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureBindAEExactLaws).
    eapply sem_ae_mono; [|apply sem_ae_true]. intros y _.
    apply (@sem_ae_ret_iff SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureDiracAELaws). reflexivity. }
  assert (Hnu_total : sem_ae nu (fun y => subenum_total (conditional (right_code y)))).
  { unfold marginal in Htotal.
    apply (@sem_ae_bind_iff SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureBindAEExactLaws) in Htotal.
    eapply sem_ae_mono; [|exact Htotal]. intros y Hy.
    exact (proj1 (@sem_ae_ret_iff SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureDiracAELaws _ (right_code y) _) Hy). }
  assert (Hmu_total : sem_ae mu (fun x => subenum_total (conditional (left_code x)))).
  { assert (Hae : free_omega_ae (fun y => subenum_total (conditional (right_code y))) (sample Y nu)).
    { apply FOAESample with (Good := fun y => subenum_total (conditional (right_code y)));
        [exact Hnu_total|]. intros y Hy. apply FOAERet. exact Hy. }
    pose proof (proj2 (free_omega_qlift_support Hcodes) _ Hae) as Htransport.
    apply free_omega_ae_sample_inv in Htransport.
    eapply sem_ae_mono; [|exact Htransport]. intros x Hx.
    assert (Himage : exists y, left_code x = right_code y /\
      subenum_total (conditional (right_code y))) by (inversion Hx; assumption).
    destruct Himage as [y [Hxy Hy]]. rewrite Hxy. exact Hy. }
  pose (joint := subenum_bind mu (fun x => subenum_bind (conditional (left_code x))
    (fun pair => subenum_ret (existT (fun _ : X => (C * Y)%type) x pair)))).
  pose (nested :=
    FOSample mu (fun x => FOSample (conditional (left_code x))
      (fun pair => FORet (existT (fun _ : X => (C * Y)%type) x pair))) :
      FreeOmegaAt SubEnum Anchor {x : X & (C * Y)%type}).
  assert (Hnormal : qlift eq nested (sample _ joint)).
  { exact (@native_sigma_identity SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureCoreLaws SubEnum_SemanticOmega
      SubEnum_SemanticMeasureDiracAELaws SubEnum_SemanticMeasureBindAEExactLaws
      Anchor X (fun _ => (C * Y)%type) mu (fun x => conditional (left_code x))). }
  assert (Hleft : qlift (fun w x => projT1 w = x) nested (sample X mu)).
  { eapply FOQLSample with (T := fun x y => x = y /\ subenum_total (conditional (left_code x))).
    - apply sem_lift_refl_ae. exact Hmu_total.
    - intros x y [<- Hx]. eapply free_omega_sample_to_constant with (point := tt).
      + intro P. apply sem_ae_ret_iff.
      + apply subenum_total_same_mass. exact Hx.
      + intro pair. apply FOQLStructural, FOLRet. reflexivity. }
  pose (resampled := FOSample nu
    (fun y => FOSample (conditional (right_code y)) (fun pair => FORet (snd pair))) :
      FreeOmegaAt SubEnum Anchor Y).
  assert (Hresampled : qlift eq resampled (sample Y nu)).
  { eapply FOQLComp with (T := eq) (U := eq)
      (mid := FOSample marginal (fun c => FOSample (conditional c) (fun pair => FORet (snd pair)))).
    - apply FOQLMono with (T := fun x y => y = x).
      + apply FOQLSym. exact (@free_omega_sample_map SubEnum
          SubEnum_SemanticMeasure SubEnum_SemanticMeasureCoreLaws
          SubEnum_SemanticOmega SubEnum_SemanticMeasureDiracAELaws
          SubEnum_SemanticMeasureBindAEExactLaws _ _ _ nu right_code _).
      + intros x y Hyx. symmetry. exact Hyx.
    - eapply FOQLComp with (T := eq) (U := eq)
        (mid := FOSample tagged (fun pair => FORet (snd pair))).
      + apply free_omega_sample_disintegration. exact Hreconstruct.
      + exact (@free_omega_sample_map SubEnum
          SubEnum_SemanticMeasure SubEnum_SemanticMeasureCoreLaws
          SubEnum_SemanticOmega SubEnum_SemanticMeasureDiracAELaws
          SubEnum_SemanticMeasureBindAEExactLaws _ _ _ nu
          (fun y => (right_code y,y)) (fun pair => FORet (snd pair))).
      + intros x z [y [-> ->]]. reflexivity.
    - intros x z [y [-> ->]]. reflexivity. }
  assert (Hright : qlift (fun w y => snd (projT2 w) = y) nested resampled).
  { change (qlift (fun w y => snd (projT2 w) = y)
      (free_omega_bind (sample X mu) (fun x => FOSample (conditional (left_code x))
        (fun pair => FORet (existT (fun _ : X => (C * Y)%type) x pair))))
      (free_omega_bind (sample Y nu) (fun y =>
        FOSample (conditional (right_code y)) (fun pair => FORet (snd pair))))).
    eapply FOQLBind; [exact Hcodes|]. intros x y Hxy. rewrite Hxy.
    eapply FOQLSample with (T := eq); [apply sem_lift_refl; intro pair; reflexivity|].
    intros a b ->. apply FOQLStructural, FOLRet. reflexivity. }
  exists joint. split.
  - eapply FOQLComp with (T := eq) (U := fun w x => projT1 w = x) (mid := nested).
    + apply FOQLMono with (T := fun x y => y = x).
      * apply FOQLSym. exact Hnormal.
      * intros x y Hyx. symmetry. exact Hyx.
    + exact Hleft.
    + intros w z [x [-> Hx]]. exact Hx.
  - split.
    + eapply FOQLComp with (T := eq)
        (U := fun (w : {x : X & (C * Y)%type}) (y : Y) => snd (projT2 w) = y) (mid := nested).
      * apply FOQLMono with (T := fun x y => y = x).
        -- apply FOQLSym. exact Hnormal.
        -- intros x y Hyx. symmetry. exact Hyx.
      * eapply FOQLComp with
          (T := fun (w : {x : X & (C * Y)%type}) (y : Y) => snd (projT2 w) = y) (U := eq);
          [exact Hright|exact Hresampled|].
        intros w z [y [Hy ->]]. exact Hy.
      * intros w z [y [-> Hy]]. exact Hy.
    + unfold joint. apply (@sem_ae_bind_iff SubEnum SubEnum_SemanticMeasure
        SubEnum_SemanticMeasureBindAEExactLaws).
      eapply sem_ae_mono; [|apply sem_ae_true]. intros x _.
      apply (@sem_ae_bind_iff SubEnum SubEnum_SemanticMeasure
        SubEnum_SemanticMeasureBindAEExactLaws).
      eapply sem_ae_mono with (P := fun pair =>
        fst pair = left_code x /\ fst pair = right_code (snd pair)).
      * intros pair [Hleftcode Hrightcode].
        apply (@sem_ae_ret_iff SubEnum SubEnum_SemanticMeasure
          SubEnum_SemanticMeasureDiracAELaws). cbn. congruence.
      * apply sem_ae_conj; [apply Hfiber|apply Hsupport; exact Htag].
Qed.
End CodedJoint.
