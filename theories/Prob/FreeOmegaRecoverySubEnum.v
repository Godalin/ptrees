Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Logic.ClassicalDescription Logic.IndefiniteDescription.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum
  EnumDisintegration FreeOmegaMeasure FreeOmegaNative FreeOmegaRecovery
  FreeOmegaDisintegration FreeOmegaCoupling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Classical choice is used ONLY to label a fiber in the small carrier.
    It is NOT used to choose a replacement sample.  The latter is drawn
    from the conditional distribution, retaining all latent randomness. *)
Definition small_fiber_code {X A} (decode : X -> A) (a : A) : option X :=
  match excluded_middle_informative (exists x, decode x = a) with
  | left H => Some (proj1_sig (constructive_indefinite_description _ H))
  | right _ => None
  end.

Lemma small_fiber_code_spec {X A} (decode : X -> A) a :
  match small_fiber_code decode a with
  | Some x => decode x = a
  | None => forall x, decode x <> a
  end.
Proof.
  unfold small_fiber_code. destruct (excluded_middle_informative _) as [H|H].
  - destruct (constructive_indefinite_description _ H) as [x Hx]. exact Hx.
  - intros x Hx. apply H. exists x. exact Hx.
Qed.

Lemma small_fiber_code_sound {X A} (decode : X -> A) x a :
  small_fiber_code decode (decode x) = small_fiber_code decode a ->
  decode x = a.
Proof.
  intro Heq.
  pose proof (small_fiber_code_spec decode (decode x)) as Hx.
  pose proof (small_fiber_code_spec decode a) as Ha.
  rewrite <- Heq in Ha.
  destruct (small_fiber_code decode (decode x)) as [y|].
  - congruence.
  - exfalso. exact (Hx x eq_refl).
Qed.

Section Recovery.
Universe frontier.
Context {A : Type@{frontier}}
  (p : free_omega_native_presentation SubEnum A).
Let X := native_sample_type p.
Let mu := native_sample_measure p.
Let decode := native_sample_value p.
Let code := small_fiber_code decode.
Let label := fun x => code (decode x).
Let joint := subenum_bind mu (fun x => subenum_ret (label x, x)).
Let marginal := subenum_bind mu (fun x => subenum_ret (label x)).

Lemma coded_joint_marginal : sem_lift (fun pair c => fst pair = c) joint marginal.
Proof.
  unfold joint, marginal.
  eapply (@sem_lift_bind SubEnum SubEnum_SemanticMeasure
    SubEnum_SemanticMeasureBindLaws X X _ _ eq).
  - apply sem_lift_refl. intro x. reflexivity.
  - intros x y ->. apply (@sem_lift_ret SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureCoreLaws). reflexivity.
Qed.

Lemma coded_joint_support : sem_ae joint (fun pair => fst pair = label (snd pair)).
Proof.
  unfold joint. apply (@sem_ae_bind_iff SubEnum SubEnum_SemanticMeasure
    SubEnum_SemanticMeasureBindAEExactLaws).
  eapply sem_ae_mono; [|apply sem_ae_true].
  intros x _. apply (@sem_ae_ret_iff SubEnum SubEnum_SemanticMeasure
    SubEnum_SemanticMeasureDiracAELaws). reflexivity.
Qed.

(** No injectivity or totality premise on the source measure; in
    particular zero-mass fibers are permitted.  The decoded carrier A may
    contain higher-universe trees: only option X * X is sampled natively. *)
Definition subenum_native_recovery : free_omega_native_recovery p.
Proof.
  destruct (constructive_indefinite_description _
    (subenum_disintegration_over coded_joint_marginal))
    as [conditional [Hreconstruct [Hfiber [Hsupport Htotal]]]].
  refine (@Build_free_omega_native_recovery _ _ _ A p
    (fun a => subenum_total (conditional (code a)))
    (fun a => FOSample (conditional (code a)) (fun pair => FORet (snd pair)))
    _ _ _ _).
  - apply free_omega_native_ae_iff.
    unfold marginal in Htotal.
    apply (@sem_ae_bind_iff SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureBindAEExactLaws) in Htotal.
    eapply sem_ae_mono; [|exact Htotal].
    intros x Hx. exact (proj1 (@sem_ae_ret_iff SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureDiracAELaws _ (label x) _) Hx).
  - intros a _. apply FOAESample with
      (Good := fun pair => fst pair = code a /\ fst pair = label (snd pair)).
    + apply sem_ae_conj; [apply Hfiber|]. apply Hsupport, coded_joint_support.
    + intros [c x] [Hc Hx]. apply FOAERet.
      apply small_fiber_code_sound. change (label x = code a).
      cbn in Hc, Hx. rewrite <- Hx. exact Hc.
  - intros a Ha. eapply free_omega_sample_to_constant with (point := tt).
    + intro P. apply sem_ae_ret_iff.
    + apply subenum_total_same_mass. exact Ha.
    + intros pair. apply FOQLStructural, FOLRet. exact I.
  - change (free_omega_qlift eq
      (FOSample mu (fun x => FOSample (conditional (label x)) (fun pair => FORet (snd pair))))
      (FOSample mu (fun x => FORet x))).
    eapply FOQLComp with (T := eq) (U := eq)
      (mid := FOSample marginal (fun c => FOSample (conditional c) (fun pair => FORet (snd pair)))).
    + apply FOQLMono with (T := fun a b => b = a).
      * apply FOQLSym. exact (@free_omega_sample_map SubEnum
          SubEnum_SemanticMeasure SubEnum_SemanticMeasureCoreLaws
          SubEnum_SemanticOmega SubEnum_SemanticMeasureDiracAELaws
          SubEnum_SemanticMeasureBindAEExactLaws _ _ _ mu label _).
      * intros x y Hyx. symmetry. exact Hyx.
    + eapply FOQLComp with (T := eq) (U := eq)
        (mid := FOSample joint (fun pair => FORet (snd pair))).
      * apply free_omega_sample_disintegration. exact Hreconstruct.
      * exact (@free_omega_sample_map SubEnum
          SubEnum_SemanticMeasure SubEnum_SemanticMeasureCoreLaws
          SubEnum_SemanticOmega SubEnum_SemanticMeasureDiracAELaws
          SubEnum_SemanticMeasureBindAEExactLaws _ _ _ mu
          (fun x => (label x, x)) (fun pair => FORet (snd pair))).
      * intros x z [y [-> ->]]. reflexivity.
    + intros x z [y [-> ->]]. reflexivity.
Defined.
End Recovery.

(** Every finite native presentation admits conditional recovery, even
    with noninjective, higher-universe decoding and missing source mass.
    The conclusion remains a QUOTIENT coupling, not native reflection. *)
Theorem subenum_native_coupling_pullback {A B}
    (p : free_omega_native_presentation SubEnum A)
    (q : free_omega_native_presentation SubEnum B) (R : A -> B -> Prop) :
  free_omega_qlift R (free_omega_native p) (free_omega_native q) ->
  free_omega_qlift
    (fun x y => R (native_sample_value p x) (native_sample_value q y))
    (FOSample (native_sample_measure p) (fun x => FORet x) :
      FreeOmegaAt SubEnum A (native_sample_type p))
    (FOSample (native_sample_measure q) (fun y => FORet y) :
      FreeOmegaAt SubEnum B (native_sample_type q)).
Proof.
  intro H. exact (free_omega_native_coupling_pullback
    (subenum_native_recovery p) (subenum_native_recovery q) H).
Qed.
