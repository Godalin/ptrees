(** Observation-level coupling recovers high-universe support when the
    observations both preserve and reflect AE predicates.  Injectivity alone
    does not establish this premise (see FreeOmegaMeasureEnumAudit). *)
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
Set Implicit Arguments.
Unset Strict Implicit.

Lemma free_omega_support_lift_observation_ae {MN}
    `{NI : SemanticMeasure MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NA : @SemanticMeasureCouplingAELaws MN NI}
    {A B OA OB} (obsA : A -> OA) (obsB : B -> OB)
    (mu : FreeOmega MN A) (nu : FreeOmega MN B)
    (outA : MN OA) (outB : MN OB)
    (R : A -> B -> Prop) (S : OA -> OB -> Prop)
    (HA : forall P, free_omega_ae (fun x => P (obsA x)) mu <-> sem_ae outA P)
    (HB : forall Q, free_omega_ae (fun y => Q (obsB y)) nu <-> sem_ae outB Q)
    (Hlift : sem_lift S outA outB)
    (Hrel : forall x y, S (obsA x) (obsB y) -> R x y) :
  free_omega_support_lift R mu nu.
Proof.
  split.
  - intros P HP.
    assert (Himage : sem_ae outA (fun o => exists x, obsA x = o /\ P x)).
    { apply (proj1 (HA _)). eapply free_omega_ae_mono; [|exact HP].
      intros x Hx. exists x. split; [reflexivity|exact Hx]. }
    pose proof (sem_lift_ae_transport_r Hlift Himage) as Htransport.
    apply (proj2 (HB _)) in Htransport.
    eapply free_omega_ae_mono; [|exact Htransport].
    intros y [o [Hsy [x [<- Hx]]]]. exists x. split; [apply Hrel|]; assumption.
  - intros Q HQ.
    assert (Himage : sem_ae outB (fun o => exists y, obsB y = o /\ Q y)).
    { apply (proj1 (HB _)). eapply free_omega_ae_mono; [|exact HQ].
      intros y Hy. exists y. split; [reflexivity|exact Hy]. }
    pose proof (sem_lift_ae_transport_r (sem_lift_sym Hlift) Himage) as Htransport.
    apply (proj2 (HA _)) in Htransport.
    eapply free_omega_ae_mono; [|exact Htransport].
    intros x [o [Hsx [y [<- Hy]]]]. exists y. split; [apply Hrel|]; assumption.
Qed.
