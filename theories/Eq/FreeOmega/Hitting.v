Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Logic.ClassicalChoice.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting
  PTreeKernel PEutt StableHittingComputation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Exact witness-rewriting API for the observable FreeOmega backend.
    Unlike the generic interface, this backend defines semantic equality
    by equality coupling and its limit predicate is saturated under that
    equality.  No native joint-realization capability is needed. *)
Section FreeOmegaHitting.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation K R := (@ptree_primitive_kernel E MN MF FI FreeOmegaMixedMeasure R).
Local Notation hits t out :=
  (@stable_hitting MF FI FO _ _ (K _) (observe t) out).

Lemma stable_hitting_output_transport {R} (t : ptree E MN R) out out' :
  hits t out -> free_omega_qlift eq out out' -> hits t out'.
Proof.
  intros Hhit Heq. unfold stable_hitting in *.
  change (free_omega_qlift eq out'
    (FOLub (fun fuel => stable_hitting_approx (K R) fuel (observe t)))).
  eapply (@sem_eq_trans MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
  - apply (@sem_eq_sym MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
    exact Heq.
  - exact Hhit.
Qed.

Lemma stable_hitting_output_iff {R} (t : ptree E MN R) witness out :
  hits t witness ->
  (hits t out <-> free_omega_qlift eq out witness).
Proof.
  intro Hwit. split.
  - intro Hout. exact (stable_hitting_unique Hout Hwit).
  - intro Heq. eapply stable_hitting_output_transport; [exact Hwit|].
    apply (@sem_eq_sym MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
    exact Heq.
Qed.

Theorem stable_hitting_prob_iff {R X}
    (mu : MN X) (k : X -> ptree E MN R) out :
  hits (Prob mu k) out <->
  exists front : X -> MF (stable_head E MN R),
    (forall x, hits (k x) (front x)) /\
    free_omega_qlift eq out (FOSample mu front).
Proof.
  split.
  - intro Hhit. exact (stable_hitting_prob_decompose
      (FI := FI) (MX := FreeOmegaMixedMeasure) Hhit).
  - intros [front [Hfront Heq]].
    eapply stable_hitting_output_transport with (out := FOSample mu front).
    + eapply (stable_hitting_prob (FI := FI) (MX := FreeOmegaMixedMeasure)
        (FO := FO)) with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros x _. apply Hfront.
    + apply (@sem_eq_sym MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
      exact Heq.
Qed.

Theorem stable_hitting_prob_dirac_iff {R X}
    `{ND : @SemanticMeasureDiracAELaws MN NI}
    (x : X) (k : X -> ptree E MN R) out :
  hits (Prob (sem_ret x) k) out <-> hits (k x) out.
Proof.
  split; intro Hhit.
  - destruct (stable_hitting_exists (FI := FI) (FO := FO)
      (K R) (observe (k x))) as [w Hw].
    eapply stable_hitting_output_transport; [exact Hw|].
    apply (@sem_eq_sym MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
    eapply (stable_hitting_prob_dirac (FI := FI)
      (MX := FreeOmegaMixedMeasure) (FO := FO)); eassumption.
  - destruct (stable_hitting_exists (FI := FI) (FO := FO) (K R)
      (observe (Prob (sem_ret x) k))) as [w Hw].
    eapply stable_hitting_output_transport; [exact Hw|].
    eapply (stable_hitting_prob_dirac (FI := FI)
      (MX := FreeOmegaMixedMeasure) (FO := FO)); eassumption.
Qed.

Theorem stable_hitting_prob_flatten_iff {R X Y}
    `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}
    (mu : MN X) (h : X -> MN Y) (k : Y -> ptree E MN R) out :
  hits (Prob mu (fun x => Prob (h x) k)) out <->
  hits (Prob (sem_bind mu h) k) out.
Proof.
  split; intro Hhit.
  - destruct (stable_hitting_exists (FI := FI) (FO := FO) (K R)
      (observe (Prob (sem_bind mu h) k))) as [w Hw].
    eapply stable_hitting_output_transport; [exact Hw|].
    apply (@sem_eq_sym MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
    eapply (stable_hitting_prob_flatten (FI := FI)
      (MX := FreeOmegaMixedMeasure) (FO := FO)); eassumption.
  - destruct (stable_hitting_exists (FI := FI) (FO := FO) (K R)
      (observe (Prob mu (fun x => Prob (h x) k)))) as [w Hw].
    eapply stable_hitting_output_transport; [exact Hw|].
    eapply (stable_hitting_prob_flatten (FI := FI)
      (MX := FreeOmegaMixedMeasure) (FO := FO)); eassumption.
Qed.
End FreeOmegaHitting.
