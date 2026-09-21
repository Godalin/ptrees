(** Role: Canonical equational/hitting theory. Depends on Core and Prob; does not provide comparison or interpreter semantics. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq.Logic Require Import ClassicalChoice.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt StableHittingComputation.
From PTree.Eq.FreeOmega Require Import Base.

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

(** A client may count complete execution rounds instead of primitive
    steps.  An increasing schedule dominating the identity has the same
    complete hitting limit. *)
Theorem stable_hitting_subsequence {R} (t : ptree E MN R)
    (schedule : nat -> nat)
    (Hmono : forall n, Peano.le (schedule n) (schedule (S n)))
    (Hge : forall n, Peano.le n (schedule n)) :
  hits t (FOLub (fun n =>
    ptree_hitting_approx (FI := FI) (FO := FO) (schedule n) (observe t))).
Proof.
  unfold stable_hitting.
  apply FOQLSym. eapply FOQLMono.
  - apply FOQLCofinal.
    + intro n. apply ptree_observable_hitting_increasing.
    + intro n. apply ptree_hitting_mono. apply Hmono.
    + split.
      * intro n. exists n. apply ptree_hitting_mono. apply Hge.
      * intro n. exists (schedule n).
        apply free_omega_approx_refl. intros h. reflexivity.
  - intros h h' ->. reflexivity.
Qed.

(** AST from a compositional observation calculation: finite execution
    observations converge to a total native measure.  No scalar denotation
    of every FreeOmega expression, nor PMF-to-bisimulation converse, is
    assumed.  Both finite observation and limit obligations stay explicit. *)
Theorem stable_hitting_ast_of_observations {R O} (t : ptree E MN R)
    (schedule : nat -> nat)
    (Hmono : forall n, Peano.le (schedule n) (schedule (S n)))
    (Hge : forall n, Peano.le n (schedule n))
    (obs : stable_head E MN R -> O) (outs : nat -> MN O) out :
  (forall n, free_omega_observes obs
    (ptree_hitting_approx (FI := FI) (FO := FO) (schedule n) (observe t))
    (outs n)) ->
  sem_lub outs out -> sem_total out ->
  ptree_stable_hitting_ast (FI := FI) (FO := FO) (observe t)
    (FOLub (fun n =>
      ptree_hitting_approx (FI := FI) (FO := FO) (schedule n) (observe t))).
Proof.
  intros Hobs Hlim Htotal. split.
  - exact (stable_hitting_subsequence t Hmono Hge).
  - apply free_omega_observable_total_intro.
    exists O, obs, out. split; last exact Htotal.
    eapply FOOObserveLub; [exact Hobs|exact Hlim|].
    intro n. apply ptree_hitting_mono. apply Hmono.
Qed.

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
