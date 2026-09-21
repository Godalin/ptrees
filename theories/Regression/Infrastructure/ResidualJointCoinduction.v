(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Classes Require Import RelationClasses.
From Coq.Logic Require Import ClassicalChoice.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnum.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Coupling.
From PTree.Eq.Internal Require Import FiniteInternal.
From PTree.Eq Require Import PStrong PEutt.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternalAcceleration.
From PTree.Regression.Backend Require Import SubEnumRegression.
From PTree.Regression.Infrastructure Require Import HiddenRandomState CouplingReferences.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A new random bit is sampled and discarded after EVERY failed retry.
    No AST, positive success probability, or totality of the retry measure
    is assumed.  Success resumes an arbitrary, possibly eventful program.
    The proof supplies explicit unary computation strategies, whose
    complete stable-hitting limits are compared.  No additional program
    equivalence or native coupling-realization assumption is used. *)
Section Retry.
Context {E : Type -> Type} {A : Type}.
Variable coin : SubEnum bool.
Variable continuation : ptree E SubEnum A.
Local Notation tree := (ptree E SubEnum A).
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).

Definition discarded_bit (t : tree) := Prob subenum_fair (fun _ => Tau t).
CoFixpoint retry_with_noise (noisy : bool) : tree :=
  Prob coin (fun success : bool => if success then continuation else
    if noisy then discarded_bit (retry_with_noise noisy) else Tau (retry_with_noise noisy)).

Inductive retry_prefix (noisy : bool) : tree -> Prop :=
| RetryBase : retry_prefix noisy (retry_with_noise noisy)
| RetryTau t : retry_prefix noisy t -> retry_prefix noisy (Tau t)
| RetryNoise t : retry_prefix noisy t -> retry_prefix noisy (discarded_bit t).

Definition retry_region t := exists noisy, retry_prefix noisy t.
Definition retry_equiv (t u : tree) := t = u \/ (retry_region t /\ retry_region u).

Lemma retry_prefix_cut noisy t : retry_prefix noisy t ->
  exists out,
    @finite_internal E SubEnum MF FI FreeOmegaMixedMeasure A t out /\
    free_omega_qlift eq out (FORet (retry_with_noise noisy)).
Proof.
  intro Hprefix. induction Hprefix as [|t Ht [out [Hcut Heq]]|t Ht [out [Hcut Heq]]].
  - exists (FORet (retry_with_noise noisy)). split.
    + exact (@FIStop E SubEnum MF FI FreeOmegaMixedMeasure A _).
    + apply free_omega_qlift_refl. intro x. reflexivity.
  - exists out. split; [apply FITau; exact Hcut|exact Heq].
  - exists (FOSample subenum_fair (fun _ => out)). split.
    + apply (@FIProb E SubEnum MF FI FreeOmegaMixedMeasure A bool
        subenum_fair (fun _ => Tau t) (fun _ => out)).
      intro b. apply FITau. exact Hcut.
    + eapply free_omega_sample_to_constant with (point := false).
      * intro P. apply sem_ae_ret_iff.
      * exact fair_discard_same_mass.
      * intro b. exact Heq.
Qed.

Lemma retry_roots_guard b c : (fun t u => pstrongF eq retry_equiv (observe t) (observe u))
  (retry_with_noise b) (retry_with_noise c).
Proof.
  unfold observe. cbn. constructor.
  apply sem_lift_refl. intros success. destruct success.
  - left. reflexivity.
  - right. split.
    + exists b. destruct b; [apply RetryNoise|apply RetryTau]; apply RetryBase.
    + exists c. destruct c; [apply RetryNoise|apply RetryTau]; apply RetryBase.
Qed.

(** These selected cuts require quotient probability algebra.  The
    left cut retains the discarded bit, whereas the right is a Dirac.
    This refutes structural lifting of THESE cuts, not every alternative
    choice of compression witnesses. *)
Lemma retry_noise_cut_not_structural b c :
  ~ free_omega_lift (fun t u => pstrongF eq retry_equiv (observe t) (observe u))
    (FOSample subenum_fair (fun _ => FORet (retry_with_noise b)))
    (FORet (retry_with_noise c)).
Proof. intro H. inversion H. Qed.

(** A single strategy is selected per TREE, not per related pair.
    Each branchwise finite certificate is kept together with its hitting
    normalization.  There is no uniform bound on prefix lengths. *)
Lemma retry_policy_exists :
  exists cut : tree -> MF tree,
    (forall t, @finite_internal E SubEnum MF FI FreeOmegaMixedMeasure A t (cut t)) /\
    (forall t, retry_region t -> exists b,
      free_omega_qlift eq (cut t) (FORet (retry_with_noise b))).
Proof.
  assert (Hex : forall t : tree, exists out : MF tree,
    @finite_internal E SubEnum MF FI FreeOmegaMixedMeasure A t out /\
    (retry_region t -> exists b, free_omega_qlift eq out (FORet (retry_with_noise b)))).
  { intro t. destruct (classic (retry_region t)) as [[b Hb]|Hnot].
    - destruct (retry_prefix_cut Hb) as [out [Hcut Heq]].
      exists out. split; [exact Hcut|]. intros _. exists b. exact Heq.
    - exists (FORet t). split.
      + exact (@FIStop E SubEnum MF FI FreeOmegaMixedMeasure A t).
      + intro Hreg. contradiction. }
  destruct (choice _ Hex) as [cut Hcut].
  exists cut. split.
  - intro t. exact (proj1 (Hcut t)).
  - intros t Hreg. exact (proj2 (Hcut t) Hreg).
Qed.

Lemma retry_policy_coupled (cut : tree -> MF tree)
    (Hroot : forall t, retry_region t -> exists b,
      free_omega_qlift eq (cut t) (FORet (retry_with_noise b))) t u :
  retry_equiv t u ->
  free_omega_qlift
    (fun t u => pstrongF eq retry_equiv (observe t) (observe u)) (cut t) (cut u).
Proof.
  intros [->|[Ht Hu]].
  - apply free_omega_qlift_refl. intro v. destruct (observe v).
    + constructor. reflexivity.
    + constructor. left. reflexivity.
    + constructor. intro x. left. reflexivity.
    + constructor. apply sem_lift_refl. intro x. left. reflexivity.
  - destruct (Hroot t Ht) as [b Hb].
    destruct (Hroot u Hu) as [c Hc].
    eapply FOQLComp with (T := eq)
      (U := fun t u => pstrongF eq retry_equiv (observe t) (observe u)).
    + exact Hb.
    + eapply FOQLComp with
        (T := fun t u => pstrongF eq retry_equiv (observe t) (observe u)) (U := eq).
      * apply FOQLStructural, FOLRet. apply retry_roots_guard.
      * apply FOQLMono with (T := fun x y => y = x).
        -- apply FOQLSym. exact Hc.
        -- intros x y Hyx. symmetry. exact Hyx.
      * intros x z [y [Hxy ->]]. exact Hxy.
    + intros x z [y [-> Hyz]]. exact Hyz.
Qed.

Theorem retry_discarded_bits_peutt :
  @peutt E SubEnum MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A A eq
    (retry_with_noise true) (retry_with_noise false).
Proof.
  destruct retry_policy_exists as [cut [Hvalid Hroot]].
  eapply peutt_coinduction_finite_internal_policies
    with (sim := retry_equiv) (cut1 := cut) (cut2 := cut).
  - exact Hvalid.
  - exact Hvalid.
  - apply retry_policy_coupled. exact Hroot.
  - right. split; eexists; apply RetryBase.
Qed.
End Retry.

Variant retry_event : Type -> Type := RetryReply : retry_event bool.
Definition retry_visible_continuation : ptree retry_event SubEnum bool :=
  Vis RetryReply (fun answer => Ret answer).

Example eventful_retry_discarded_bits :
  @peutt retry_event SubEnum (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool bool eq
    (retry_with_noise subenum_fair retry_visible_continuation true)
    (retry_with_noise subenum_fair retry_visible_continuation false).
Proof. apply retry_discarded_bits_peutt. Qed.

(** Success is impossible in this instance.  The same endpoint is valid
    without an eventual-return premise. *)
Example always_failing_retry_discarded_bits :
  @peutt retry_event SubEnum (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool bool eq
    (retry_with_noise (subenum_ret false) retry_visible_continuation true)
    (retry_with_noise (subenum_ret false) retry_visible_continuation false).
Proof. apply retry_discarded_bits_peutt. Qed.
