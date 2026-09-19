Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Classes.RelationClasses.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum FreeOmegaMeasure
  FreeOmegaCoupling.
From PTree.Eq Require Import FiniteInternal PFiniteResidual PEutt.
From PTree.Eq.FreeOmega Require Import FiniteInternalEquivalenceJointSubEnum.
From PTree.Examples Require Import SubEnumRegression HiddenRandomState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A new random bit is sampled and discarded after EVERY failed retry.
    No AST, positive success probability, or totality of the retry measure
    is assumed.  Success resumes an arbitrary, possibly eventful program.
    The proof supplies only a residual postfixed equivalence candidate;
    joint rows, their two costs, and the recurring process are extracted. *)
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

Lemma retry_equiv_equivalence : Equivalence retry_equiv.
Proof.
  split.
  - intro t. left. reflexivity.
  - intros t u [->|[Ht Hu]]; [left; reflexivity|right; split; assumption].
  - intros t u v [->|[Ht Hu]] [->|[Hu' Hv]];
      unfold retry_equiv; auto.
Qed.

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
      * exact hidden_fair_same_mass.
      * intro b. exact Heq.
Qed.

Lemma retry_roots_guard b c : pfinite_guard eq retry_equiv
  (retry_with_noise b) (retry_with_noise c).
Proof.
  unfold pfinite_guard, observe. cbn. constructor.
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
  ~ free_omega_lift (pfinite_guard eq retry_equiv)
    (FOSample subenum_fair (fun _ => FORet (retry_with_noise b)))
    (FORet (retry_with_noise c)).
Proof. intro H. inversion H. Qed.

Lemma retry_equiv_postfixed t u : retry_equiv t u ->
  @pfinite_residualF E SubEnum MF SubEnum_SemanticMeasure FI
    FreeOmegaMixedMeasure A A eq retry_equiv t u.
Proof.
  intros [->|[[b Hb] [c Hc]]].
  - eapply PFiniteResidualStep; [apply FIStop|apply FIStop|].
    apply sem_lift_ret.
    exact (@Equivalence_Reflexive _ _ (pfinite_guard_equivalence retry_equiv_equivalence) u).
  - destruct (retry_prefix_cut Hb) as [out1 [Hcut1 Heq1]].
    destruct (retry_prefix_cut Hc) as [out2 [Hcut2 Heq2]].
    eapply PFiniteResidualStep; [exact Hcut1|exact Hcut2|].
    change (free_omega_qlift (pfinite_guard eq retry_equiv) out1 out2).
    eapply FOQLComp with (T := eq) (U := pfinite_guard eq retry_equiv); [exact Heq1| |].
    + eapply FOQLComp with (T := pfinite_guard eq retry_equiv) (U := eq).
      * apply FOQLStructural, FOLRet. apply retry_roots_guard.
      * apply FOQLMono with (T := fun x y => y = x).
        -- apply FOQLSym. exact Heq2.
        -- intros x y Hyx. symmetry. exact Hyx.
      * intros x z [y [Hxy ->]]. exact Hxy.
    + intros x z [y [-> Hyz]]. exact Hyz.
Qed.

Theorem retry_discarded_bits_peutt :
  @peutt E SubEnum MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A A eq
    (retry_with_noise true) (retry_with_noise false).
Proof.
  apply peutt_coinduction_residual_equivalence_subenum with (sim := retry_equiv).
  - exact retry_equiv_equivalence.
  - exact retry_equiv_postfixed.
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
