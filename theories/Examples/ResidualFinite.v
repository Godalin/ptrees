Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Automatic Proposition Inductives.

From Coq Require Import Program.Equality RelationClasses Logic.ClassicalDescription.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import
  TwoLevelMeasure TwoLevelMeasureEnum TwoLevelMeasureSubEnum
  FreeOmegaMeasure DiscreteMC.
From PTree.Eq Require Import
  FiniteInternal FiniteInternalHitting PFiniteResidual PStrong PEutt.
From PTree.Eq.FreeOmega Require Import FiniteInternalAcceleration.
From PTree.Examples Require Import RandomWalk.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum.

Variant residualE : Type -> Type := .
Local Notation RF :=
  (@pfinite_residual_rel residualE Enum (FreeOmega Enum)
    Enum_SemanticMeasure Enum_SemanticMeasureCoreLaws
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    bool bool eq).

CoFixpoint residual_spin : ptree residualE Enum bool := Tau residual_spin.

Lemma residual_finite_tau_divergence : RF (Tau residual_spin) residual_spin.
Proof. exact (pfinite_residual_tau_prefix 1 residual_spin). Qed.

Lemma residual_finite_prob_tau (mu : Enum bool)
    (k : bool -> ptree residualE Enum bool) :
  RF (Prob mu (fun b => Tau (k b))) (Prob mu k).
Proof. exact (pfinite_residual_prob_tau_prefix mu (fun _ => 1) k). Qed.

(** The law is generic in the node carrier, so the nat-indexed branch
    depths need not be bounded.  This is not a finite-support Enum claim. *)
Section UnboundedBranchDepth.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}.
Context {R : Type}.

Lemma residual_finite_nonuniform (mu : MN nat) (k : nat -> ptree E MN R) :
  @pfinite_residual_rel E MN MF NI NC FI FC MX R R eq
    (Prob mu (fun n => tau_prefix n (k n))) (Prob mu k).
Proof. apply pfinite_residual_prob_tau_prefix. Qed.

End UnboundedBranchDepth.

(** FIStop cannot bypass the strong guard.  In particular a silent loop
    cannot be related to a return by an unguarded coinductive self-reference. *)
Lemma residual_finite_spin_not_ret : ~ RF residual_spin (Ret true).
Proof.
  intro Hrel. pose proof (pfinite_residual_unfold Hrel) as Hstep.
  inversion Hstep as [t1 t2 out1 out2 Hexec1 Hexec2 Hlift]; subst.
  pose proof (finite_internal_self_loop_inv Hexec1 eq_refl) as Hout1.
  pose proof (finite_internal_ret_inv Hexec2) as Hout2.
  subst out1 out2.
  pose proof (free_omega_qlift_support Hlift) as [Hsupport _].
  assert (Hae : @free_omega_ae Enum Enum_SemanticMeasure _
    (fun t => t = residual_spin) (FORet residual_spin)).
  { constructor. reflexivity. }
  specialize (Hsupport _ Hae). dependent destruction Hsupport.
  destruct H as [t [Hguard ->]].
  unfold pfinite_guard in Hguard. cbn in Hguard. inversion Hguard.
Qed.

(** Purely internal, potentially unbounded retry: there is no Vis guard
    between retries.  Each failed toss has one administrative Tau on the
    left and two on the right. *)
CoFixpoint residual_retry_left : ptree residualE SubEnum bool :=
  Prob rw_coin (fun b : bool => if b then Ret true else Tau residual_retry_left).

CoFixpoint residual_retry_right : ptree residualE SubEnum bool :=
  Prob rw_coin (fun b : bool => if b then Ret true else Tau (Tau residual_retry_right)).

(** Select only the explicit administrative prefixes.  Propositional
    equality avoids assuming an eta law or dependent elimination for the
    coinductive tree.  These are proof witnesses, not executable samplers. *)
Definition residual_retry_cut1 (t : ptree residualE SubEnum bool) :
    FreeOmega SubEnum (ptree residualE SubEnum bool) :=
  if excluded_middle_informative (t = Tau residual_retry_left)
  then FORet residual_retry_left else FORet t.

Definition residual_retry_cut2 (t : ptree residualE SubEnum bool) :
    FreeOmega SubEnum (ptree residualE SubEnum bool) :=
  if excluded_middle_informative (t = Tau (Tau residual_retry_right))
  then FORet residual_retry_right else FORet t.

Local Notation SFI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).

Lemma residual_retry_cut1_valid t :
  @finite_internal residualE SubEnum (FreeOmega SubEnum) SFI FreeOmegaMixedMeasure
    bool t (residual_retry_cut1 t).
Proof.
  unfold residual_retry_cut1. destruct (excluded_middle_informative _) as [->|Hne].
  - apply FITau. exact (@FIStop residualE SubEnum (FreeOmega SubEnum) SFI
      FreeOmegaMixedMeasure bool _).
  - exact (@FIStop residualE SubEnum (FreeOmega SubEnum) SFI
      FreeOmegaMixedMeasure bool _).
Qed.

Lemma residual_retry_cut2_valid t :
  @finite_internal residualE SubEnum (FreeOmega SubEnum) SFI FreeOmegaMixedMeasure
    bool t (residual_retry_cut2 t).
Proof.
  unfold residual_retry_cut2. destruct (excluded_middle_informative _) as [->|Hne].
  - apply FITau. apply FITau.
    exact (@FIStop residualE SubEnum (FreeOmega SubEnum) SFI
      FreeOmegaMixedMeasure bool _).
  - exact (@FIStop residualE SubEnum (FreeOmega SubEnum) SFI
      FreeOmegaMixedMeasure bool _).
Qed.

Inductive residual_retry_pairs :
    ptree residualE SubEnum bool -> ptree residualE SubEnum bool -> Prop :=
| ResidualRetryReturn : residual_retry_pairs (Ret true) (Ret true)
| ResidualRetryLoop : residual_retry_pairs residual_retry_left residual_retry_right
| ResidualRetryDelay : residual_retry_pairs
    (Tau residual_retry_left) (Tau (Tau residual_retry_right)).

Lemma residual_retry_cuts_coupled t1 t2 :
  residual_retry_pairs t1 t2 ->
  free_omega_qlift (pfinite_guard eq residual_retry_pairs)
    (residual_retry_cut1 t1) (residual_retry_cut2 t2).
Proof.
  intro Hpair. destruct Hpair;
    unfold residual_retry_cut1, residual_retry_cut2;
    destruct (excluded_middle_informative _) as [H1|H1];
    destruct (excluded_middle_informative _) as [H2|H2].
  all: try solve [exfalso; apply H1; reflexivity | exfalso; apply H2; reflexivity].
  all: try solve [apply (f_equal (@observe residualE SubEnum bool)) in H1; discriminate H1
    | apply (f_equal (@observe residualE SubEnum bool)) in H2; discriminate H2].
  all: apply FOQLStructural; apply FOLRet; unfold pfinite_guard, observe; cbn.
  - constructor. reflexivity.
  - constructor. apply sem_lift_refl. intros []; constructor.
  - constructor. apply sem_lift_refl. intros []; constructor.
Qed.

Lemma residual_retries_peutt :
  @peutt residualE SubEnum (FreeOmega SubEnum) SFI
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool bool eq
    residual_retry_left residual_retry_right.
Proof.
  eapply peutt_coinduction_finite_internal_policies with
    (sim := residual_retry_pairs)
    (cut1 := residual_retry_cut1) (cut2 := residual_retry_cut2).
  - apply residual_retry_cut1_valid.
  - apply residual_retry_cut2_valid.
  - apply residual_retry_cuts_coupled.
  - constructor.
Qed.

(** Infinitely many visible rounds, each with a finite administrative delay.
    This exercises the sound native up-to rule, independently of the still
    pending inclusion of the residual greatest fixed point. *)
Variant residual_tickE : Type -> Type := ResidualTick : residual_tickE unit.

CoFixpoint residual_service_left : ptree residual_tickE SubEnum bool :=
  Vis ResidualTick (fun _ => Tau residual_service_left).

CoFixpoint residual_service_right : ptree residual_tickE SubEnum bool :=
  Vis ResidualTick (fun _ => Tau (Tau residual_service_right)).

Lemma residual_services_peutt :
  @peutt residual_tickE SubEnum (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool bool eq
    residual_service_left residual_service_right.
Proof.
  eapply peutt_coinduction_upto_finite_internal with
    (sim := fun s1 s2 =>
      s1 = observe residual_service_left /\ s2 = observe residual_service_right).
  - intros s1 s2 [-> ->].
    apply stable_hitting_match_vis. intros [].
    exists (Tau residual_service_left), (Tau (Tau residual_service_right)),
      (FORet residual_service_left), (FORet residual_service_right).
    split; [reflexivity|]. split; [reflexivity|].
    split.
    + apply FITau. exact (@FIStop residual_tickE SubEnum (FreeOmega SubEnum)
        (FreeOmegaObservableSemanticMeasure
          (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
        FreeOmegaMixedMeasure bool residual_service_left).
    + split.
      * apply FITau. apply FITau.
        exact (@FIStop residual_tickE SubEnum (FreeOmega SubEnum)
          (FreeOmegaObservableSemanticMeasure
            (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
          FreeOmegaMixedMeasure bool residual_service_right).
      * apply FOQLStructural. apply FOLRet. split; reflexivity.
  - split; reflexivity.
Qed.

(** The actual RandomWalk renewal equation is already derivable in the new
    candidate, without invoking [peutt_prob] or stable hitting.  It remains
    a candidate regression until greatest-fixed-point soundness is proved. *)
Lemma random_walk_passage_residual_finite y :
  @pfinite_residual rwE SubEnum (FreeOmega SubEnum)
    SubEnum_SemanticMeasure SubEnum_SemanticMeasureCoreLaws
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure nat
    (rw_passage y)
    (Prob rw_coin (fun down : bool => if down then Ret (S y) else rw_continuation)).
Proof.
  etransitivity.
  - apply pstruct_pfinite_residual. apply passage_unfold_guarded.
  - apply pfinite_residual_of_rel.
    exact (pfinite_residual_prob_tau_prefix rw_coin (fun _ => 1)
      (fun down : bool => if down then Ret (S y) else rw_continuation)).
Qed.
