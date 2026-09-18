Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Automatic Proposition Inductives.

From Coq Require Import Program.Equality RelationClasses.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import
  TwoLevelMeasure TwoLevelMeasureEnum TwoLevelMeasureSubEnum
  FreeOmegaMeasure DiscreteMC.
From PTree.Eq Require Import FiniteInternal PFiniteResidual PStrong.
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
