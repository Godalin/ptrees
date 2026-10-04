(** Public source-language algebra. Equality is pointwise equality of forward
    kernels, not equality of syntax or of Coq functions. No concrete backend,
    PTree implementation or external validation is imported here. *)
From Coq Require Import Utf8 Morphisms RelationClasses.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder KleisliIteration.
From PTree.Examples.PGCL Require Export Syntax Forward.
Set Implicit Arguments.
Unset Strict Implicit.

Section Equations.
Context {S P : Type} {MN MF : Type → Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI} `{MX : MixedMeasure MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variable coin : P → MN bool.
Local Notation D := (denote (S := S) (MF := MF) coin).

Definition cequiv (c d : command S P) := kernel_eq (D c) (D d).

#[global] Instance cequiv_equivalence : Equivalence cequiv.
Proof.
  split.
  - intros c s. apply sem_eq_refl.
  - intros c d H s. apply sem_eq_sym, H.
  - intros c d e H G s. eapply sem_eq_trans; [apply H|apply G].
Qed.

#[global] Instance seq_Proper : Proper (cequiv ==> cequiv ==> cequiv) (@CSeq S P).
Proof.
  intros c c' H d d' G s. cbn [denote].
  eapply sem_eq_trans; [apply sem_bind_eq_l; apply H|].
  apply sem_bind_ae_proper. eapply sem_ae_mono; [|apply sem_ae_true].
  intros t _. apply G.
Qed.

#[global] Instance if_Proper b : Proper (cequiv ==> cequiv ==> cequiv) (CIf b).
Proof. intros c c' H d d' G s. cbn [denote]. destruct (b s); [apply H|apply G]. Qed.

#[global] Instance choice_Proper p : Proper (cequiv ==> cequiv ==> cequiv) (CChoice p).
Proof.
  intros c c' H d d' G s. cbn [denote].
  apply mixed_bind_ae_proper. eapply sem_ae_mono; [|apply sem_ae_true].
  intros [] _; [apply H|apply G].
Qed.

#[global] Instance while_Proper b : Proper (cequiv ==> cequiv) (CWhile b).
Proof.
  intros c d H s. eapply sem_iter_proper;
    [apply while_kernel_proper; exact H|apply iterate_spec|apply iterate_spec].
Qed.

Theorem cequiv_denotes c d :
  cequiv c d ↔ ∀ K, denotes coin c K ↔ denotes coin d K.
Proof.
  split.
  - intros H K. split; intro HK.
    + eapply DenEquiv; [apply denote_spec|].
      intro s. eapply sem_eq_trans; [apply sem_eq_sym, H|].
      apply sem_eq_sym. exact (denotes_canonical HK s).
    + eapply DenEquiv; [apply denote_spec|].
      intro s. eapply sem_eq_trans; [apply H|].
      apply sem_eq_sym. exact (denotes_canonical HK s).
  - intro H. intro s.
    apply denotes_canonical. apply (proj1 (H (D c))). apply denote_spec.
Qed.

Theorem seq_skip_l c : cequiv (CSeq CSkip c) c.
Proof. intro s. apply sem_bind_ret_l. Qed.

Theorem seq_assoc c d e : cequiv (CSeq (CSeq c d) e) (CSeq c (CSeq d e)).
Proof. intro s. apply sem_bind_assoc. Qed.

Theorem seq_diverge_l `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
    `{BindOrder : @SemanticMeasureBindOrderLaws MF FI FO}
    c : cequiv (CSeq CDiverge c) CDiverge.
Proof. intro s. apply sem_bind_zero_eq. Qed.

Theorem assign_assign f g : cequiv (CSeq (CAssign f) (CAssign g)) (CAssign (λ s, g (f s))).
Proof. intro s. exact (sem_bind_ret_l (f s) (λ t, sem_ret (g t))). Qed.

Theorem assign_id : cequiv (CAssign (λ s, s)) CSkip.
Proof. intro s. apply sem_eq_refl. Qed.

Theorem if_same b c : cequiv (CIf b c c) c.
Proof. intro s. cbn [denote]. destruct (b s); reflexivity. Qed.

Theorem if_true c d : cequiv (CIf (λ _, true) c d) c.
Proof. intro s. apply sem_eq_refl. Qed.

Theorem if_false c d : cequiv (CIf (λ _, false) c d) d.
Proof. intro s. apply sem_eq_refl. Qed.

Theorem if_seq b c d e : cequiv (CSeq (CIf b c d) e) (CIf b (CSeq c e) (CSeq d e)).
Proof. intro s. cbn [denote]. destruct (b s); reflexivity. Qed.

Theorem choice_seq p c d e :
  cequiv (CSeq (CChoice p c d) e) (CChoice p (CSeq c e) (CSeq d e)).
Proof.
  intro s. cbn [denote]. eapply sem_eq_trans; [apply mixed_bind_assoc|].
  apply mixed_bind_ae_proper. eapply sem_ae_mono; [|apply sem_ae_true].
  intros [] _; reflexivity.
Qed.

Theorem while_skip_diverge : cequiv (CWhile (λ _, true) CSkip) CDiverge.
Proof. intro s. apply denote_endless_skip. Qed.

(** This unit law is NOT a field of the minimal BindLaws interface.
    Keep its ordinary measure-level premise explicit, rather than inventing
    a command-level class or silently assuming all interfaces provide it. *)
Theorem seq_skip_r
    (right_unit : ∀ (mu : MF S), sem_eq (sem_bind mu sem_ret) mu) c :
  cequiv (CSeq c CSkip) c.
Proof. intro s. apply right_unit. Qed.

Context `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}.
Theorem while_unfold b c :
  cequiv (CWhile b c) (CIf b (CSeq c (CWhile b c)) CSkip).
Proof. intro s. exact (denote_while_unfold coin b c s). Qed.

Theorem while_false c : cequiv (CWhile (λ _, false) c) CSkip.
Proof. rewrite while_unfold, if_false. reflexivity. Qed.
End Equations.

Module PGCLAlgebraNotations.
Notation "c '≈g[' coin ']' d" := (cequiv coin c d)
  (at level 70, coin at level 0, no associativity) : pgcl_scope.
End PGCLAlgebraNotations.
