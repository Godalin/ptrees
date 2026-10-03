(** Backend-parametric forward semantics. This file contains no PTree and
    no external validating model. A denotation is a whole state kernel;
    while uses the existing absorbing Kleisli iteration relation.
    No chosen omega-limit is needed to state the semantics. *)
From Coq Require Import Utf8.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Prob.Interface Require Import Measure Omega Mixed KleisliIteration.
From PTree.Examples.PGCL Require Import Syntax.
Set Implicit Arguments.
Unset Strict Implicit.

Section Semantics.
Context {S P : Type} {MN MF : Type → Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.
Variable coin : P → MN bool.

Definition kernel := S → MF S.
Definition kernel_eq (K L : kernel) := ∀ s, sem_eq (K s) (L s).

Definition while_kernel (b : S → bool) (K : kernel) s : MF (S+S) :=
  if b s then sem_bind (K s) (λ t, sem_ret (inl t))
  else sem_ret (inr s).

Inductive denotes : command S P → kernel → Prop :=
| DenSkip : denotes CSkip (λ s, sem_ret s)
| DenDiverge : denotes CDiverge (λ _, sem_zero)
| DenAssign f : denotes (CAssign f) (λ s, sem_ret (f s))
| DenSeq c d K L : denotes c K → denotes d L →
    denotes (CSeq c d) (λ s, sem_bind (K s) L)
| DenIf b c d K L : denotes c K → denotes d L →
    denotes (CIf b c d) (λ s, if b s then K s else L s)
| DenChoice p c d K L : denotes c K → denotes d L →
    denotes (CChoice p c d) (λ s, mixed_bind (coin p) (λ v : bool, if v then K s else L s))
| DenWhile b c K L : denotes c K →
    (∀ s, sem_iter (while_kernel b K) s (L s)) → denotes (CWhile b c) L
| DenEquiv c K L : denotes c K → kernel_eq K L → denotes c L.

(** Forward transport of an initial subdistribution, not a backward wp. *)
Definition forward (K : kernel) (mu : MF S) := sem_bind mu K.
End Semantics.

(** A selected kernel is only an API convenience. The relation above is the
    specification; its uniqueness below makes the choice irrelevant. *)
Section Selected.
Context {S P : Type} {MN MF : Type → Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variable coin : P → MN bool.

Definition iterate (K : S → MF (S+S)) s : MF S :=
  proj1_sig (sem_lub_choose (sem_iter_approx_increasing K s)).
Lemma iterate_spec K s : sem_iter K s (iterate K s).
Proof. exact (proj2_sig (sem_lub_choose (sem_iter_approx_increasing K s))). Qed.

Fixpoint denote (c : command S P) : S → MF S :=
  match c with
  | CSkip => λ s, sem_ret s
  | CDiverge => λ _, sem_zero
  | CAssign f => λ s, sem_ret (f s)
  | CSeq c d => λ s, sem_bind (denote c s) (denote d)
  | CIf b c d => λ s, if b s then denote c s else denote d s
  | CChoice p c d => λ s, mixed_bind (coin p) (λ v : bool,
      if v then denote c s else denote d s)
  | CWhile b c => iterate (while_kernel b (denote c))
  end.

Theorem denote_spec c : denotes coin c (denote c).
Proof.
  induction c; cbn [denote].
  - apply DenSkip.
  - apply DenDiverge.
  - apply DenAssign.
  - apply DenSeq; assumption.
  - apply DenIf; assumption.
  - apply DenChoice; assumption.
  - apply DenWhile with (K := denote c); [exact IHc|].
    intro s. apply iterate_spec.
Qed.
End Selected.

Section Algebra.
Context {S P : Type} {MN MF : Type → Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI} `{MX : MixedMeasure MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variable coin : P → MN bool.
Local Notation D := (denote (S := S) (MF := MF) coin).

Lemma while_kernel_proper b (K L : S → MF S) :
  kernel_eq K L → ∀ s, sem_eq (while_kernel b K s) (while_kernel b L s).
Proof.
  intros H s. unfold while_kernel. destruct (b s); [apply sem_bind_eq_l; apply H|apply sem_eq_refl].
Qed.

Theorem denotes_canonical c K : denotes coin c K → kernel_eq K (D c).
Proof.
  intro H; induction H; intro s; cbn [denote].
  - apply sem_eq_refl.
  - apply sem_eq_refl.
  - apply sem_eq_refl.
  - eapply sem_eq_trans; [apply sem_bind_eq_l; apply IHdenotes1|].
    apply sem_bind_ae_proper. eapply sem_ae_mono; [|apply sem_ae_true].
    intros t _. apply IHdenotes2.
  - destruct (b s); [apply IHdenotes1|apply IHdenotes2].
  - apply mixed_bind_ae_proper. eapply sem_ae_mono; [|apply sem_ae_true].
    intros [] _; [apply IHdenotes1|apply IHdenotes2].
  - eapply sem_iter_proper; [apply while_kernel_proper; exact IHdenotes|apply H0|apply iterate_spec].
  - eapply sem_eq_trans; [apply sem_eq_sym; apply H0|apply IHdenotes].
Qed.

Theorem denotes_unique (c : command S P) (K L : S → MF S) :
  denotes coin c K → denotes coin c L → kernel_eq K L.
Proof.
  intros HK HL s. eapply sem_eq_trans; [exact (denotes_canonical HK s)|].
  apply sem_eq_sym. exact (denotes_canonical HL s).
Qed.

Theorem denotes_exists (c : command S P) : ∃ K : S → MF S, denotes coin c K.
Proof. exists (D c). apply denote_spec. Qed.

Theorem forward_sequence c d mu :
  sem_eq (forward (D (CSeq c d)) mu) (forward (D d) (forward (D c) mu)).
Proof. apply sem_eq_sym. apply sem_bind_assoc. Qed.

Theorem denote_endless_skip s :
  sem_eq (D (CWhile (λ _, true) CSkip) s) sem_zero.
Proof.
  eapply sem_lub_unique; [apply iterate_spec|].
  eapply sem_lub_chain_proper with (chain := λ _, sem_zero).
  - intro n. apply sem_eq_sym.
    induction n as [|n IH]; [apply sem_eq_refl|].
    cbn [sem_iter_approx sem_iter_step while_kernel denote].
    eapply sem_eq_trans; [apply sem_bind_eq_l; apply sem_bind_ret_l|].
    eapply sem_eq_trans; [apply sem_bind_ret_l|exact IH].
  - apply sem_lub_constant.
Qed.

Context `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}.
Theorem denote_while_unfold b c s :
  sem_eq (D (CWhile b c) s)
    (if b s then sem_bind (D c s) (D (CWhile b c)) else sem_ret s).
Proof.
  eapply sem_eq_trans.
  - apply (sem_iter_fixed_point (K := while_kernel b (D c))). intro t. apply iterate_spec.
  - unfold sem_iter_step, while_kernel. destruct (b s).
    + eapply sem_eq_trans; [apply sem_bind_assoc|].
      apply sem_bind_ae_proper. eapply sem_ae_mono; [|apply sem_ae_true].
      intros t _. exact (sem_bind_ret_l (inl t)
        (λ v : S+S, match v with inl j => D (CWhile b c) j | inr a => sem_ret a end)).
    + exact (sem_bind_ret_l (inr s)
        (λ v : S+S, match v with inl j => D (CWhile b c) j | inr a => sem_ret a end)).
Qed.

(** Classical bottom-started iteration, not an arbitrary fixed-point
    solution. Round n of a return-only PTree summary corresponds to S n
    of these approximants (ReturnIteration.v). *)
Theorem denote_while_approximants b c s :
  sem_lub (λ n, sem_iter_approx (while_kernel b (D c)) n s)
    (D (CWhile b c) s).
Proof. apply iterate_spec. Qed.

(** Order-theoretic leastness is conditional on genuine supremum laws.
    These are deliberately NOT claimed for the raw FreeOmega order. *)
Theorem denote_while_least b c
    (upper : ∀ (chain : nat → MF S) out, sem_lub chain out →
      ∀ n, sem_le (chain n) out)
    (least : ∀ (chain : nat → MF S) out bound, sem_lub chain out →
      (∀ n, sem_le (chain n) bound) → sem_le out bound) :
  (∀ s, sem_le (sem_iter_step (while_kernel b (D c)) (D (CWhile b c)) s)
                  (D (CWhile b c) s) ∧
        sem_le (D (CWhile b c) s)
          (sem_iter_step (while_kernel b (D c)) (D (CWhile b c)) s)) ∧
  (∀ Y, (∀ s, sem_le (sem_iter_step (while_kernel b (D c)) Y s) (Y s)) →
    ∀ s, sem_le (D (CWhile b c) s) (Y s)).
Proof.
  apply (sem_iter_least_fixed_point (K := while_kernel b (D c)) upper least).
  intro s. apply iterate_spec.
Qed.
End Algebra.

Declare Scope pgcl_denotation_scope.
Delimit Scope pgcl_denotation_scope with pgcl_den.
Module PGCLDenotationNotations.
Notation "'⟦' c '⟧[' coin ']'" := (denote coin c)
  (at level 0, c at level 200, coin at level 0) : pgcl_denotation_scope.
Notation "c '⇓[' coin ']' K" := (denotes coin c K)
  (at level 70, coin at level 0, K at next level) : pgcl_denotation_scope.
End PGCLDenotationNotations.
