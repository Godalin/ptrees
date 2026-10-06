(** * MixedHead: up-to-bind refinement followed by native coupling

    Appendix reading path:
      masked_impl -- up to bind --> kernel_impl
                  -- native coupling --> mixed_spec.

    Protocol.v retains the original direct proof unchanged. Here we
    reuse only its programs and finite-distribution calculations, not its
    final protocol equivalence. Challenge/Reply provide visible progress;
    sampling itself is NOT a coinductive guard. *)
From Coq Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ITree.Basics Require Import Monad.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure Quotient Measure.
From PTree.Eq Require Import Shallow UnifiedFrontier PEutt StableHittingRelation PTreeKernel.
From PTree.Eq.FreeOmega Require Import Base Hitting Relation Bind.
From PTree.Examples.MixedHead Require Import Protocol.
Set Implicit Arguments.
Unset Strict Implicit.
Import PTree MonadNotation SemanticMeasureNotations.
Local Open Scope monad_scope.
Local Open Scope semantic_measure_scope.
Local Open Scope freeomega_scope.

Local Notation tree := (ptree mixedE SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation MX := (@FreeOmegaMixedMeasure SubEnumQ).
Local Notation W := (PEutt.peutt (E := mixedE) (MN := SubEnumQ)
  (FI := FI) (MX := MX) (FO := FO)).
Local Notation "t ≈ₚ u" := (W eq t u)
  (at level 70, no associativity) : type_scope.
Local Notation "t ≈ₚ[ RR ] u" := (W RR t u)
  (at level 70, RR at next level, no associativity) : type_scope.

(** * 1. Factor the finite sampler, without changing masked_impl *)

Definition draw_impl (c : bool) : tree (impl_return + impl_return) :=
  mask <- sample coin_three_quarters;;
  continue <- sample uniform2;;
  payload <- (first <- sample coin_third;;
              if (first : bool) then Ret L0
              else second <- sample uniform2;; Ret (if (second : bool) then L1 else L2));;
  let bit := xorb c mask in
  Ret (if (continue : bool) then inr (bit, payload) else inl (bit, payload)).

CoFixpoint kernel_impl (m : hidden3) : tree impl_return :=
  c <- trigger Challenge;;
  x <- sample (mixed_samples uniform3 c);;
  match x with
  | inl result => Ret result
  | inr (b,h) => Vis (Reply b) (λ (ack : bool), kernel_impl (if ack then h else m))
  end.

(** A finite program equivalence, proved before either coinduction. The
    endpoint is homogeneous: no 3-to-2 abstraction is used at this stage. *)
Lemma draw_impl_kernel c :
  draw_impl c ≈ₚ sample (mixed_samples uniform3 c).
Proof.
  eapply peutt_of_hitting_lift with
    (out1 := x ←ω draw_distribution c ;; ηω (FHRet x))
    (out2 := x ←ω mixed_samples uniform3 c ;; ηω (FHRet x)).
  - unfold draw_impl, draw_distribution.
    apply stable_hitting_native_sample. intro mask.
    apply stable_hitting_native_sample. intro continue.
    cbn [observe].
    apply stable_hitting_native_sample. intros [].
    + apply stable_hitting_native_ret.
    + cbn [observe].
      apply stable_hitting_native_sample. intro second.
      apply stable_hitting_native_ret.
  - eapply (stable_hitting_prob (FO := FO) (MX := MX)) with (Good := λ _, True).
    + apply sem_ae_true.
    + intros x _. apply (stable_hitting_ret (FO := FO) (MX := MX)).
  - eapply FOQLSample with (T := eq).
    + exact (draw_distribution_mixed c).
    + intros x y ->. apply FOQLStructural. constructor. constructor. reflexivity.
Qed.

(** * 2. Up to bind: replace the sampler inside a recursive protocol

    The candidate contains roots and pending Reply states only. The sampler
    followed by its continuation is not in the candidate: up-to-bind removes
    that context using the independently proved draw_impl_kernel. *)
Theorem masked_kernel_equivalent m : masked_impl m ≈ₚ kernel_impl m.
Proof.
  eapply peutt_coinduction_upto_bind with
    (sim := λ s1 s2,
      (∃ old, s1 = observe (masked_impl old) ∧ s2 = observe (kernel_impl old)) ∨
      (∃ old h b,
        s1 = VisF (Reply b) (λ (ack : bool), masked_impl (if ack then h else old)) ∧
        s2 = VisF (Reply b) (λ (ack : bool), kernel_impl (if ack then h else old))));
    try typeclasses eauto.
  - intros. apply ptree_bind_cofinal_all.
  - intros s1 s2 [(old & -> & ->) | (old & h & b & -> & ->)].
    + apply stable_hitting_match_vis. intro answer.
      cbn [observe].
      eapply bind_upto_closure_bind with (RR := eq) (t1 := draw_impl answer).
      * apply draw_impl_kernel.
      * intros [r|[b h]] y <-.
        -- right. apply peutt_ret. reflexivity.
        -- left. right. exists old, h, b. split; reflexivity.
    + apply stable_hitting_match_vis. intro ack.
      apply bind_upto_closure_includes. left.
      exists (if ack then h else old). split; reflexivity.
  - left. exists m. split; reflexivity.
Qed.

(** * 3. Ordinary coinduction: couple the complete Ret/Vis frontiers

    The candidate contains roots and post-Challenge sampling states. For
    sampling states we construct their complete frontiers, then use the
    existing 3-to-2 coupling. Returns satisfy return_rel; Reply continuations
    return to related roots. Both old and fresh bridges are needed for ack.
    No probability up-to closure is used, and Prob is not a progress guard. *)
Theorem kernel_spec_equivalent m z :
  bridge m z → kernel_impl m ≈ₚ[return_rel] mixed_spec z.
Proof.
  intro Hinitial.
  eapply peutt_coinduction with
    (sim := λ s1 s2,
      (∃ old z, bridge old z ∧
        s1 = observe (kernel_impl old) ∧ s2 = observe (mixed_spec z)) ∨
      (∃ old z c, bridge old z ∧
        s1 = observe (x <- sample (mixed_samples uniform3 c);;
          match x with
          | inl r => Ret r
          | inr (b,h) => Vis (Reply b) (λ (ack : bool), kernel_impl (if ack then h else old))
          end) ∧
        s2 = observe (x <- sample (mixed_samples uniform2 c);;
          match x with
          | inl r => Ret r
          | inr (b,j) => Vis (Reply b) (λ (ack : bool), mixed_spec (if ack then j else z))
          end)));
    try typeclasses eauto.
  - intros s1 s2 [(old & z' & Hold & -> & ->) |
      (old & z' & c & Hold & -> & ->)].
    + apply stable_hitting_match_vis. intro answer.
      cbn [observe].
      right. exists old, z', answer. split; [exact Hold|]. split; reflexivity.
    + cbn [observe].
      eapply stable_hitting_match_of_hitting_lift.
      * eapply (stable_hitting_prob (FO := FO) (MX := MX)) with
          (Good := λ _, True)
          (front := λ x, match x with inl r => _ | inr (b,h) => _ end).
        -- apply sem_ae_true.
        -- intros [r|[b h]] _; cbn [observe].
           ++ apply (stable_hitting_ret (FO := FO) (MX := MX)).
           ++ apply (stable_hitting_vis (FO := FO) (MX := MX)).
      * eapply (stable_hitting_prob (FO := FO) (MX := MX)) with
          (Good := λ _, True)
          (front := λ x, match x with inl r => _ | inr (b,j) => _ end).
        -- apply sem_ae_true.
        -- intros [r|[b j]] _; cbn [observe].
           ++ apply (stable_hitting_ret (FO := FO) (MX := MX)).
           ++ apply (stable_hitting_vis (FO := FO) (MX := MX)).
      * eapply FOQLSample with (T := mixed_sample_rel).
        -- exact (mixed_samples_lift c).
        -- intros [r|[b h]] [u|[b' j]] H; simpl in H; try contradiction;
             apply FOQLStructural; constructor.
           ++ constructor. exact H.
           ++ destruct H as [Hbit Hfresh]. simpl in Hbit, Hfresh. subst b'.
              constructor. intro ack. left.
              exists (if ack then h else old), (if ack then j else z').
              split; [destruct ack; assumption|]. split; reflexivity.
  - left. exists m, z. repeat split; try assumption; reflexivity.
Qed.

(** * 4. Same public claim, obtained by composing the two refinements

    This proof does not call Protocol.masked_protocol_equivalent. *)
Theorem masked_protocol_equivalent_upto m :
  masked_impl m ≈ₚ[return_rel] mixed_spec (abstract_state m).
Proof.
  eapply peutt_rel_compose with (R12 := eq) (R23 := return_rel).
  - intros a b c -> H. exact H.
  - apply masked_kernel_equivalent.
  - apply kernel_spec_equivalent. destruct m; simpl; auto.
Qed.
