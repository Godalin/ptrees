(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq.Logic Require Import ClassicalChoice.

From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
From PTree.Eq.Internal Require Import FiniteInternal.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt PStrong.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The semantic bridge is separate from the operational judgment. *)
Section FiniteInternalHitting.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{FI : SemanticMeasure MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.
Section OneReturnType.
Context {R : Type}.
Local Notation K := (@ptree_primitive_kernel E MN MF FI MX R).

Theorem finite_internal_hitting_lift t out
    (front : ptree E MN R -> MF (stable_head E MN R)) target :
  finite_internal t out ->
  (forall u, stable_hitting K (observe u) (front u)) ->
  stable_hitting K (observe t) target ->
  sem_lift eq target (sem_bind out front).
Proof.
  intros Hexec Hfront. revert target. induction Hexec; intros target Htarget.
  - eapply sem_lift_proper_r.
    + apply sem_eq_sym. apply sem_bind_ret_l.
    + eapply sem_lift_proper_l.
      * eapply stable_hitting_unique; [apply Hfront|exact Htarget].
      * apply sem_lift_refl. intro h. reflexivity.
  - apply IHHexec. apply (proj1 (stable_hitting_tau_iff t target)).
    exact Htarget.
  - assert (Hprob : stable_hitting K (observe (Prob mu k))
        (mixed_bind mu (fun x => front (k x)))).
    { eapply stable_hitting_prob with (Good := fun _ => True).
      - apply sem_ae_true.
      - intros x _. apply Hfront. }
    eapply sem_lift_proper_l.
    + eapply stable_hitting_unique; [exact Hprob|exact Htarget].
    + eapply sem_lift_proper_r.
      * apply sem_eq_sym. apply mixed_bind_assoc.
      * eapply mixed_lift_bind with (R := eq).
        -- apply sem_lift_refl. intro x. reflexivity.
        -- intros x y ->. apply H0. apply Hfront.
Qed.

End OneReturnType.

(** Finite compression preserves generator-level matching, for an arbitrary
    continuation candidate.  No folding into [peutt] is used here. *)
Theorem finite_internal_match {A B} (RR : A -> B -> Prop)
    (sim : ptree' E MN A -> ptree' E MN B -> Prop)
    (S : ptree E MN A -> ptree E MN B -> Prop)
    (t1 : ptree E MN A) (t2 : ptree E MN B) out1 out2 :
  finite_internal t1 out1 -> finite_internal t2 out2 ->
  sem_lift S out1 out2 ->
  (forall u v, S u v ->
    stable_hitting_match
      (@ptree_primitive_kernel E MN MF FI MX A)
      (@ptree_primitive_kernel E MN MF FI MX B)
      (ptree_stable_head_rel RR) sim (observe u) (observe v)) ->
  stable_hitting_match
    (@ptree_primitive_kernel E MN MF FI MX A)
    (@ptree_primitive_kernel E MN MF FI MX B)
    (ptree_stable_head_rel RR) sim (observe t1) (observe t2).
Proof.
  intros Hexec1 Hexec2 Hres Hmatch.
  assert (Hex1 : forall u : ptree E MN A, exists out,
      stable_hitting (@ptree_primitive_kernel E MN MF FI MX A)
        (observe u) out).
  { intro u. apply stable_hitting_exists. }
  assert (Hex2 : forall u : ptree E MN B, exists out,
      stable_hitting (@ptree_primitive_kernel E MN MF FI MX B)
        (observe u) out).
  { intro u. apply stable_hitting_exists. }
  destruct (choice _ Hex1) as [front1 Hfront1].
  destruct (choice _ Hex2) as [front2 Hfront2].
  eapply stable_hitting_match_of_hitting_lift; [apply Hfront1|apply Hfront2|].
  eapply sem_lift_mono with
    (R := fun x z => exists y, x = y /\ ptree_stable_head_rel RR sim y z).
  - intros x z [y [-> Hyz]]. exact Hyz.
  - eapply sem_lift_comp.
    + eapply finite_internal_hitting_lift;
        [exact Hexec1|exact Hfront1|apply Hfront1].
    + eapply sem_lift_mono with
        (R := fun x z => exists y, ptree_stable_head_rel RR sim x y /\ z = y).
      * intros x z [y [Hxy Heq]]. subst y. exact Hxy.
      * eapply sem_lift_comp.
        -- eapply sem_lift_bind; [exact Hres|].
           intros u v Huv. eapply stable_hitting_match_hitting_lift;
             [apply Hmatch; exact Huv|apply Hfront1|apply Hfront2].
        -- apply sem_lift_sym. eapply finite_internal_hitting_lift;
             [exact Hexec2|exact Hfront2|apply Hfront2].
Qed.

(** Sound inductive compression around an already established behavioral
    relation. *)
Theorem peutt_of_finite_internal {A B} (RR : A -> B -> Prop)
    (t1 : ptree E MN A) (t2 : ptree E MN B) out1 out2 :
  finite_internal t1 out1 -> finite_internal t2 out2 ->
  sem_lift (@peutt E MN MF FI FC MX FO A B RR) out1 out2 ->
  peutt RR t1 t2.
Proof.
  intros H1 H2 Hlift. apply peutt_fold.
  eapply finite_internal_match; [exact H1|exact H2|exact Hlift|].
  intros u v Huv. apply peutt_unfold. exact Huv.
Qed.

Section FiniteInternalCoinduction.
Context {A B : Type} (RR : A -> B -> Prop).

Definition finite_internal_closure
    (sim : ptree' E MN A -> ptree' E MN B -> Prop) s1 s2 : Prop :=
  exists t1 t2 out1 out2,
    s1 = observe t1 /\ s2 = observe t2 /\
    finite_internal t1 out1 /\ finite_internal t2 out2 /\
    sem_lift (fun u v => sim (observe u) (observe v)) out1 out2.

Lemma finite_internal_closure_includes sim s1 s2 :
  sim s1 s2 -> finite_internal_closure sim s1 s2.
Proof.
  intro H. exists (go s1), (go s2), (sem_ret (go s1)), (sem_ret (go s2)).
  split; [reflexivity|]. split; [reflexivity|].
  split; [apply FIStop|]. split; [apply FIStop|].
  apply sem_lift_ret. exact H.
Qed.

Lemma finite_internal_closure_compatible sim
    (Hprogress : forall s1 s2, sim s1 s2 ->
      stable_hitting_match
        (@ptree_primitive_kernel E MN MF FI MX A)
        (@ptree_primitive_kernel E MN MF FI MX B)
        (ptree_stable_head_rel RR) (finite_internal_closure sim) s1 s2) :
  forall s1 s2, finite_internal_closure sim s1 s2 ->
    stable_hitting_match
      (@ptree_primitive_kernel E MN MF FI MX A)
      (@ptree_primitive_kernel E MN MF FI MX B)
      (ptree_stable_head_rel RR) (finite_internal_closure sim) s1 s2.
Proof.
  intros s1 s2 [t1 [t2 [out1 [out2 [-> [-> [H1 [H2 Hlift]]]]]]]].
  eapply finite_internal_match; [exact H1|exact H2|exact Hlift|].
  intros u v Huv. apply Hprogress. exact Huv.
Qed.

(** Sound up-to-compression coinduction for the native hitting generator.
    The caller still owes a complete hitting match per candidate round;
    this must not be confused with an arbitrary internal [pstrongF] guard. *)
Theorem peutt_coinduction_upto_finite_internal sim
    (Hprogress : forall s1 s2, sim s1 s2 ->
      stable_hitting_match
        (@ptree_primitive_kernel E MN MF FI MX A)
        (@ptree_primitive_kernel E MN MF FI MX B)
        (ptree_stable_head_rel RR) (finite_internal_closure sim) s1 s2) :
  forall t1 t2, sim (observe t1) (observe t2) -> peutt RR t1 t2.
Proof.
  eapply peutt_coinduction_upto_closure.
  - exact finite_internal_closure_includes.
  - exact finite_internal_closure_compatible.
  - exact Hprogress.
Qed.

End FiniteInternalCoinduction.

End FiniteInternalHitting.
