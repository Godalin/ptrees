(** Generic forward correspondence. Complete frontiers are compared by
    sem_eq, never by record equality or by an assumed lift/order reflection.
    Nested and nonterminating bodies are covered by complete-step iteration. *)
From Coq Require Import Utf8.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder KleisliIteration.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt BindScheduling.
From PTree.Interp Require Import HandlerMachine ReturnIteration.
From PTree.Examples.PGCL Require Import Syntax Forward Interpretation.
Set Implicit Arguments.
Unset Strict Implicit.

Section Correspondence.
Context {MN MF E : Type → Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI} `{MX : MixedMeasure MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Local Notation front := (handler_complete_front (E := E) (MF := MF)).
Local Notation lift_return := (@iteration_return_map E MN MF FI).

Definition returns {A} (t : ptree E MN A) (mu : MF A) :=
  sem_eq (front t) (lift_return mu).

Lemma returns_ret {A} (a : A) : returns (Ret a) (sem_ret a).
Proof.
  eapply sem_eq_trans.
  - eapply ptree_stable_hitting_unique;
      [apply handler_complete_front_hitting|apply ptree_stable_hitting_ret].
  - apply sem_eq_sym. exact (sem_bind_ret_l a
      (λ x : A, sem_ret (FHRet x : stable_head E MN A))).
Qed.

Lemma returns_diverge {A} : returns (@silent_forever E MN A) sem_zero.
Proof.
  eapply sem_eq_trans.
  - eapply ptree_stable_hitting_unique;
      [apply handler_complete_front_hitting|apply ptree_stable_hitting_spin_zero; reflexivity].
  - apply sem_eq_sym. apply sem_bind_zero_eq.
Qed.

Lemma returns_bind {A B} (t : ptree E MN A) (k : A → ptree E MN B)
    mu (K : A → MF B) :
  returns t mu → (∀ a, returns (k a) (K a)) →
  returns (PTree.bind t k) (sem_bind mu K).
Proof.
  intros Ht Hk. unfold returns, iteration_return_map in *.
  eapply sem_eq_trans with (y := sem_bind (front t) (bind_frontier k (λ a, front (k a)))).
  - eapply ptree_stable_hitting_unique; [apply handler_complete_front_hitting|].
    apply stable_hitting_bind.
    + apply BindScheduling.ptree_bind_cofinal_all.
      * exact (@sem_bind_ret_order MF FI FO BO).
      * exact (@sem_bind_zero_order MF FI FO BO).
      * exact (@mixed_bind_assoc_order MN MF FI MX FO MO).
      * exact (@mixed_bind_le_k MN MF FI MX FO MO).
      * exact (@sem_lub_cofinal MF FI FO Directed).
    + apply handler_complete_front_hitting.
    + intro a. apply handler_complete_front_hitting.
  - eapply sem_eq_trans; [apply sem_bind_eq_l; exact Ht|].
    eapply sem_eq_trans; [apply sem_bind_assoc|].
    eapply sem_eq_trans; [|apply sem_eq_sym; apply sem_bind_assoc].
    apply sem_bind_ae_proper. eapply sem_ae_mono; [|apply sem_ae_true].
    intros a _. eapply sem_eq_trans; [apply sem_bind_ret_l|].
    exact (Hk a).
Qed.

Lemma returns_prob {A X} (mu : MN X) (k : X → ptree E MN A) (K : X → MF A) :
  (∀ x, returns (k x) (K x)) → returns (Prob mu k) (mixed_bind mu K).
Proof.
  intro Hk. unfold returns, iteration_return_map in *.
  eapply sem_eq_trans with (y := mixed_bind mu (λ x, front (k x))).
  - eapply ptree_stable_hitting_unique; [apply handler_complete_front_hitting|].
    eapply stable_hitting_prob with (Good := λ _, True).
    + apply sem_ae_true.
    + intros x _. apply handler_complete_front_hitting.
  - eapply sem_eq_trans; [|apply sem_eq_sym; apply mixed_bind_assoc].
    apply mixed_bind_ae_proper. eapply sem_ae_mono; [|apply sem_ae_true].
    intros x _. apply Hk.
Qed.

Theorem returns_iter {I A} (step : I → ptree E MN (I+A)) (K : I → MF (I+A)) :
  (∀ i, returns (step i) (K i)) → ∀ i out,
  sem_iter K i out → returns (PTree.iter step i) out.
Proof.
  intros Hstep i out Hiter.
  destruct (ptree_iter_return_only_equiv (step := step)
    (front := λ j, front (step j)) (K := K)
    (λ j, handler_complete_front_hitting (step j)) Hstep Hiter)
    as [hs [Hhit Heq]].
  eapply sem_eq_trans; [|exact Heq].
  eapply ptree_stable_hitting_unique; [apply handler_complete_front_hitting|exact Hhit].
Qed.

Context {S P : Type} (coin : P → MN bool).

Theorem execute_denote (c : command S P) s :
  returns (execute (E := E) coin c s) (denote (MF := MF) coin c s).
Proof.
  induction c in s |- *; cbn [execute denote].
  - apply returns_ret.
  - apply returns_diverge.
  - apply returns_ret.
  - apply returns_bind; [apply IHc1|apply IHc2].
  - destruct (test s); [apply IHc1|apply IHc2].
  - apply returns_prob. intros []; [apply IHc1|apply IHc2].
  - apply returns_iter with (K := while_kernel test (denote (MF := MF) coin c));
      [|apply iterate_spec].
    intro t. unfold while_kernel. destruct (test t).
    + apply returns_bind; [apply IHc|]. intro u. apply returns_ret.
    + apply returns_ret.
Qed.

(** Paper-facing statement: any complete witness agrees with the independent
    compositional forward kernel. The output may have infinite support. *)
Theorem pgcl_forward_correspondence (c : command S P) K s out :
  denotes coin c K →
  ptree_stable_hitting (MF := MF) (observe (execute (E := E) coin c s)) out →
  sem_eq out (lift_return (K s)).
Proof.
  intros HD Hhit. eapply sem_eq_trans.
  - eapply ptree_stable_hitting_unique; [exact Hhit|apply handler_complete_front_hitting].
  - eapply sem_eq_trans; [apply execute_denote|].
    apply sem_bind_eq_l. apply sem_eq_sym. exact (denotes_canonical HD s).
Qed.
End Correspondence.
