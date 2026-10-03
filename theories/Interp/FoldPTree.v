(** Agreement between monadic folding and productive tree interpretation.
    The proof-only pacing below accounts for the fold's post-operation Tau;
    it does not impose termination or guardedness on the source/handler. *)
From Coq Require Import Utf8 Morphisms RelationClasses Lia.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinition Fold.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder RelationalClosure.
From PTree.Eq Require Import Shallow PStruct PEutt Relation Algebra Bind BindScheduling
  UnifiedFrontier PTreeKernel PrimitiveStableHitting RelationalHitting StableHittingRelation.
From PTree.Interp Require Import IterationUniform Unrestricted Structural HandlerRelation HandlerFacts.
Set Implicit Arguments.
Unset Strict Implicit.
Notation "` R" := (elem R) (at level 10).

(** One administrative delay after either kind of operation. *)
Local CoFixpoint paced {E MN A} (t : ptree E MN A) : ptree E MN A :=
  match observe t with
  | RetF a => Ret a
  | TauF u => Tau (paced u)
  | VisF _ e k => Vis e (λ x, Tau (paced (k x)))
  | ProbF _ mu k => Prob mu (λ x, Tau (paced (k x)))
  end.

Local Lemma observe_paced {E MN A} (t : ptree E MN A) :
  observe (paced t) =
    match observe t with
    | RetF a => RetF a
    | TauF u => TauF (paced u)
    | VisF _ e k => VisF e (λ x, Tau (paced (k x)))
    | ProbF _ mu k => ProbF mu (λ x, Tau (paced (k x)))
    end.
Proof. unfold observe at 1. cbn. destruct (observe t); reflexivity. Qed.

Section Pacing.
Context {E MN MF : Type → Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}.
Context {A : Type}.

Local Definition paced_kernel (s : ptree' E MN A) :=
  match s with
  | RetF a => sem_ret (SHStable (FHRet a))
  | TauF u => sem_ret (SHInternal (observe u))
  | VisF _ e k => sem_ret (SHStable (FHVis e (λ x, Tau (paced (k x)))))
  | ProbF _ mu k => mixed_bind mu (λ x, sem_ret (SHInternal (observe (k x))))
  end.
Local Definition paced_approx n t := stable_hitting_approx paced_kernel n (observe t).
Local Definition after n t := match n with O => sem_zero | S m => paced_approx m t end.
Local Notation equiv := (@BindScheduling.equiv MF FI FO).
#[local] Existing Instance BindScheduling.equiv_equivalence.
#[local] Existing Instance BindScheduling.le_equiv_Proper.
#[local] Existing Instance BindScheduling.bind_equiv_Proper.
#[local] Instance paced_mixed_equiv X Y (mu : MN X) :
  Proper (pointwise_relation X (@equiv Y) ==> @equiv Y) (mixed_bind mu).
Proof. apply BindScheduling.mixed_equiv_Proper. apply mixed_bind_le_k. Qed.
Local Notation hit_unfold := (@BindScheduling.hitting_unfold E MN MF FI MX FO Ord
  (@sem_bind_ret_order MF FI FO BO) (@mixed_bind_assoc_order MN MF FI MX FO MO)
  (@mixed_bind_le_k MN MF FI MX FO MO)).

Local Lemma paced_approx_unfold n t :
  equiv (paced_approx n t)
    (match observe t with
     | RetF a => sem_ret (FHRet a)
     | TauF u => after n u
     | VisF _ e k => sem_ret (FHVis e (λ x, Tau (paced (k x))))
     | ProbF _ mu k => mixed_bind mu (λ x, after n (k x))
     end).
Proof.
  unfold paced_approx, stable_hitting_approx, paced_kernel.
  destruct (observe t).
  all: try (etransitivity; [apply sem_bind_ret_order|]; destruct n; reflexivity).
  etransitivity; [apply mixed_bind_assoc_order|].
  apply paced_mixed_equiv. intro x.
  etransitivity; [apply sem_bind_ret_order|]. destruct n; reflexivity.
Qed.

Local Lemma paced_tree_le n t :
  sem_le (ptree_hitting_approx (MF := MF) n (observe (paced t))) (paced_approx n t).
Proof.
  revert t. induction n as [|n IH]; intro t.
  all: rewrite observe_paced; setoid_rewrite paced_approx_unfold.
  all: destruct (observe t); setoid_rewrite hit_unfold; cbn [after observe].
  all: try apply sem_le_refl.
  - apply IH.
  - apply mixed_bind_le_k. intro x.
    destruct n as [|m]; setoid_rewrite hit_unfold.
    + apply sem_zero_le.
    + cbn [observe]. eapply sem_le_trans; [|apply IH]. apply ptree_hitting_mono. lia.
Qed.

Local Lemma paced_kernel_le n t :
  sem_le (paced_approx n t)
    (ptree_hitting_approx (MF := MF) (2*n) (observe (paced t))).
Proof.
  revert t. induction n as [|n IH]; intro t.
  all: rewrite observe_paced; setoid_rewrite paced_approx_unfold.
  - destruct (observe t); setoid_rewrite hit_unfold; cbn [after observe];
      try apply sem_le_refl.
  - replace (2*S n) with (S (S (2*n))) by lia.
    destruct (observe t); setoid_rewrite hit_unfold; cbn [after observe].
    + apply sem_le_refl.
    + eapply sem_le_trans; [apply IH|]. apply ptree_hitting_mono. lia.
    + apply sem_le_refl.
    + apply mixed_bind_le_k. intro x. setoid_rewrite hit_unfold. apply IH.
Qed.

Context `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}.
Local Lemma paced_hitting t out :
  stable_hitting paced_kernel (observe t) out →
  ptree_stable_hitting (MF := MF) (observe (paced t)) out.
Proof.
  unfold stable_hitting, ptree_stable_hitting, stable_hitting.
  enough (H : sem_lub (λ n, paced_approx n t) out ↔
    sem_lub (λ n, ptree_hitting_approx (MF := MF) n (observe (paced t))) out)
    by exact (proj1 H).
  apply sem_lub_cofinal.
  - exact (stable_hitting_increasing paced_kernel (observe t)).
  - apply ptree_hitting_increasing.
  - intro n. exists (2*n). apply paced_kernel_le.
  - intro n. exists n. apply paced_tree_le.
Qed.
End Pacing.

Section PacingSoundness.
Context {E MN MF : Type → Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}.
Variables (Hmixed : relational_mixed_bind NI FI MX)
  (Hzero : relational_zero FO) (Hlimit : relational_lub FO).
Context {A : Type}.
Local Definition paced_states (s v : ptree' E MN A) :=
  ∃ t, v = observe t ∧
    (s = observe (paced t) ∨ s = observe (Tau (paced t))).
Local Notation HR := (@ptree_stable_head_rel E MN A A eq paced_states).

Local Lemma paced_kernel_related s v : s = v →
  sem_lift (stable_target_rel eq HR)
    (paced_kernel (MF := MF) s) (ptree_primitive_kernel (MF := MF) v).
Proof.
  intros ->. destruct v; cbn [paced_kernel ptree_primitive_kernel].
  - apply sem_lift_ret. constructor. reflexivity.
  - apply sem_lift_ret. reflexivity.
  - apply sem_lift_ret. constructor. intro x.
    exists (k x). split; [reflexivity|right; reflexivity].
  - eapply Hmixed with (R := eq); [apply sem_lift_refl; intro x; reflexivity|].
    intros x y ->. apply sem_lift_ret. reflexivity.
Qed.

Local Lemma paced_peutt (t : ptree E MN A) :
  peutt (MF := MF) eq (paced t) t.
Proof.
  eapply peutt_coinduction with (sim := paced_states).
  - intros s v [u [-> Hs]].
    destruct (stable_hitting_exists (paced_kernel (MF := MF)) (observe u)) as [mu Hmu].
    destruct (ptree_stable_hitting_exists (MF := MF) (observe u)) as [nu Hnu].
    assert (HsHit : ptree_stable_hitting (MF := MF) s mu).
    { destruct Hs as [Hs|Hs]; rewrite Hs.
      - apply paced_hitting. exact Hmu.
      - apply (proj2 (ptree_stable_hitting_tau_iff _ _)).
        apply paced_hitting. exact Hmu. }
    eapply stable_hitting_match_of_hitting_lift; [exact HsHit|exact Hnu|].
    eapply (stable_hitting_rel (relational_bind_of_laws FB) Hzero
      paced_kernel_related Hlimit); eauto.
  - exists t. split; [reflexivity|left; reflexivity].
Qed.
End PacingSoundness.

Section StructuralAgreement.
Context {E F MN : Type → Type} (h : ∀ X, E X → ptree F MN X).
Context {A : Type}.
Local Definition before := λ X (e : E X), Tau (@h X e).
Local Definition run (t : ptree E MN A) := fold before (@PTree.sample F MN) t.
Local Definition finish (v : ptree E MN A + A) :=
  match v with inl t => Tau (run t) | inr a => Ret a end.
Local Definition interpreted (t : ptree E MN A) := PTree.interp_tree h (paced t).
Local Definition active {X} (u : ptree F MN X) (k : X → ptree E MN A) :=
  PTree.bind (PTree.bind u (λ x, Ret (inl (k x)))) finish.
Local Definition active_interp {X} (u : ptree F MN X) (k : X → ptree E MN A) :=
  PTree.bind u (λ x, PTree.interp_tree h (Tau (paced (k x)))).

Local Lemma observe_run t :
  observe (run t) = match observe t with
  | RetF a => RetF a
  | TauF u => TauF (run u)
  | VisF _ e k => TauF (active (h e) k)
  | ProbF _ mu k => ProbF mu (λ x, PTree.bind (PTree.bind (Ret x)
      (λ y, Ret (inl (k y)))) finish)
  end.
Proof.
  unfold run, fold. change (observe
    (PTree.bind (fold_step before (@PTree.sample F MN) t) finish) =
    match observe t with
    | RetF a => RetF a
    | TauF u => TauF (run u)
    | VisF _ e k => TauF (active (h e) k)
    | ProbF _ mu k => ProbF mu (λ x, PTree.bind (PTree.bind (Ret x)
        (λ y, Ret (inl (k y)))) finish)
    end).
  rewrite observe_bind. unfold fold_step. destruct (observe t); reflexivity.
Qed.

Local Definition schedule_candidate (l r : ptree F MN A) :=
  (∃ t, l = run t ∧ r = interpreted t) ∨
  (∃ X (u : ptree F MN X) k, l = active u k ∧ r = active_interp u k) ∨
  (∃ t, observe l = TauF (run t) ∧ observe r = TauF (interpreted t)).

Local Lemma fold_before_structural t : pstruct eq (run t) (interpreted t).
Proof.
  assert (H : ∀ l r, schedule_candidate l r → pstruct eq l r).
  { unfold pstruct. coinduction CH CIH. intros l r Hlr.
    change (pstructF eq (` CH) (observe l) (observe r)).
    destruct Hlr as [[u [-> ->]]|[[X [u [k [-> ->]]]]|[u [Hl Hr]]]].
    - rewrite observe_run. unfold interpreted. rewrite observe_interp, observe_paced.
      destruct (observe u) as [a|v|X e k|X mu k]; cbn.
      + constructor. reflexivity.
      + constructor. apply CIH. left. exists v. split; reflexivity.
      + constructor. apply CIH. right. left. exists X, (h e), k. split; reflexivity.
      + constructor. intro x. apply CIH. right. right. exists (k x). split; reflexivity.
    - unfold active, active_interp. rewrite !observe_bind.
      destruct (observe u) as [x|v|Y e k'|Y mu k']; cbn.
      + constructor. apply CIH. left. exists (k x). split; reflexivity.
      + constructor. apply CIH. right. left. exists X, v, k. split; reflexivity.
      + constructor. intro y. apply CIH. right. left. exists X, (k' y), k. split; reflexivity.
      + constructor. intro y. apply CIH. right. left. exists X, (k' y), k. split; reflexivity.
    - rewrite Hl, Hr. constructor. apply CIH. left. exists u. split; reflexivity. }
  apply H. left. exists t. split; reflexivity.
Qed.
End StructuralAgreement.

Section Agreement.
Context {E F MN MF : Type → Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variables (Hmixed : relational_mixed_bind NI FI MX)
  (Hzero : relational_zero FO) (Hlimit : relational_lub FO).
Variable h : ∀ X, E X → ptree F MN X.
Local Notation W := (peutt (MF := MF) eq).
Local Notation structural :=
  (Relation.peutt_of_pstruct (relational_bind_of_laws FB) Hmixed Hzero Hlimit).

(** Neither source termination nor a guarded handler is assumed. The
    probability obligations are the existing generic relational profile. *)
Theorem fold_ptree_interp {A} (t : ptree E MN A) :
  W (fold h (@PTree.sample F MN) t) (PTree.interp_tree h t).
Proof.
  transitivity (fold (before h) (@PTree.sample F MN) t).
  - unfold fold. apply (peutt_iter_Proper Hzero Hlimit); [|reflexivity].
    intro u. unfold fold_step, before. destruct (observe u); try apply peutt_refl.
    eapply peutt_bind with (RR := eq).
    + apply peutt_tau_r.
    + intros x y ->. apply peutt_refl.
  - transitivity (PTree.interp_tree h (paced t)).
    + apply structural. apply fold_before_structural.
    + apply (Unrestricted.peutt_interp Hzero Hlimit).
      apply (paced_peutt Hmixed Hzero Hlimit).
Qed.

Theorem interp_ptree_agrees {A} (t : ptree E MN A) :
  W (interp h t) (PTree.interp_tree h t).
Proof. apply fold_ptree_interp. Qed.

Theorem interp_ptree_ret {A} (a : A) : W (interp h (Ret a)) (Ret a).
Proof.
  transitivity (PTree.interp_tree h (Ret a)); [apply interp_ptree_agrees|].
  apply peutt_observe_eq. reflexivity.
Qed.

Theorem interp_ptree_bind {A B} (t : ptree E MN A) (k : A → ptree E MN B) :
  W (interp h (PTree.bind t k))
    (PTree.bind (interp h t) (λ x, interp h (k x))).
Proof.
  transitivity (PTree.interp_tree h (PTree.bind t k)); [apply interp_ptree_agrees|].
  transitivity (PTree.bind (PTree.interp_tree h t) (λ x, PTree.interp_tree h (k x))).
  - apply structural. apply pstruct_interp_bind.
  - eapply peutt_bind with (RR := eq).
    + symmetry. apply interp_ptree_agrees.
    + intros x y ->. symmetry. apply interp_ptree_agrees.
Qed.

Theorem interp_ptree_tau {A} (t : ptree E MN A) :
  W (interp h (Tau t)) (interp h t).
Proof.
  rewrite !interp_ptree_agrees.
  transitivity (Tau (PTree.interp_tree h t)); [apply peutt_observe_eq; reflexivity|].
  apply peutt_tau_l.
Qed.

Theorem interp_ptree_vis {A X} (e : E X) (k : X → ptree E MN A) :
  W (interp h (Vis e k)) (PTree.bind (h e) (λ x, interp h (k x))).
Proof.
  setoid_rewrite interp_ptree_agrees.
  transitivity (Tau (PTree.bind (h e) (λ x, PTree.interp_tree h (k x))));
    [apply peutt_observe_eq; reflexivity|apply peutt_tau_l].
Qed.

Theorem interp_ptree_prob {A X} (mu : MN X) (k : X → ptree E MN A) :
  W (interp h (Prob mu k)) (Prob mu (λ x, interp h (k x))).
Proof.
  assert (Hsample : ∀ c : X → ptree F MN A,
    W (PTree.bind (PTree.sample mu) c) (Prob mu c)).
  { intro c. apply structural. apply pstruct_fold.
    cbn. constructor. intro x. apply observe_eq_pstruct. reflexivity. }
  transitivity (PTree.interp_tree h (Prob mu k)); [apply interp_ptree_agrees|].
  transitivity (Prob mu (λ x, PTree.interp_tree h (k x)));
    [apply peutt_observe_eq; reflexivity|].
  rewrite <- !Hsample.
  eapply peutt_bind with (RR := eq); [apply peutt_refl|].
  intros x y ->. symmetry. apply interp_ptree_agrees.
Qed.

Theorem interp_ptree_iter {I A} (step : I → ptree E MN (I+A)) i :
  W (interp h (PTree.iter step i)) (PTree.iter (λ j, interp h (step j)) i).
Proof.
  transitivity (PTree.interp_tree h (PTree.iter step i)); [apply interp_ptree_agrees|].
  transitivity (PTree.iter (λ j, PTree.interp_tree h (step j)) i).
  - apply structural. apply pstruct_interp_iter.
  - apply (peutt_iter_Proper Hzero Hlimit); [|reflexivity].
    intro j. symmetry. apply interp_ptree_agrees.
Qed.

Theorem interp_ptree_peutt {A B} (RR : A → B → Prop)
    (t : ptree E MN A) (u : ptree E MN B) :
  peutt (MF := MF) RR t u → peutt (MF := MF) RR (interp h t) (interp h u).
Proof.
  intro H. setoid_rewrite interp_ptree_agrees.
  apply (Unrestricted.peutt_interp Hzero Hlimit). exact H.
Qed.
End Agreement.

(** Public handler calculus. Agreement is used here once, rather than in
    every client. Proper proofs are deliberately not global instances. *)
Section Calculus.
Context {MN MF : Type → Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variables (Hmixed : relational_mixed_bind NI FI MX)
  (Hzero : relational_zero FO) (Hlimit : relational_lub FO).
Local Notation W := (peutt (MF := MF)).
Local Notation agreement := (interp_ptree_agrees Hmixed Hzero Hlimit).
Local Notation structural :=
  (Relation.peutt_of_pstruct (relational_bind_of_laws FB) Hmixed Hzero Hlimit).

Theorem interp_ptree_handler_rel {E F A B} (RR : A → B → Prop)
    (h g : ∀ X, E X → ptree F MN X)
    (t : ptree E MN A) (u : ptree E MN B) :
  peutt_handler (MF := MF) h g → W RR t u → W RR (interp h t) (interp g u).
Proof.
  intros Hh Htu. setoid_rewrite agreement.
  eapply peutt_interp_handler_rel; eassumption.
Qed.

Lemma interp_ptree_Proper {E F A} (h : ∀ X, E X → ptree F MN X) :
  Proper (W eq ==> W eq) (@interp E MN (ptree F MN) _ _ _ h A).
Proof. intros t u H. exact (interp_ptree_peutt Hmixed Hzero Hlimit h H). Qed.

Lemma interp_ptree_handler_Proper {E F A} :
  Proper (peutt_handler (MF := MF) ==> W eq ==> W eq)
    (λ h t, @interp E MN (ptree F MN) _ _ _ h A t).
Proof. intros h g Hh t u Htu. eapply interp_ptree_handler_rel; eassumption. Qed.

Lemma interp_ptree_handler_polymorphic_Proper {E F} :
  Proper (peutt_handler (MF := MF) ==>
    forall_relation (λ A, @peutt E MN MF FI FC MX FO A A eq ==>
      @peutt F MN MF FI FC MX FO A A eq))
    (@interp E MN (ptree F MN) _ _ _).
Proof. intros h g Hh A t u Htu. eapply interp_ptree_handler_rel; eassumption. Qed.

Theorem interp_ptree_trigger {E F X} (h : ∀ X, E X → ptree F MN X) (e : E X) :
  W eq (interp h (PTree.trigger e)) (h X e).
Proof.
  rewrite agreement.
  apply (peutt_interp_trigger_event Hmixed Hzero Hlimit).
Qed.

Theorem interp_ptree_sample {E F X} (h : ∀ X, E X → ptree F MN X) (mu : MN X) :
  W eq (interp h (PTree.sample mu)) (PTree.sample mu).
Proof.
  rewrite agreement. apply structural.
  apply pstruct_fold. cbn. constructor.
  intro x. apply observe_eq_pstruct. reflexivity.
Qed.

Theorem interp_ptree_identity {E A} (t : ptree E MN A) :
  W eq (interp Handler.id_ t) t.
Proof. rewrite agreement. apply peutt_interp_identity. Qed.

Theorem interp_ptree_compose {E F G A}
    (h : ∀ X, E X → ptree F MN X) (g : ∀ X, F X → ptree G MN X)
    (t : ptree E MN A) :
  W eq (interp g (interp h t)) (interp (Handler.cat h g) t).
Proof.
  transitivity (PTree.interp_tree g (PTree.interp_tree h t)).
  - rewrite (agreement g).
    apply (Unrestricted.peutt_interp Hzero Hlimit). apply agreement.
  - rewrite agreement. apply structural. apply pstruct_interp_compose.
Qed.
End Calculus.
