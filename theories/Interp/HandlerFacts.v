(** Handler algebra modulo whole-continuation behavioral equality.
    Probability assumptions stay explicit; no handler-law capability is added. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Handler.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder RelationalClosure.
From PTree.Eq Require Import Shallow PStruct PEutt Relation Algebra
  UnifiedFrontier PrimitiveStableHitting PTreeKernel BindScheduling StableHittingRelation.
From PTree.Interp Require Import Kernel Scheduling Structural HandlerRelation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FiniteIdentity.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}.
Local Notation equiv := (@BindScheduling.equiv MF FI FO).
#[local] Existing Instance BindScheduling.equiv_equivalence.
#[local] Existing Instance BindScheduling.le_equiv_Proper.
#[local] Existing Instance BindScheduling.bind_equiv_Proper.
#[local] Instance mixed_equiv A B (mu : MN A) :
  Proper (pointwise_relation A (@equiv B) ==> @equiv B)
    (@mixed_bind MN MF MX A B mu).
Proof. apply BindScheduling.mixed_equiv_Proper. exact (@mixed_bind_le_k MN MF FI MX FO MO). Qed.
Local Notation hit_unfold := (@BindScheduling.hitting_unfold E MN MF FI MX FO Ord
  (@sem_bind_ret_order MF FI FO BO) (@mixed_bind_assoc_order MN MF FI MX FO MO)
  (@mixed_bind_le_k MN MF FI MX FO MO)).
Local Lemma ret_equiv A B (x : A) (k : A -> MF B) :
  equiv (sem_bind (sem_ret x) k) (k x).
Proof. apply sem_bind_ret_order. Qed.
Local Lemma zero_equiv A B (k : A -> MF B) :
  equiv (sem_bind sem_zero k) sem_zero.
Proof. split; [apply sem_bind_zero_order|apply sem_zero_le]. Qed.
Local Lemma mixed_assoc_equiv A B C (mu : MN A) (k : A -> MF B) (h : B -> MF C) :
  equiv (sem_bind (mixed_bind mu k) h) (mixed_bind mu (fun x => sem_bind (k x) h)).
Proof. apply mixed_bind_assoc_order. Qed.

(** Right unit is derived only for finite, native-generated frontiers. *)
Lemma handler_finite_front_ret {A} n (t : ptree' E MN A) :
  equiv (sem_bind (ptree_hitting_approx (MF := MF) n t) sem_ret)
    (ptree_hitting_approx (MF := MF) n t).
Proof.
  revert t. induction n as [|n IH]; intros [a|u|X e k|X mu k];
    setoid_rewrite hit_unfold; cbn [observe].
  - apply ret_equiv.
  - apply zero_equiv.
  - apply ret_equiv.
  - setoid_rewrite mixed_assoc_equiv. apply mixed_equiv. intro x. apply zero_equiv.
  - apply ret_equiv.
  - apply IH.
  - apply ret_equiv.
  - setoid_rewrite mixed_assoc_equiv. apply mixed_equiv. intro x. apply IH.
Qed.

Context `{FC : @SemanticMeasureCoreLaws MF FI}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}.

Lemma handler_complete_front_ret {A} (t : ptree' E MN A) mu :
  ptree_stable_hitting (MF := MF) t mu ->
  sem_eq (sem_bind mu sem_ret) mu.
Proof.
  intro H. eapply sem_lub_unique.
  - apply sem_bind_lub; [apply ptree_hitting_increasing|exact H].
  - assert (Hiff : sem_lub (fun n => ptree_hitting_approx (MF := MF) n t) mu <->
        sem_lub (fun n => sem_bind (ptree_hitting_approx (MF := MF) n t) sem_ret) mu).
    { apply sem_lub_cofinal.
      - apply ptree_hitting_increasing.
      - intro n. apply sem_bind_le_mu. apply ptree_hitting_increasing.
      - intro n. exists n. apply (proj2 (handler_finite_front_ret n t)).
      - intro n. exists n. apply (proj1 (handler_finite_front_ret n t)). }
    exact (proj1 Hiff H).
Qed.
End FiniteIdentity.

Section Identity.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}.

Definition handler_identity_head {A} (h : stable_head E MN A) : stable_head E MN A :=
  match h with
  | FHRet a => FHRet a
  | @FHVis _ _ _ X e k => FHVis e (fun x =>
      PTree.bind (Ret x) (fun y => PTree.interp Handler.id_ (k y)))
  end.

Lemma handler_identity_head_hitting {A} (h : stable_head E MN A) :
  ptree_stable_hitting (MF := MF)
    (observe (ptree_interp_head_tree Handler.id_ h))
    (sem_ret (handler_identity_head h)).
Proof.
  destruct h as [a|X e k].
  - apply ptree_stable_hitting_ret.
  - apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    rewrite observe_bind. apply ptree_stable_hitting_vis.
Qed.

Theorem peutt_interp_identity {A} (t : ptree E MN A) :
  peutt (MF := MF) eq (PTree.interp Handler.id_ t) t.
Proof.
  eapply peutt_coinduction with (sim := fun s u =>
    exists v, s = observe (PTree.interp Handler.id_ v) /\ u = observe v).
  - intros s u [v [-> ->]].
    destruct (ptree_stable_hitting_exists (MF := MF) (observe v)) as [mu Hmu].
    eapply stable_hitting_match_of_hitting_lift with
      (out1 := sem_bind mu (fun h => sem_ret (handler_identity_head h))) (out2 := mu).
    + eapply ptree_stable_hitting_interp.
      * apply Scheduling.ptree_interp_cofinal_all.
      * exact Hmu.
      * apply handler_identity_head_hitting.
    + exact Hmu.
    + eapply sem_lift_proper_r.
      * exact (handler_complete_front_ret Hmu).
      * eapply sem_lift_bind with (R := eq).
        -- apply sem_lift_refl. intros h. reflexivity.
        -- intros h h' ->. apply sem_lift_ret. destruct h' as [a|X e k].
           ++ constructor. reflexivity.
           ++ constructor. intro x. rewrite observe_bind. cbn.
              exists (k x). split; reflexivity.
  - exists t. split; reflexivity.
Qed.
End Identity.

Section Combinations.
Context {MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.

Lemma handler_case_congr {E F G}
    (h1 h2 : Handler MN E G) (g1 g2 : Handler MN F G) :
  peutt_handler (MF := MF) h1 h2 -> peutt_handler (MF := MF) g1 g2 ->
  peutt_handler (MF := MF) (Handler.case_ h1 g1) (Handler.case_ h2 g2).
Proof. intros H G' X [e|e]; [apply H|apply G']. Qed.

Lemma handler_case_eta {E F G} (h : Handler MN (E +' F) G) :
  peutt_handler (MF := MF)
    (Handler.case_ (fun X e => h X (inl1 e)) (fun X e => h X (inr1 e))) h.
Proof. intros X [e|e]; apply peutt_refl. Qed.

Lemma handler_empty_unique {F} (h : Handler MN void1 F) :
  peutt_handler (MF := MF) h Handler.empty.
Proof. intros X e. destruct e. Qed.

Lemma handler_case_cat {E F G H} (h : Handler MN E G)
    (g : Handler MN F G) (k : Handler MN G H) :
  peutt_handler (MF := MF) (Handler.cat (Handler.case_ h g) k)
    (Handler.case_ (Handler.cat h k) (Handler.cat g k)).
Proof. intros X [e|e]; apply peutt_refl. Qed.
End Combinations.

Section Category.
Context {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
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

Local Notation structural := (Relation.peutt_of_pstruct
  (relational_bind_of_laws FB) Hmixed Hzero Hlimit).

Theorem peutt_interp_trigger_event {E F X} (h : Handler MN E F) (e : E X) :
  peutt (MF := MF) eq (PTree.interp h (PTree.trigger e)) (h X e).
Proof.
  eapply peutt_trans with (y := Tau (h X e)); [|apply peutt_tau_l].
  apply structural.
  apply pstruct_fold. rewrite observe_interp. cbn.
  constructor.
  eapply pstruct_trans with (y := PTree.bind (h X e) (fun x => Ret x)).
  - eapply pstruct_bind with (RA := eq) (RB := eq).
    + intros x y ->. apply observe_eq_pstruct. reflexivity.
    + apply pstruct_refl.
  - apply pstruct_bind_ret_r.
Qed.

Theorem handler_cat_congr {E F G}
    (h1 h2 : Handler MN E F) (g1 g2 : Handler MN F G) :
  peutt_handler (MF := MF) h1 h2 -> peutt_handler (MF := MF) g1 g2 ->
  peutt_handler (MF := MF) (Handler.cat h1 g1) (Handler.cat h2 g2).
Proof.
  intros H G' X e. unfold Handler.cat.
  exact (peutt_interp_handler_rel Hzero Hlimit G' (H X e)).
Qed.

Theorem handler_cat_id_l {E F} (h : Handler MN E F) :
  peutt_handler (MF := MF) (Handler.cat Handler.id_ h) h.
Proof. intros X e. apply peutt_interp_trigger_event. Qed.

Theorem handler_cat_id_r {E F} (h : Handler MN E F) :
  peutt_handler (MF := MF) (Handler.cat h Handler.id_) h.
Proof. intros X e. apply peutt_interp_identity. Qed.

Theorem handler_cat_assoc {E F G H}
    (h : Handler MN E F) (g : Handler MN F G) (k : Handler MN G H) :
  peutt_handler (MF := MF)
    (Handler.cat (Handler.cat h g) k) (Handler.cat h (Handler.cat g k)).
Proof. intros X e. apply structural. apply pstruct_interp_compose. Qed.

Theorem handler_case_inl {E F G}
    (h : Handler MN E G) (g : Handler MN F G) :
  peutt_handler (MF := MF) (Handler.cat Handler.inl_ (Handler.case_ h g)) h.
Proof. intros X e. exact (peutt_interp_trigger_event (Handler.case_ h g) (inl1 e)). Qed.

Theorem handler_case_inr {E F G}
    (h : Handler MN E G) (g : Handler MN F G) :
  peutt_handler (MF := MF) (Handler.cat Handler.inr_ (Handler.case_ h g)) g.
Proof. intros X e. exact (peutt_interp_trigger_event (Handler.case_ h g) (inr1 e)). Qed.

Theorem handler_bimap_congr {E1 E2 F1 F2}
    (h1 h2 : Handler MN E1 F1) (g1 g2 : Handler MN E2 F2) :
  peutt_handler (MF := MF) h1 h2 -> peutt_handler (MF := MF) g1 g2 ->
  peutt_handler (MF := MF) (Handler.bimap h1 g1) (Handler.bimap h2 g2).
Proof.
  intros H G. apply handler_case_congr;
    apply handler_cat_congr; try assumption; intros X e; apply peutt_refl.
Qed.

Theorem handler_case_eta_cat {E F G} (h : Handler MN (E +' F) G) :
  peutt_handler (MF := MF)
    (Handler.case_ (Handler.cat Handler.inl_ h) (Handler.cat Handler.inr_ h)) h.
Proof. intros X [e|e]; apply peutt_interp_trigger_event. Qed.

Lemma handler_cat_Proper {E F G} :
  Proper (peutt_handler (MF := MF) ==> peutt_handler (MF := MF) ==>
    peutt_handler (MF := MF)) (@Handler.cat MN E F G).
Proof. intros h1 h2 H g1 g2 G'. apply handler_cat_congr; assumption. Qed.
End Category.
