(** Early exit is a stable-head projection, not a void-valued returning
    handler. Its behavioral proof therefore needs no collapsed-event loop. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms RelationClasses.
From ITree.Events Require Import Exception.
From ITree.Basics Require Import Basics.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder RelationalClosure.
From PTree.Eq Require Import Shallow PStruct UnifiedFrontier PrimitiveStableHitting
  PTreeKernel PEutt StableHittingRelation BindScheduling.
From PTree.Interp Require Import Exception.
Set Implicit Arguments.
Unset Strict Implicit.

Definition exception_head {Err E MN A} (h : stable_head (exceptE Err +' E) MN A) :
    stable_head E MN (Err+A) :=
  match h with
  | FHRet a => FHRet (inr a)
  | @FHVis _ _ _ X e k => match e with
      | inl1 ex => FHRet (inl (exception_value ex))
      | inr1 fe => FHVis fe (fun x => run_exception (k x)) end
  end.

Lemma run_exception_ret {Err E MN A} (a : A) :
  pstruct eq (@run_exception Err E MN A (Ret a)) (Ret (inr a)).
Proof. apply observe_eq_pstruct. reflexivity. Qed.
Lemma run_exception_throw {Err E MN A} (e : Err) :
  pstruct eq (@run_exception Err E MN A (Vis (inl1 (Throw e)) (fun v : void => match v with end)))
    (Ret (inl e)).
Proof. apply observe_eq_pstruct. reflexivity. Qed.
Lemma run_exception_prob {Err E MN A X} (mu : MN X) (k : X -> ptree (exceptE Err +' E) MN A) :
  pstruct eq (run_exception (Prob mu k)) (Prob mu (fun x => run_exception (k x))).
Proof. apply observe_eq_pstruct. reflexivity. Qed.

Section Approximation.
Context {Err : Type} {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}.
Local Notation equiv := (@BindScheduling.equiv MF FI FO).
#[local] Existing Instance BindScheduling.equiv_equivalence.
#[local] Existing Instance BindScheduling.le_equiv_Proper.
#[local] Existing Instance BindScheduling.bind_equiv_Proper.
#[local] Instance mixed_equiv A B (mu : MN A) :
  Proper (pointwise_relation A (@equiv B) ==> @equiv B) (@mixed_bind MN MF MX A B mu).
Proof. apply BindScheduling.mixed_equiv_Proper. exact (@mixed_bind_le_k MN MF FI MX FO MO). Qed.
Local Notation hit_unfold := (fun G => @BindScheduling.hitting_unfold G MN MF FI MX FO Ord
  (@sem_bind_ret_order MF FI FO BO) (@mixed_bind_assoc_order MN MF FI MX FO MO)
  (@mixed_bind_le_k MN MF FI MX FO MO)).
Local Lemma ret_equiv A B (x : A) (k : A -> MF B) : equiv (sem_bind (sem_ret x) k) (k x).
Proof. apply sem_bind_ret_order. Qed.
Local Lemma zero_equiv A B (k : A -> MF B) : equiv (sem_bind sem_zero k) sem_zero.
Proof. split; [apply sem_bind_zero_order|apply sem_zero_le]. Qed.
Local Lemma mixed_assoc A B C (mu : MN A) (k : A -> MF B) (h : B -> MF C) :
  equiv (sem_bind (mixed_bind mu k) h) (mixed_bind mu (fun x => sem_bind (k x) h)).
Proof. apply mixed_bind_assoc_order. Qed.

Lemma exception_hitting_approx {A} n (t : ptree (exceptE Err +' E) MN A) :
  equiv (ptree_hitting_approx (MF := MF) n (observe (run_exception t)))
    (sem_bind (ptree_hitting_approx (MF := MF) n (observe t)) (fun h => sem_ret (exception_head h))).
Proof.
  revert t. induction n as [|n IH]; intro t; rewrite observe_run_exception;
    setoid_rewrite (hit_unfold (exceptE Err +' E));
    destruct (observe t) as [a|u|X e k|X mu k].
  - setoid_rewrite (hit_unfold E). setoid_rewrite ret_equiv. reflexivity.
  - setoid_rewrite (hit_unfold E). setoid_rewrite zero_equiv. reflexivity.
  - setoid_rewrite ret_equiv. destruct e; setoid_rewrite (hit_unfold E); reflexivity.
  - setoid_rewrite (hit_unfold E). setoid_rewrite mixed_assoc. apply mixed_equiv. intro x.
    setoid_rewrite zero_equiv. reflexivity.
  - setoid_rewrite (hit_unfold E). setoid_rewrite ret_equiv. reflexivity.
  - setoid_rewrite (hit_unfold E). apply IH.
  - setoid_rewrite ret_equiv. destruct e; setoid_rewrite (hit_unfold E); reflexivity.
  - setoid_rewrite (hit_unfold E). setoid_rewrite mixed_assoc. apply mixed_equiv. intro x. apply IH.
Qed.

Context `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}.
Theorem exception_hitting {A} (t : ptree (exceptE Err +' E) MN A) front :
  ptree_stable_hitting (MF := MF) (observe t) front ->
  ptree_stable_hitting (MF := MF) (observe (run_exception t))
    (sem_bind front (fun h => sem_ret (exception_head h))).
Proof.
  intro H. assert (Hmap : sem_lub
    (fun n => sem_bind (ptree_hitting_approx (MF := MF) n (observe t)) (fun h => sem_ret (exception_head h)))
    (sem_bind front (fun h => sem_ret (exception_head h)))).
  { apply sem_bind_lub; [apply ptree_hitting_increasing|exact H]. }
  assert (HC : sem_lub
    (fun n => sem_bind (ptree_hitting_approx (MF := MF) n (observe t)) (fun h => sem_ret (exception_head h)))
    (sem_bind front (fun h => sem_ret (exception_head h))) <->
    ptree_stable_hitting (MF := MF) (observe (run_exception t))
      (sem_bind front (fun h => sem_ret (exception_head h)))).
  { unfold ptree_stable_hitting, stable_hitting. apply sem_lub_cofinal.
    - intro n. apply sem_bind_le_mu. apply ptree_hitting_increasing.
    - apply ptree_hitting_increasing.
    - intro n. exists n. apply (proj2 (exception_hitting_approx n t)).
    - intro n. exists n. apply (proj1 (exception_hitting_approx n t)). }
  exact (proj1 HC Hmap).
Qed.

Context `{FC : @SemanticMeasureCoreLaws MF FI}.
Variable Hbind : relational_bind FI.
Context {A B : Type} (RR : A -> B -> Prop).
Local Notation source_rel := (@peutt (exceptE Err +' E) MN MF FI FC MX FO A B RR).
Definition exception_candidate (v : ptree' E MN (Err+A)) (w : ptree' E MN (Err+B)) : Prop :=
  exists t u, v = observe (run_exception t) /\ w = observe (run_exception u) /\ source_rel t u.

Theorem run_exception_peutt (t : ptree (exceptE Err +' E) MN A) (u : ptree (exceptE Err +' E) MN B) :
  source_rel t u ->
  @peutt E MN MF FI FC MX FO (Err+A) (Err+B) (exception_result_rel RR) (run_exception t) (run_exception u).
Proof.
  intro Htu. eapply peutt_coinduction with (sim := exception_candidate).
  - intros v w [t0 [u0 [-> [-> Hsource]]]].
    destruct (stable_hitting_exists (ptree_primitive_kernel (MF := MF)) (observe t0)) as [mu Hmu].
    destruct (stable_hitting_exists (ptree_primitive_kernel (MF := MF)) (observe u0)) as [nu Hnu].
    eapply stable_hitting_match_of_hitting_lift.
    + exact (exception_hitting Hmu).
    + exact (exception_hitting Hnu).
    + eapply Hbind.
      * eapply peutt_state_hitting_lift; [exact Hsource|exact Hmu|exact Hnu].
      * intros h1 h2 Hh. apply sem_lift_ret. inversion Hh; subst; cbn [exception_head].
        -- constructor. exact H.
        -- destruct e as [ex|fe]; cbn [exception_head].
           ++ constructor. reflexivity.
           ++ constructor. intro x. exists (k1 x), (k2 x). repeat split; try reflexivity. apply H.
  - exists t,u. repeat split; try reflexivity. exact Htu.
Qed.
End Approximation.
