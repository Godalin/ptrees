(** Universe-unchecked direct MathComp assembly, NOT a safe backend theorem.
    MN = MF = the existing native kernel. No formal completion is used.
    Native probability mathematics remains in Prob/Backend/MathComp with
    universe checking enabled. See docs/MATHCOMP_DIRECT.md and Gate M.
    Native order, omega, diagonal/Fubini and relational bind are checked in
    Gate S. Only their recursive-frontier instantiation belongs to Gate M. *)
Local Unset Universe Checking.
From mathcomp Require Import reals boolp.
From Coinduction Require Import all.
From Coq Require Import Program.Equality.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws
  OrderLaws OmegaLaws BindLaws.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import Shallow UnifiedFrontier PTreeKernel PEutt
  PrimitiveStableHitting StableHittingRelation.
Require Import Lia.
From Coq.Classes Require Morphisms.

Section Direct.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation MX := (MathCompNativeMixedMeasure R).

Definition mathcomp_direct_mixed : MixedMeasure M M := MX.
Definition mathcomp_direct_tree {E A} := ptree E M A.
Definition mathcomp_direct_head {E A} := stable_head E M A.
Definition mathcomp_direct_frontier {E A} := M (@mathcomp_direct_head E A).
Definition mathcomp_direct_kernel {E A} := @ptree_primitive_kernel E M M NI MX A.
Definition mathcomp_direct_hitting {E A} := @ptree_stable_hitting E M M NI MX NO A.

Lemma mathcomp_direct_hitting_exists {E A} (t : @mathcomp_direct_tree E A) :
  exists out, mathcomp_direct_hitting (observe t) out.
Proof. apply ptree_stable_hitting_exists. Qed.

(** Gluing is a mathematical premise, independent of the universe bypass. *)
Context `{G : MathCompCouplingGluing R}.
Local Notation NC := (@MathCompNodeSemanticMeasureCoreLaws R G).
Definition mathcomp_direct_peutt {E A} := @peutt E M M NI NC MX NO A A eq.
Lemma mathcomp_direct_peutt_refl {E A} (t : @mathcomp_direct_tree E A) :
  mathcomp_direct_peutt t t.
Proof. exact (@peutt_refl E M M NI NC MX NO A t). Qed.

Section Bind.
Context {E : Type -> Type}.
Local Notation approx := (@ptree_hitting_approx E M M NI MX NO).

Lemma mathcomp_direct_approx_unfold {A} n (t : ptree' E M A) :
  mathcomp_kernel_eq (approx n t)
    (match t with
     | RetF a => mathcomp_kernel_ret R (FHRet a)
     | VisF _ e k => mathcomp_kernel_ret R (FHVis e k)
     | TauF u => match n with O => mathcomp_kernel_zero R
                            | S m => approx m (observe u) end
     | ProbF _ mu k => match n with O => mathcomp_kernel_zero R
                        | S m => mathcomp_kernel_bind mu (fun x => approx m (observe (k x))) end
     end).
Proof.
  destruct t.
  - apply (ptree_hitting_ret (FI := NI) (MX := MX) (FO := NO)).
  - destruct n; [apply (ptree_hitting_tau_zero (FI := NI) (MX := MX) (FO := NO))|apply (ptree_hitting_tau_succ (FI := NI) (MX := MX) (FO := NO))].
  - apply (ptree_hitting_vis (FI := NI) (MX := MX) (FO := NO)).
  - destruct n.
    + eapply mathcomp_kernel_eq_trans.
      * apply (ptree_hitting_prob_zero (FI := NI) (MX := MX) (FO := NO)).
      * apply mathcomp_native_bind_zero.
    + apply (ptree_hitting_prob_succ (FI := NI) (MX := MX) (FO := NO)).
Qed.

Definition mathcomp_direct_split {A B} n m
    (t : ptree E M A) (k : A -> ptree E M B) :=
  mathcomp_kernel_bind (approx n (observe t))
    (@ptree_head_bind_approx E M M NI MX NO A B m k).

Lemma mathcomp_direct_global_le_diagonal {A B} n
    (t : ptree E M A) (k : A -> ptree E M B) :
  mathcomp_node_le (approx n (observe (PTree.bind t k)))
    (mathcomp_direct_split n n t k).
Proof.
  revert t; induction n as [|n IH]; intro t;
    unfold mathcomp_direct_split; rewrite observe_bind;
    remember (observe t) as ot eqn:Hobs; destruct ot;
    setoid_rewrite mathcomp_direct_approx_unfold; cbn [observe].
  - setoid_rewrite mathcomp_kernel_bind_ret_l. cbn [ptree_head_bind_approx].
    apply mathcomp_native_eq_le, mathcomp_kernel_eq_sym.
    exact (mathcomp_direct_approx_unfold 0 (observe (k r))).
  - apply mathcomp_native_zero_le.
  - setoid_rewrite mathcomp_kernel_bind_ret_l. apply mathcomp_native_le_refl.
  - apply mathcomp_native_zero_le.
  - setoid_rewrite mathcomp_kernel_bind_ret_l. cbn [ptree_head_bind_approx].
    apply mathcomp_native_eq_le, mathcomp_kernel_eq_sym.
    exact (mathcomp_direct_approx_unfold (S n) (observe (k r))).
  - eapply mathcomp_native_le_trans; [apply IH|].
    apply mathcomp_native_bind_le_k; intro head.
    apply (ptree_head_bind_approx_mono (FI := NI) (MX := MX) (FO := NO)); lia.
  - setoid_rewrite mathcomp_kernel_bind_ret_l. apply mathcomp_native_le_refl.
  - eapply mathcomp_native_le_eq_r; [apply mathcomp_kernel_bind_assoc|].
    apply mathcomp_native_bind_le_k; intro x.
    eapply mathcomp_native_le_trans; [apply IH|].
    apply mathcomp_native_bind_le_k; intro head.
    apply (ptree_head_bind_approx_mono (FI := NI) (MX := MX) (FO := NO)); lia.
Qed.
Lemma mathcomp_direct_split_le_global {A B} n m
    (t : ptree E M A) (k : A -> ptree E M B) :
  mathcomp_node_le (mathcomp_direct_split n m t k)
    (approx (n + m) (observe (PTree.bind t k))).
Proof.
  revert t; induction n as [|n IH]; intro t;
    unfold mathcomp_direct_split; rewrite observe_bind;
    remember (observe t) as ot eqn:Hobs; destruct ot;
    setoid_rewrite mathcomp_direct_approx_unfold; cbn [observe Nat.add].
  - setoid_rewrite mathcomp_kernel_bind_ret_l. cbn [ptree_head_bind_approx].
    apply mathcomp_native_eq_le. exact (mathcomp_direct_approx_unfold m (observe (k r))).
  - eapply mathcomp_native_le_eq_l; [apply mathcomp_native_bind_zero_left|].
    apply mathcomp_native_zero_le.
  - setoid_rewrite mathcomp_kernel_bind_ret_l. apply mathcomp_native_le_refl.
  - eapply mathcomp_native_le_eq_l; [apply mathcomp_native_bind_zero_left|].
    apply mathcomp_native_zero_le.
  - setoid_rewrite mathcomp_kernel_bind_ret_l. cbn [ptree_head_bind_approx].
    eapply mathcomp_native_le_eq_r.
    + apply mathcomp_kernel_eq_sym. exact (mathcomp_direct_approx_unfold (S n + m) (observe (k r))).
    + apply (ptree_hitting_mono (FI := NI) (MX := MX) (FO := NO)); lia.
  - apply IH.
  - setoid_rewrite mathcomp_kernel_bind_ret_l. apply mathcomp_native_le_refl.
  - eapply mathcomp_native_le_eq_l; [apply mathcomp_kernel_bind_assoc|].
    apply mathcomp_native_bind_le_k; intro x; apply IH.
Qed.

Theorem mathcomp_direct_bind_cofinal {A B}
    (t : ptree E M A) (k : A -> ptree E M B) :
  @ptree_bind_cofinal E M M NI MX NO A B t k.
Proof.
  intro out; apply mathcomp_native_lub_cofinal.
  - intro n; exists n; apply mathcomp_direct_global_le_diagonal.
  - intro n; exists (n + n); apply mathcomp_direct_split_le_global.
Qed.

(** Reuse the generic bind candidate, but select native hitting witnesses
    with MathComp's existing [cid], not ClassicalChoice's extra axioms. *)
Lemma mathcomp_direct_front_choice {A B} (k : A -> ptree E M B) :
  exists front : A -> M (stable_head E M B),
    forall a, stable_hitting
      (@ptree_primitive_kernel E M M NI MX B) (observe (k a)) (front a).
Proof.
  exists (fun a => proj1_sig (cid (mathcomp_direct_hitting_exists (k a)))).
  intro a; exact (proj2_sig (cid (mathcomp_direct_hitting_exists (k a)))).
Qed.

Lemma mathcomp_direct_bind_postfixed A :
  forall s1 s2, bind_bisim_candidate (FI := NI) (MX := MX) (FO := NO)
    (A := A) s1 s2 -> stable_hitting_match
      (@ptree_primitive_kernel E M M NI MX A)
      (@ptree_primitive_kernel E M M NI MX A)
      (@ptree_stable_head_rel E M A A eq)
      (bind_bisim_candidate (A := A)) s1 s2.
Proof.
  intros s1 s2 [Hknown|Hbind].
  - apply stable_hitting_bisim_unfold in Hknown.
    unfold stable_hitting_match in Hknown |- *.
    destruct Hknown as [Hforward Hbackward]. split.
    + intros out1 Hhit1. destruct (Hforward out1 Hhit1)
        as [out2 [Hhit2 Hlift]]. exists out2. split; [exact Hhit2|].
      eapply sem_lift_mono; [|exact Hlift].
      apply ptree_stable_head_rel_mono.
      intros x1 x2 Hrel. left. exact Hrel.
    + intros out2 Hhit2. destruct (Hbackward out2 Hhit2)
        as [out1 [Hhit1 Hlift]]. exists out1. split; [exact Hhit1|].
      eapply sem_lift_mono; [|exact Hlift].
      apply ptree_stable_head_rel_mono.
      intros x1 x2 Hrel. left. exact Hrel.
  - destruct Hbind as
      [R1 [R2 [RR [t1 [t2 [k1 [k2 [-> [-> [Hsource Hk]]]]]]]]]].
    apply peutt_unfold in Hsource.
    unfold stable_hitting_match in Hsource |- *.
    destruct Hsource as [Hforward Hbackward]. split.
    + intros hs1 Hhit1.
      destruct (stable_hitting_exists
        (@ptree_primitive_kernel E M M NI MX R1) (observe t1))
        as [source1 Hsource1].
      destruct (Hforward source1 Hsource1)
        as [source2 [Hsource2 Hlift]].
      destruct (mathcomp_direct_front_choice k1) as [front1 Hfront1].
      destruct (mathcomp_direct_front_choice k2) as [front2 Hfront2].
      assert (Hbound1 : stable_hitting
        (@ptree_primitive_kernel E M M NI MX A)
        (observe (PTree.bind t1 k1))
        (sem_bind source1 (stable_head_bind_front k1 front1))).
      { eapply stable_hitting_bind;
          [apply mathcomp_direct_bind_cofinal|exact Hsource1|exact Hfront1]. }
      assert (Hbound2 : stable_hitting
        (@ptree_primitive_kernel E M M NI MX A)
        (observe (PTree.bind t2 k2))
        (sem_bind source2 (stable_head_bind_front k2 front2))).
      { eapply stable_hitting_bind;
          [apply mathcomp_direct_bind_cofinal|exact Hsource2|exact Hfront2]. }
      exists (sem_bind source2 (stable_head_bind_front k2 front2)). split.
      * exact Hbound2.
      * eapply sem_lift_proper_l.
        -- eapply stable_hitting_unique; [exact Hbound1|exact Hhit1].
        -- eapply sem_lift_bind; [exact Hlift|].
        intros h1 h2 Hhead. dependent destruction Hhead.
        -- eapply sem_lift_mono.
           ++ apply ptree_stable_head_rel_mono.
              intros x1 x2 Hrel. left. exact Hrel.
           ++ apply peutt_state_hitting_lift
                with (s1 := observe (k1 r1)) (s2 := observe (k2 r2));
                [exact (Hk r1 r2 H)|exact (Hfront1 r1)|exact (Hfront2 r2)].
        -- apply sem_lift_ret. constructor. intro x. right.
           exists R1, R2, RR, (k0 x), (k3 x), k1, k2.
           repeat split; try reflexivity.
           ++ exact (H x).
           ++ exact Hk.
    + intros hs2 Hhit2.
      destruct (stable_hitting_exists
        (@ptree_primitive_kernel E M M NI MX R2) (observe t2))
        as [source2 Hsource2].
      destruct (Hbackward source2 Hsource2)
        as [source1 [Hsource1 Hlift]].
      destruct (mathcomp_direct_front_choice k1) as [front1 Hfront1].
      destruct (mathcomp_direct_front_choice k2) as [front2 Hfront2].
      assert (Hbound1 : stable_hitting
        (@ptree_primitive_kernel E M M NI MX A)
        (observe (PTree.bind t1 k1))
        (sem_bind source1 (stable_head_bind_front k1 front1))).
      { eapply stable_hitting_bind;
          [apply mathcomp_direct_bind_cofinal|exact Hsource1|exact Hfront1]. }
      assert (Hbound2 : stable_hitting
        (@ptree_primitive_kernel E M M NI MX A)
        (observe (PTree.bind t2 k2))
        (sem_bind source2 (stable_head_bind_front k2 front2))).
      { eapply stable_hitting_bind;
          [apply mathcomp_direct_bind_cofinal|exact Hsource2|exact Hfront2]. }
      exists (sem_bind source1 (stable_head_bind_front k1 front1)). split.
      * exact Hbound1.
      * eapply sem_lift_proper_r.
        -- eapply stable_hitting_unique; [exact Hbound2|exact Hhit2].
        -- eapply sem_lift_bind; [exact Hlift|].
        intros h1 h2 Hhead. dependent destruction Hhead.
        -- eapply sem_lift_mono.
           ++ apply ptree_stable_head_rel_mono.
              intros x1 x2 Hrel. left. exact Hrel.
           ++ apply peutt_state_hitting_lift
                with (s1 := observe (k1 r1)) (s2 := observe (k2 r2));
                [exact (Hk r1 r2 H)|exact (Hfront1 r1)|exact (Hfront2 r2)].
        -- apply sem_lift_ret. constructor. intro x. right.
           exists R1, R2, RR, (k0 x), (k3 x), k1, k2.
           repeat split; try reflexivity.
           ++ exact (H x).
           ++ exact Hk.
Qed.

(** Eventful bind congruence, using the proved native scheduling bounds. *)

Theorem mathcomp_direct_peutt_bind {A B C} (RR : A -> B -> Prop)
    (t : ptree E M A) (u : ptree E M B)
    (k : A -> ptree E M C) (h : B -> ptree E M C) :
  @peutt E M M NI NC MX NO A B RR t u ->
  (forall x y, RR x y -> mathcomp_direct_peutt (k x) (h y)) ->
  mathcomp_direct_peutt (PTree.bind t k) (PTree.bind u h).
Proof.
  intros Htu Hkh.
  unfold mathcomp_direct_peutt, peutt, peutt_state, stable_hitting_bisim.
  eapply (@leq_gfp _ _ (fstable_hitting_bisim
    (@ptree_primitive_kernel E M M NI MX C)
    (@ptree_primitive_kernel E M M NI MX C)
    (@ptree_stable_head_rel_mono E M C C eq))
    (bind_bisim_candidate (A := C))).
  - exact (mathcomp_direct_bind_postfixed C).
  - right; exists A, B, RR, t, u, k, h.
    repeat split; try reflexivity; assumption.
Qed.
End Bind.
End Direct.
