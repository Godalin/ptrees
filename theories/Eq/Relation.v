(** Structural relations imply behavioral equivalence whenever the frontier
    lifting preserves increasing limits. The proof is backend independent;
    the relational-limit premise is probability mathematics, not a PTree law. *)
Set Warnings "-notation-overridden".
Set Universe Polymorphism.
From Coq.Program Require Import Equality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed RelationalClosure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting
  StableHittingRelation RelationalHitting PTreeKernel PStruct PStrong PEutt.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Relation.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.
Variable Hbind : relational_bind FI.
Variable Hmixed : relational_mixed_bind NI FI MX.
Variable Hzero : relational_zero FO.

Definition pstrong_state {A B} (RR : A -> B -> Prop)
    (s : ptree' E MN A) (t : ptree' E MN B) : Prop :=
  exists u v, s = observe u /\ t = observe v /\ pstrong RR u v.

Lemma pstrong_kernel {A B} (RR : A -> B -> Prop) s t :
  pstrong_state RR s t ->
  sem_lift
    (stable_target_rel (pstrong_state RR) (stable_head_rel RR (pstrong RR)))
    (ptree_primitive_kernel (MF := MF) s)
    (ptree_primitive_kernel (MF := MF) t).
Proof.
  intros [u [v [-> [-> Hs]]]].
  pose proof (pstrong_unfold Hs) as Hstep. dependent destruction Hstep;
    rewrite <- x0, <- x; cbn [ptree_primitive_kernel].
  - apply sem_lift_ret. constructor. exact H.
  - apply sem_lift_ret. exists t1, t2. repeat split; auto.
  - apply sem_lift_ret. constructor. exact H.
  - eapply Hmixed; [exact H|].
    intros a b Hab. apply sem_lift_ret.
    exists (k1 a), (k2 b). repeat split; auto.
Qed.

Theorem ptree_hitting_pstrong {A B} (RR : A -> B -> Prop)
    fuel (t : ptree E MN A) (u : ptree E MN B) :
  pstrong RR t u ->
  sem_lift (stable_head_rel RR (pstrong RR))
    (ptree_hitting_approx (MF := MF) fuel (observe t))
    (ptree_hitting_approx (MF := MF) fuel (observe u)).
Proof.
  intro H. eapply stable_hitting_approx_rel.
  - exact Hbind.
  - exact Hzero.
  - apply pstrong_kernel.
  - exists t, u. repeat split; auto.
Qed.

Context `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}.
Variable Hlimit : relational_lub FO.

Theorem peutt_of_pstrong {A B} (RR : A -> B -> Prop)
    (t : ptree E MN A) (u : ptree E MN B) :
  pstrong RR t u -> peutt (MF := MF) RR t u.
Proof.
  intro Hstrong. eapply peutt_coinduction with (sim := pstrong_state RR).
  - intros s1 s2 [v1 [v2 [-> [-> Hs]]]].
    destruct (stable_hitting_exists (ptree_primitive_kernel (MF := MF))
      (observe v1)) as [out1 Hout1].
    destruct (stable_hitting_exists (ptree_primitive_kernel (MF := MF))
      (observe v2)) as [out2 Hout2].
    eapply stable_hitting_match_of_hitting_lift;
      [exact Hout1|exact Hout2|].
    eapply sem_lift_mono with (R := stable_head_rel RR (pstrong RR)).
    + intros h1 h2 Hhead. dependent destruction Hhead.
      * constructor. exact H.
      * constructor. intro x. exists (k1 x), (k2 x).
        repeat split; try reflexivity. exact (H x).
    + eapply Hlimit.
      * exact (stable_hitting_increasing (ptree_primitive_kernel (MF := MF))
          (observe v1)).
      * exact (stable_hitting_increasing (ptree_primitive_kernel (MF := MF))
          (observe v2)).
      * exact Hout1.
      * exact Hout2.
      * intro n. exact (ptree_hitting_pstrong n Hs).
  - exists t, u. repeat split; try reflexivity. exact Hstrong.
Qed.

Theorem peutt_of_pstruct {A B} (RR : A -> B -> Prop)
    (t : ptree E MN A) (u : ptree E MN B) :
  pstruct RR t u -> peutt (MF := MF) RR t u.
Proof.
  intro H. apply peutt_of_pstrong. apply pstruct_pstrong. exact H.
Qed.
End Relation.
