Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import List Arith.PeanoNat FunctionalExtensionality Lia
  Logic.ClassicalChoice Program.Equality Morphisms.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import Shallow UnifiedFrontier PrimitiveStableHitting
  PStruct PStrong PFinite PEutt PTreeKernel.
From PTree.Eq.FreeOmega Require Import Base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FreeOmegaRelation.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).

Lemma ptree_hitting_pstruct {A B}
    (RR : A -> B -> Prop) fuel (t1 : ptree E MN A) (t2 : ptree E MN B) :
  pstruct RR t1 t2 ->
  free_omega_lift (frontier_head_rel RR (pstruct RR))
    (ptree_hitting_approx (MF := MF) fuel (observe t1))
    (ptree_hitting_approx (MF := MF) fuel (observe t2)).
Proof.
  revert t1 t2. induction fuel as [|fuel IH]; intros t1 t2 Hstruct.
  all: pose proof (pstruct_unfold Hstruct) as Hstep;
    dependent destruction Hstep.
  - rewrite <- x0, <- x. constructor. constructor. exact H.
  - rewrite <- x0, <- x.
    cbn [ptree_hitting_approx ptree_primitive_kernel]. constructor.
  - rewrite <- x0, <- x. constructor. constructor. exact H.
  - rewrite <- x0, <- x.
    change (free_omega_lift
      (@frontier_head_rel E MN A B RR (@pstruct E MN A B RR))
      (FOSample mu (fun _ => FOZero))
      (FOSample mu (fun _ => FOZero))).
    eapply FOLSample with (S := eq).
    + apply sem_lift_refl. intros z. reflexivity.
    + intros z z' ->. constructor.
  - rewrite <- x0, <- x. constructor. constructor. exact H.
  - rewrite <- x0, <- x.
    cbn [ptree_hitting_approx ptree_primitive_kernel].
    exact (IH _ _ H).
  - rewrite <- x0, <- x. constructor. constructor. exact H.
  - rewrite <- x0, <- x.
    change (free_omega_lift
      (@frontier_head_rel E MN A B RR (@pstruct E MN A B RR))
      (FOSample mu (fun z => ptree_hitting_approx (MF := MF)
        fuel (observe (k1 z))))
      (FOSample mu (fun z => ptree_hitting_approx (MF := MF)
        fuel (observe (k2 z))))).
    eapply FOLSample with (S := eq).
    + apply sem_lift_refl. intros z. reflexivity.
    + intros z z' ->. apply IH. exact (H z').
Qed.

(** State-level closure used to interpret syntax-sensitive structural
    equivalence inside the canonical stable-hitting coinduction principle. *)
Definition pstruct_state {A B} (RR : A -> B -> Prop)
    (s1 : ptree' E MN A) (s2 : ptree' E MN B) : Prop :=
  exists (t1 : ptree E MN A) (t2 : ptree E MN B),
    s1 = observe t1 /\ s2 = observe t2 /\ pstruct RR t1 t2.

(** Structural probabilistic bisimulation is sound for the canonical weak
    equivalence.  Pointwise structural couplings of all finite hitting
    approximants are closed by the FreeOmega limit constructor; visible
    continuations re-enter the coinduction candidate. *)
Theorem peutt_of_pstruct {A B}
    (RR : A -> B -> Prop) (t1 : ptree E MN A) (t2 : ptree E MN B) :
  pstruct RR t1 t2 ->
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A B RR t1 t2.
Proof.
  intro Hstruct. eapply peutt_coinduction with
    (sim := pstruct_state RR).
  - intros s1 s2 [u1 [u2 [-> [-> Hs]]]].
    destruct (stable_hitting_exists
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure A) (observe u1)) as [out1 Hout1].
    destruct (stable_hitting_exists
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure B) (observe u2)) as [out2 Hout2].
    eapply stable_hitting_match_of_hitting_lift;
      [exact Hout1|exact Hout2|].
    eapply FOQLMono.
    + unfold stable_hitting in Hout1, Hout2.
      cbn in Hout1, Hout2.
      eapply FOQLComp with (T := eq)
        (U := frontier_head_rel RR (pstruct RR))
        (mid := FOLub (fun fuel => ptree_hitting_approx
          (MF := MF) fuel (observe u1))).
      * exact Hout1.
      * eapply FOQLComp with
          (T := frontier_head_rel RR (pstruct RR))
          (U := eq)
          (mid := FOLub (fun fuel => ptree_hitting_approx
            (MF := MF) fuel (observe u2))).
        -- apply FOQLLub. intro fuel.
           apply FOQLStructural.
           exact (ptree_hitting_pstruct
             (RR := RR) fuel Hs).
        -- apply FOQLSym. eapply FOQLMono; [exact Hout2|].
           intros x y ->. reflexivity.
        -- intros x z [y [Hxy ->]]. exact Hxy.
      * intros x z [y [-> Hyz]]. exact Hyz.
    + intros h1 h2 Hhead. dependent destruction Hhead.
      * constructor. exact H.
      * constructor. intro x. exists (k1 x), (k2 x).
        repeat split; try reflexivity. exact (H x).
  - exists t1, t2. repeat split; try reflexivity. exact Hstruct.
Qed.

(** Strong lockstep coupling is also sound for the canonical weak endpoint.
    Unlike [pstruct], probability nodes may use distinct source measures;
    their coupling is threaded through every finite hitting approximant and
    then closed by the FreeOmega limit. *)
Lemma ptree_hitting_pstrong {A B}
    (RR : A -> B -> Prop) fuel (t1 : ptree E MN A) (t2 : ptree E MN B) :
  pstrong RR t1 t2 ->
  free_omega_lift (frontier_head_rel RR (pstrong RR))
    (ptree_hitting_approx (MF := MF) fuel (observe t1))
    (ptree_hitting_approx (MF := MF) fuel (observe t2)).
Proof.
  revert t1 t2. induction fuel as [|fuel IH]; intros t1 t2 Hstrong.
  all: pose proof (pstrong_unfold Hstrong) as Hstep;
    dependent destruction Hstep.
  - rewrite <- x0, <- x. constructor. constructor. exact H.
  - rewrite <- x0, <- x.
    cbn [ptree_hitting_approx ptree_primitive_kernel]. constructor.
  - rewrite <- x0, <- x. constructor. constructor. exact H.
  - rewrite <- x0, <- x.
    change (free_omega_lift
      (@frontier_head_rel E MN A B RR (@pstrong E MN NI NC A B RR))
      (FOSample mu (fun _ => FOZero))
      (FOSample nu (fun _ => FOZero))).
    eapply FOLSample with
      (S := fun a b => pstrong RR (k1 a) (k2 b)).
    + exact H.
    + intros a b Hab. constructor.
  - rewrite <- x0, <- x. constructor. constructor. exact H.
  - rewrite <- x0, <- x.
    cbn [ptree_hitting_approx ptree_primitive_kernel].
    exact (IH _ _ H).
  - rewrite <- x0, <- x. constructor. constructor. exact H.
  - rewrite <- x0, <- x.
    change (free_omega_lift
      (@frontier_head_rel E MN A B RR (@pstrong E MN NI NC A B RR))
      (FOSample mu (fun a => ptree_hitting_approx (MF := MF)
        fuel (observe (k1 a))))
      (FOSample nu (fun b => ptree_hitting_approx (MF := MF)
        fuel (observe (k2 b))))).
    eapply FOLSample with
      (S := fun a b => pstrong RR (k1 a) (k2 b)).
    + exact H.
    + intros a b Hab. exact (IH _ _ Hab).
Qed.

Definition pstrong_state {A B} (RR : A -> B -> Prop)
    (s1 : ptree' E MN A) (s2 : ptree' E MN B) : Prop :=
  exists (t1 : ptree E MN A) (t2 : ptree E MN B),
    s1 = observe t1 /\ s2 = observe t2 /\ pstrong RR t1 t2.

Theorem peutt_of_pstrong {A B}
    (RR : A -> B -> Prop) (t1 : ptree E MN A) (t2 : ptree E MN B) :
  pstrong RR t1 t2 ->
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A B RR t1 t2.
Proof.
  intro Hstrong. eapply peutt_coinduction with
    (sim := pstrong_state RR).
  - intros s1 s2 [u1 [u2 [-> [-> Hs]]]].
    destruct (stable_hitting_exists
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure A) (observe u1)) as [out1 Hout1].
    destruct (stable_hitting_exists
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure B) (observe u2)) as [out2 Hout2].
    eapply stable_hitting_match_of_hitting_lift;
      [exact Hout1|exact Hout2|].
    eapply FOQLMono.
    + unfold stable_hitting in Hout1, Hout2.
      cbn in Hout1, Hout2.
      eapply FOQLComp with (T := eq)
        (U := frontier_head_rel RR (pstrong RR))
        (mid := FOLub (fun fuel => ptree_hitting_approx
          (MF := MF) fuel (observe u1))).
      * exact Hout1.
      * eapply FOQLComp with
          (T := frontier_head_rel RR (pstrong RR))
          (U := eq)
          (mid := FOLub (fun fuel => ptree_hitting_approx
            (MF := MF) fuel (observe u2))).
        -- apply FOQLLub. intro fuel.
           apply FOQLStructural.
           exact (ptree_hitting_pstrong
             (RR := RR) fuel Hs).
        -- apply FOQLSym. eapply FOQLMono; [exact Hout2|].
           intros x y ->. reflexivity.
        -- intros x z [y [Hxy ->]]. exact Hxy.
      * intros x z [y [-> Hyz]]. exact Hyz.
    + intros h1 h2 Hhead. dependent destruction Hhead.
      * constructor. exact H.
      * constructor. intro x. exists (k1 x), (k2 x).
        repeat split; try reflexivity. exact (H x).
  - exists t1, t2. repeat split; try reflexivity. exact Hstrong.
Qed.

Definition pfinite_rel_state {A B} (RR : A -> B -> Prop)
    (s1 : ptree' E MN A) (s2 : ptree' E MN B) : Prop :=
  exists (t1 : ptree E MN A) (t2 : ptree E MN B),
    s1 = observe t1 /\ s2 = observe t2 /\
    @pfinite_rel E MN MF NI NC
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
      A B RR t1 t2.

(** Every finite weak proof is sound for the unbounded endpoint.  The key
    distinction is visible in the proof: finite Tau prefixes are eliminated
    by induction, while visible continuations return to coinduction. *)
Theorem peutt_of_pfinite_rel {A B}
    (RR : A -> B -> Prop) (t1 : ptree E MN A) (t2 : ptree E MN B) :
  @pfinite_rel E MN MF NI NC
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
      A B RR t1 t2 ->
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A B RR t1 t2.
Proof.
  intro Hfinite. eapply peutt_coinduction_upto with
    (sim := pfinite_rel_state RR).
  - intros s1 s2 [u1 [u2 [-> [-> Hrel]]]].
    induction Hrel as [u1 u2 Hcore|u1 u2 Hrel IH|u1 u2 Hrel IH].
    + pose proof (pfinite_rel_core_unfold Hcore) as Hstep.
      inversion Hstep as
          [v1 v2 Hstrong|v1 v2 out1 out2 Hhit1 Hhit2 Hlift]; subst.
      * pose proof (peutt_of_pstrong (RR := RR) Hstrong) as Hknown.
        apply peutt_unfold in Hknown.
        eapply stable_hitting_match_mono.
        -- apply ptree_stable_head_rel_mono.
        -- intros x1 x2 Hx. right. exact Hx.
        -- exact Hknown.
      * eapply stable_hitting_match_of_hitting_lift.
        -- exact (finite_stable_hitting_stable Hhit1).
        -- exact (finite_stable_hitting_stable Hhit2).
        -- eapply sem_lift_mono; [|exact Hlift].
           intros h1 h2 Hhead. dependent destruction Hhead.
           ++ constructor. exact H.
           ++ constructor. intro x. left.
              exists (k1 x), (k2 x). repeat split; try reflexivity.
              exact (H x).
    + unfold stable_hitting_match in IH |- *.
      destruct IH as [IHforward IHbackward]. split.
      * intros out Htau.
        apply (proj1 (stable_hitting_tau_iff u1 out)) in Htau.
        exact (IHforward out Htau).
      * intros out Hright.
        destruct (IHbackward out Hright) as [out1 [Hleft Hlift]].
        exists out1. split; [|exact Hlift].
        apply (proj2 (stable_hitting_tau_iff u1 out1)). exact Hleft.
    + unfold stable_hitting_match in IH |- *.
      destruct IH as [IHforward IHbackward]. split.
      * intros out Hleft.
        destruct (IHforward out Hleft) as [out2 [Hright Hlift]].
        exists out2. split; [|exact Hlift].
        apply (proj2 (stable_hitting_tau_iff u2 out2)). exact Hright.
      * intros out Htau.
        apply (proj1 (stable_hitting_tau_iff u2 out)) in Htau.
        exact (IHbackward out Htau).
  - exists t1, t2. repeat split; try reflexivity. exact Hfinite.
Qed.

Theorem peutt_of_pfinite {R}
    (t1 t2 : ptree E MN R) :
  @pfinite E MN MF NI NC
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega R t1 t2 ->
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R R eq t1 t2.
Proof.
  intro Hfinite. induction Hfinite.
  - now apply peutt_of_pfinite_rel.
  - apply peutt_refl.
  - now apply peutt_sym.
  - eapply peutt_trans; eauto.
Qed.

#[global] Instance pfinite_rel_peutt_subrelation {R} :
  subrelation
    (@pfinite_rel E MN MF NI NC
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega R R eq)
    (@peutt E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega R R eq).
Proof. intros t1 t2. apply peutt_of_pfinite_rel. Qed.

#[global] Instance pfinite_peutt_subrelation {R} :
  subrelation
    (@pfinite E MN MF NI NC
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega R)
    (@peutt E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega R R eq).
Proof. intros t1 t2. apply peutt_of_pfinite. Qed.

End FreeOmegaRelation.
