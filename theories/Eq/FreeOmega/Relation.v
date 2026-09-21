(** Role: Canonical equational/hitting theory. Depends on Core and Prob; does not provide comparison or interpreter semantics. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq.Program Require Import Equality.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PStruct PStrong PEutt PTreeKernel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FreeOmegaRelation.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).

Lemma ptree_hitting_pstruct {A B}
    (RR : A -> B -> Prop) fuel (t1 : ptree E MN A) (t2 : ptree E MN B) :
  pstruct RR t1 t2 ->
  free_omega_lift (stable_head_rel RR (pstruct RR))
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
      (@stable_head_rel E MN A B RR (@pstruct E MN A B RR))
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
      (@stable_head_rel E MN A B RR (@pstruct E MN A B RR))
      (FOSample mu (fun z => ptree_hitting_approx (MF := MF)
        fuel (observe (k1 z))))
      (FOSample mu (fun z => ptree_hitting_approx (MF := MF)
        fuel (observe (k2 z))))).
    eapply FOLSample with (S := eq).
    + apply sem_lift_refl. intros z. reflexivity.
    + intros z z' ->. apply IH. exact (H z').
Qed.

(** Structural equations preserve finite observations exactly, not merely
    up to a coupling.  The two result types and head observers may differ;
    only their agreement on related stable heads matters.  This lets a
    quantitative client analyse a simpler return type and transport its
    finite calculations through a structural program equation. *)
Theorem ptree_hitting_observes_pstruct {A B O}
    (RR : A -> B -> Prop)
    (obs1 : stable_head E MN A -> O)
    (obs2 : stable_head E MN B -> O)
    (Hobs : forall h1 h2, stable_head_rel RR (pstruct RR) h1 h2 ->
      obs1 h1 = obs2 h2)
    fuel (t1 : ptree E MN A) (t2 : ptree E MN B) out :
  pstruct RR t1 t2 ->
  free_omega_observes obs1
    (ptree_hitting_approx (MF := MF) fuel (observe t1)) out ->
  free_omega_observes obs2
    (ptree_hitting_approx (MF := MF) fuel (observe t2)) out.
Proof.
  revert t1 t2 out. induction fuel as [|fuel IH]; intros t1 t2 out Hstruct Hout;
    pose proof (pstruct_unfold Hstruct) as Hstep;
    dependent destruction Hstep;
    rewrite <- x0, <- x in *.
  all: cbn [ptree_hitting_approx ptree_primitive_kernel
    stable_hitting_approx stable_target_approx sem_bind sem_ret mixed_bind
    free_omega_bind FreeOmegaMixedMeasure FreeOmegaObservableSemanticMeasure
    FreeOmegaSemanticMeasure] in *.
  - dependent destruction Hout. rewrite (Hobs _ _ (FHRRet _ H)). constructor.
  - dependent destruction Hout. constructor.
  - dependent destruction Hout. rewrite (Hobs _ _ (FHRVis _ _ H)). constructor.
  - dependent destruction Hout. eapply FOOObserveSample.
    intro z. specialize (H z). dependent destruction H.
    rewrite <- x. constructor.
  - dependent destruction Hout. rewrite (Hobs _ _ (FHRRet _ H)). constructor.
  - eapply IH; eassumption.
  - dependent destruction Hout. rewrite (Hobs _ _ (FHRVis _ _ H)). constructor.
  - dependent destruction Hout. eapply FOOObserveSample.
    intro z. eapply IH; [apply H0|apply H].
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
        (U := stable_head_rel RR (pstruct RR))
        (mid := FOLub (fun fuel => ptree_hitting_approx
          (MF := MF) fuel (observe u1))).
      * exact Hout1.
      * eapply FOQLComp with
          (T := stable_head_rel RR (pstruct RR))
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
  free_omega_lift (stable_head_rel RR (pstrong RR))
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
      (@stable_head_rel E MN A B RR (@pstrong E MN NI NC A B RR))
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
      (@stable_head_rel E MN A B RR (@pstrong E MN NI NC A B RR))
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
        (U := stable_head_rel RR (pstrong RR))
        (mid := FOLub (fun fuel => ptree_hitting_approx
          (MF := MF) fuel (observe u1))).
      * exact Hout1.
      * eapply FOQLComp with
          (T := stable_head_rel RR (pstrong RR))
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

End FreeOmegaRelation.
