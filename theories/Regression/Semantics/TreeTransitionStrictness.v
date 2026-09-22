(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Program Require Import Equality.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg rat.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling PTree.Prob.Backend.EnumQ.SemanticCoupling PTree.Prob.Backend.EnumQ.FrontierLift.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Semantics Require Import HeadTransition TreeTransition TreeTransitionBisim.
Fail Check PTree.Eq.PEutt.peutt.
From PTree.Eq Require Import PEutt.
From PTree.Semantics Require Import TreeTransitionSoundness.
From PTree.Regression.Backend Require Import EnumQMeasureRegression SubEnumQRegression.
From PTree.Regression.Probability Require Import CorrelatedSampleAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant correlationE : Type -> Type := Query : correlationE bool.
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).
Local Notation tree := (ptree correlationE SubEnumQ bool).
Local Notation head := (stable_head correlationE SubEnumQ bool).
Local Notation W := (@peutt correlationE SubEnumQ MF FI FC FreeOmegaMixedMeasure FO bool bool eq).
Local Notation TB := (@tree_trans_bisim correlationE SubEnumQ MF FI FC FreeOmegaMixedMeasure FO bool bool eq).
Local Notation HR := (stable_head_rel eq W).
Local Notation hits t out := (@ptree_stable_hitting correlationE SubEnumQ MF FI
  FreeOmegaMixedMeasure FO bool (observe t) out).
Local Notation trans := (@tree_trans correlationE SubEnumQ MF FI FreeOmegaMixedMeasure FO bool).
Local Notation returns := (@tree_return_observation correlationE SubEnumQ MF FI FreeOmegaMixedMeasure FO bool).
Local Notation offers := (@tree_offered_event_observation correlationE SubEnumQ MF FI FreeOmegaMixedMeasure FO bool).

(** The two rows are the two possible hidden coins; the columns are the
    two responses. P has rows (false,false), (true,true), whereas Q has
    rows (false,true), (true,false), all with probability one half. *)
Definition answer (anti b x : bool) := if anti then (if x then negb b else b) else b.
Definition correlation_head anti b : head := FHVis Query (fun x => Ret (answer anti b x)).
Definition correlation_program anti : tree :=
  Prob subenumQ_fair (fun b => Vis Query (fun x => Ret (answer anti b x))).
Definition P := correlation_program false.
Definition Q := correlation_program true.
Definition correlation_front anti : MF head :=
  FOSample subenumQ_fair (fun b => FORet (correlation_head anti b)).
Definition response_front anti x : MF head :=
  FOSample subenumQ_fair (fun b => FORet (FHRet (answer anti b x))).

Lemma correlation_hitting anti : hits (correlation_program anti) (correlation_front anti).
Proof.
  eapply (ptree_stable_hitting_prob (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
Qed.

Lemma correlation_returns anti :
  returns (correlation_program anti) (FOSample subenumQ_fair (fun _ => FOZero)).
Proof. exists (correlation_front anti). split; [apply correlation_hitting|apply sem_eq_refl]. Qed.
Lemma correlation_offers anti :
  offers (correlation_program anti) (FOSample subenumQ_fair (fun _ => FORet (Offered Query))).
Proof. exists (correlation_front anti). split; [apply correlation_hitting|apply sem_eq_refl]. Qed.

(** A contribution witness only for these finite supported continuations. *)
Definition respond x (h : head) : MF head :=
  match h with
  | FHRet _ => FOZero
  | @FHVis _ _ _ X e k =>
    (match e in correlationE X return (X -> tree) -> MF head with
     | Query => fun k => match observe (k x) with
         | RetF r => FORet (FHRet r) | _ => FOZero end
     end) k
  end.

Lemma correlation_transition anti x :
  trans (correlation_program anti) (Obs Query x) (response_front anti x).
Proof.
  exists (correlation_front anti), (respond x).
  split; [apply correlation_hitting|]. split; [|apply sem_eq_refl].
  eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
  intros b _. apply FOAERet, HARMatch. constructor.
  apply (ptree_stable_hitting_ret (FI := FI) (FO := FO)).
Qed.

Import EnumQ PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling GRing.Theory.
Local Open Scope ring_scope.

(** Crossed coupling for the true response; false uses the diagonal one. *)
Lemma fair_complement_coupling :
  @sem_lift SubEnumQ SubEnumQ_SemanticMeasure bool bool
    (fun b c => b = negb c) subenumQ_fair subenumQ_fair.
Proof.
  change (@sem_lift EnumQ EnumQ_SemanticMeasure bool bool
    (fun b c => b = negb c) reg_fair reg_fair).
  apply enumQ_sem_lift_of_coupling.
  exists (unif2 (false,true) (true,false)).
  - intros []; native_compute; reflexivity.
  - intros []; native_compute; reflexivity.
  - intros [] [] Hmass; try reflexivity; native_compute in Hmass; discriminate.
Qed.

Lemma response_marginals_equal x :
  @sem_lift MF FI head head eq (response_front false x) (response_front true x).
Proof.
  destruct x.
  - eapply FOQLSample with (T := fun b c => b = negb c).
    + exact fair_complement_coupling.
    + intros b c Hbc. apply FOQLStructural, FOLRet. cbn. congruence.
  - eapply FOQLSample with (T := eq).
    + apply sem_lift_refl. intro b. reflexivity.
    + intros b c ->. apply FOQLStructural, FOLRet. reflexivity.
Qed.

(** Equality closes all later states, since successors are already Ret. *)
Definition correlation_candidate (t u : tree) := t = u \/ (t = P /\ u = Q).

Lemma correlation_postfixed t u : correlation_candidate t u ->
  @tree_trans_bisimF correlationE SubEnumQ MF FI FreeOmegaMixedMeasure FO bool bool eq
    correlation_candidate t u.
Proof.
  intros [->|[-> ->]].
  - split.
    + split; intros out Hout; exists out; split; try exact Hout;
        apply sem_lift_refl; intro b; reflexivity.
    + split.
      * split; intros out Hout; exists out; split; try exact Hout;
          apply sem_lift_refl; intro e; reflexivity.
      * intro label. split; intros out Hout; exists out; split; try exact Hout;
          apply sem_lift_refl; intro h; left; reflexivity.
  - split.
    + eapply tree_measure_match_of_witnesses.
      * intros. eapply tree_head_observation_unique; eassumption.
      * intros. eapply tree_head_observation_unique; eassumption.
      * exact (correlation_returns false).
      * exact (correlation_returns true).
      * apply sem_lift_refl. intro b. reflexivity.
    + split.
      * eapply tree_measure_match_of_witnesses.
        -- intros. eapply tree_head_observation_unique; eassumption.
        -- intros. eapply tree_head_observation_unique; eassumption.
        -- exact (correlation_offers false).
        -- exact (correlation_offers true).
        -- apply sem_lift_refl. intro e. reflexivity.
      * intros [X e x]. destruct e.
        eapply tree_measure_match_of_witnesses.
        -- intros. eapply tree_trans_unique; eassumption.
        -- intros. eapply tree_trans_unique; eassumption.
        -- exact (correlation_transition false x).
        -- exact (correlation_transition true x).
        -- eapply sem_lift_mono; [|exact (response_marginals_equal x)].
           intros h k ->. left. reflexivity.
Qed.

Theorem correlated_response_tree_trans_bisim : TB P Q.
Proof.
  eapply tree_trans_bisim_coinduction with (sim := correlation_candidate).
  - exact correlation_postfixed.
  - right. split; reflexivity.
Qed.

(** Inversion uses the concrete backend's support transport, not a new
    generic Dirac-injectivity law. *)
Lemma return_peutt_injective b c : W (Ret b) (Ret c) -> b = c.
Proof.
  intro Hrel.
  assert (Hlift : @sem_lift MF FI head head HR (FORet (FHRet b)) (FORet (FHRet c))).
  { eapply peutt_couples_complete_heads; [exact Hrel| |];
      apply (ptree_stable_hitting_ret (FI := FI) (FO := FO)). }
  assert (Hb : free_omega_ae (NI := SubEnumQ_SemanticMeasure)
    (fun h : head => h = FHRet b) (FORet (FHRet b))).
  { constructor. reflexivity. }
  pose proof (proj1 (free_omega_qlift_support Hlift) _ Hb) as Hc.
  dependent destruction Hc. destruct H as [h [Hhr ->]]. inversion Hhr. assumption.
Qed.

Lemma no_correlated_head_pair b c : ~ HR (correlation_head false b) (correlation_head true c).
Proof.
  intro Hrel. dependent destruction Hrel.
  pose proof (return_peutt_injective (H false)) as Hfalse.
  pose proof (return_peutt_injective (H true)) as Htrue.
  destruct b, c; discriminate.
Qed.

Theorem correlated_response_not_peutt : ~ W P Q.
Proof.
  intro Hrel.
  pose proof (peutt_couples_complete_heads Hrel (correlation_hitting false)
    (correlation_hitting true)) as Hfront.
  assert (Hleft : free_omega_ae (NI := SubEnumQ_SemanticMeasure)
    (fun h => exists b, h = correlation_head false b) (correlation_front false)).
  { eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros b _. apply FOAERet. exists b. reflexivity. }
  pose proof (proj1 (free_omega_qlift_support Hfront) _ Hleft) as Hright.
  apply free_omega_ae_sample_inv in Hright.
  pose proof (proj1 (exchange_fair_both_values Hright)) as Htrue.
  dependent destruction Htrue. destruct H as [h [Hhr [b ->]]].
  exact (no_correlated_head_pair Hhr).
Qed.

(** Concrete proper inclusion: universal forward implication plus one
    independently proved transition-equivalent, peutt-distinct pair. *)
Theorem peutt_strictly_contained_in_tree_trans_bisim :
  (forall t u, W t u -> TB t u) /\ (TB P Q /\ ~ W P Q).
Proof.
  split.
  - intros t u H. exact (peutt_tree_trans_bisim (FI := FI) (FC := FC) (FO := FO) H).
  - split; [exact correlated_response_tree_trans_bisim|exact correlated_response_not_peutt].
Qed.
