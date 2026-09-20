(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Program Require Import Equality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.Backend Require Import TwoLevelMeasureSubEnum.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel.
From PTree.Semantics Require Import HeadTransition TreeTransition TreeTransitionBisim.
From PTree.Regression.Backend Require Import SubEnumRegression.
From PTree.Regression.Probability Require Import CorrelatedSampleAlgebra.
From PTree.Regression.Semantics Require Import TreeTransitionStrictness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Stage 1: an exposure experiment, not a new interpreter or relation.
    Reuse exactly the accepted 2x2 pair, on the SAME event interface.
    The handler ignores its first answer and returns its second answer.
    It is deterministic, total, and visibly guarded, but not atomic. *)
Definition two_query_handler X (e : correlationE X) : ptree correlationE SubEnum X :=
  match e in correlationE X return ptree correlationE SubEnum X with
  | Query => Vis Query (fun _ => Vis Query (fun x => Ret x))
  end.

Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
Local Notation tree := (ptree correlationE SubEnum bool).
Local Notation head := (stable_head correlationE SubEnum bool).
Local Notation TB := (@tree_trans_bisim correlationE SubEnum MF FI FC FreeOmegaMixedMeasure FO bool bool eq).
Local Notation hits t out := (@ptree_stable_hitting correlationE SubEnum MF FI
  FreeOmegaMixedMeasure FO bool (observe t) out).
Local Notation trans := (@tree_trans correlationE SubEnum MF FI FreeOmegaMixedMeasure FO bool).

(** Even semantic visible guarding alone will not suffice for transition
    congruence: the handler's complete first behavior is this Dirac Vis. *)
Lemma two_query_handler_first_hitting :
  hits (two_query_handler Query)
    (FORet (FHVis Query (fun _ => Vis Query (fun x => Ret x)))).
Proof. apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)). Qed.

Definition exposure anti : tree := PTree.interp two_query_handler (correlation_program anti).
Definition exposure_resume anti b (x : bool) : tree :=
  PTree.interp two_query_handler (Ret (answer anti b x)).
Definition exposure_last anti b (x : bool) : tree :=
  PTree.bind (Ret x) (exposure_resume anti b).
Definition exposure_second anti b : tree :=
  PTree.bind (Vis Query (fun x => Ret x)) (exposure_resume anti b).
Definition exposure_second_head anti b : head :=
  FHVis Query (exposure_last anti b).
Definition exposure_first_head anti b : head :=
  FHVis Query (fun _ => exposure_second anti b).
Definition exposure_front anti : MF head :=
  FOSample subenum_fair (fun b => FORet (exposure_first_head anti b)).
Definition exposure_successors anti : MF head :=
  FOSample subenum_fair (fun b => FORet (exposure_second_head anti b)).

Lemma exposure_last_hitting anti b x :
  hits (exposure_last anti b x) (FORet (FHRet (answer anti b x))).
Proof.
  change (hits (Ret (answer anti b x)) (FORet (FHRet (answer anti b x)))).
  apply (ptree_stable_hitting_ret (FI := FI) (FO := FO)).
Qed.

Lemma exposure_second_hitting anti b :
  hits (exposure_second anti b) (FORet (exposure_second_head anti b)).
Proof.
  change (hits (Vis Query (exposure_last anti b))
    (FORet (FHVis Query (exposure_last anti b)))).
  apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
Qed.

Lemma exposure_hitting anti : hits (exposure anti) (exposure_front anti).
Proof.
  change (hits (Prob subenum_fair (fun b =>
    PTree.interp two_query_handler (Vis Query (fun x => Ret (answer anti b x)))))
    (exposure_front anti)).
  eapply (ptree_stable_hitting_prob (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _.
    change (hits (Tau (PTree.bind (two_query_handler Query) (exposure_resume anti b)))
      (FORet (exposure_first_head anti b))).
    apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    change (hits (Vis Query (fun _ => exposure_second anti b))
      (FORet (FHVis Query (fun _ => exposure_second anti b)))).
    apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
Qed.

(** Both interpreted programs still have identical current return and
    offered-event observations. Separation happens AFTER the first action. *)
Lemma exposure_returns anti :
  @tree_return_observation correlationE SubEnum MF FI FreeOmegaMixedMeasure FO bool
    (exposure anti) (FOSample subenum_fair (fun _ => FOZero)).
Proof. exists (exposure_front anti). split; [apply exposure_hitting|apply sem_eq_refl]. Qed.

Lemma exposure_offers anti :
  @tree_offered_event_observation correlationE SubEnum MF FI FreeOmegaMixedMeasure FO bool
    (exposure anti) (FOSample subenum_fair (fun _ => FORet (Offered Query))).
Proof. exists (exposure_front anti). split; [apply exposure_hitting|apply sem_eq_refl]. Qed.

(** A finite witness used only by this experiment. It is not a general
    stable-hitting evaluator. All continuations below are already stable. *)
Definition exposure_action x (h : head) : MF head :=
  match h with
  | FHRet _ => FOZero
  | @FHVis _ _ _ X e k =>
    (match e in correlationE X return (X -> tree) -> MF head with
     | Query => fun k => match observe (k x) with
       | @VisF _ _ _ _ Y e' k' => FORet (FHVis e' k')
       | RetF r => FORet (FHRet r)
       | _ => FOZero
       end
     end) k
  end.

Lemma exposure_first_transition anti x :
  trans (exposure anti) (Obs Query x) (exposure_successors anti).
Proof.
  exists (exposure_front anti), (exposure_action x).
  split; [apply exposure_hitting|]. split; [|apply sem_eq_refl].
  eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
  intros b _. apply FOAERet, HARMatch. constructor.
  exact (exposure_second_hitting anti b).
Qed.

Lemma exposure_second_transition anti b x :
  trans (stable_head_tree (exposure_second_head anti b)) (Obs Query x)
    (FORet (FHRet (answer anti b x))).
Proof.
  apply (tree_trans_vis (FI := FI) (FO := FO)).
  exact (exposure_last_hitting anti b x).
Qed.

Lemma exposure_return_injective b c : TB (Ret b) (Ret c) -> b = c.
Proof.
  intro Hrel.
  pose proof (tree_trans_bisim_return_observations Hrel
    (tree_return_ret (FI := FI) (FO := FO) b)
    (tree_return_ret (FI := FI) (FO := FO) c)) as Hlift.
  assert (Hb : free_omega_ae (NI := SubEnum_SemanticMeasure)
    (fun x : bool => x = b) (FORet b)).
  { constructor. reflexivity. }
  pose proof (proj1 (free_omega_qlift_support Hlift) _ Hb) as Hc.
  dependent destruction Hc. destruct H as [x [-> ->]]. reflexivity.
Qed.

(** Once the first target interaction has occurred, each matched pair
    must face BOTH possible second answers with the SAME hidden-bit pair. *)
Lemma exposure_second_pair_impossible b c :
  ~ TB (stable_head_tree (exposure_second_head false b))
       (stable_head_tree (exposure_second_head true c)).
Proof.
  intro Hrel.
  assert (Hanswer : forall x, answer false b x = answer true c x).
  { intro x.
    pose proof (tree_trans_bisim_transitions Hrel
      (exposure_second_transition false b x)
      (exposure_second_transition true c x)) as Hlift.
    assert (Hb : free_omega_ae (NI := SubEnum_SemanticMeasure)
      (fun h : head => h = FHRet (answer false b x))
      (FORet (FHRet (answer false b x)))).
    { constructor. reflexivity. }
    pose proof (proj1 (free_omega_qlift_support Hlift) _ Hb) as Hc.
    dependent destruction Hc. destruct H as [h [Hpair ->]].
    exact (exposure_return_injective Hpair). }
  specialize (Hanswer false) as Hfalse.
  specialize (Hanswer true) as Htrue.
  destruct b, c; discriminate.
Qed.

Theorem two_query_interp_not_tree_trans_bisim : ~ TB (exposure false) (exposure true).
Proof.
  intro Hrel.
  pose proof (tree_trans_bisim_transitions Hrel
    (exposure_first_transition false false)
    (exposure_first_transition true false)) as Hlift.
  assert (Hleft : free_omega_ae (NI := SubEnum_SemanticMeasure)
    (fun h => exists b, h = exposure_second_head false b) (exposure_successors false)).
  { eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros b _. apply FOAERet. exists b. reflexivity. }
  pose proof (proj1 (free_omega_qlift_support Hlift) _ Hleft) as Hright.
  apply free_omega_ae_sample_inv in Hright.
  pose proof (proj1 (exchange_fair_both_values Hright)) as Htrue.
  dependent destruction Htrue. destruct H as [h [Hpair [b ->]]].
  exact (exposure_second_pair_impossible Hpair).
Qed.

(** Direct failure of arbitrary interpretation congruence. No use of
    [~ peutt P Q] to infer a negative transition-bisimulation statement. *)
Theorem tree_trans_bisim_interp_counterexample :
  TB P Q /\
  ~ TB (PTree.interp two_query_handler P) (PTree.interp two_query_handler Q).
Proof.
  split; [exact correlated_response_tree_trans_bisim|].
  exact two_query_interp_not_tree_trans_bisim.
Qed.

Corollary tree_trans_bisim_not_interp_congruent :
  ~ (forall (handler : forall X, correlationE X -> ptree correlationE SubEnum X)
      (t u : tree), TB t u -> TB (PTree.interp handler t) (PTree.interp handler u)).
Proof.
  intro Hpreserve. apply two_query_interp_not_tree_trans_bisim.
  exact (Hpreserve two_query_handler P Q correlated_response_tree_trans_bisim).
Qed.
