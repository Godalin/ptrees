Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

From Coq Require Import Program.Equality Classes.RelationClasses.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum FreeOmegaMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Semantics Require Import HeadTransition.

(** Architectural regression: the head transition theory does not even
    load PEutt transitively. Tests of concrete hitting computations below
    import its existing computation lemmas explicitly, after this check. *)
Fail Check PTree.Eq.PEutt.peutt.
From PTree.Eq Require Import PEutt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant head_testE : Type -> Type :=
  | Ask : head_testE bool
  | Tell : head_testE unit.

Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
Local Notation step := (@head_step head_testE SubEnum MF FI FreeOmegaMixedMeasure FO).
Local Notation bisim := (@head_bisim head_testE SubEnum MF FI FC
  FreeOmegaMixedMeasure FO bool bool eq).
Local Notation hits t out := (@ptree_stable_hitting head_testE SubEnum MF FI
  FreeOmegaMixedMeasure FO _ (observe t) out).

(** The action selects a distribution, not a single successor tree. *)
Example sampled_successor_step (mu : SubEnum bool) answer :
  step
    (FHVis Ask (fun a => Prob mu (fun b => Tau (Ret (xorb a b)))))
    (Obs Ask answer)
    (FOSample mu (fun b => FORet (FHRet (xorb answer b)))).
Proof.
  constructor.
  eapply (stable_hitting_prob (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. apply (proj2 (stable_hitting_tau_iff _ _)).
    apply (stable_hitting_ret (FI := FI) (FO := FO)).
Qed.

Example terminal_has_no_step label out : ~ step (FHRet true) label out.
Proof. apply head_step_ret. Qed.

Example action_event_is_not_erased k out :
  ~ step (FHVis Ask k) (Obs Tell tt) (out : MF (stable_head head_testE SubEnum bool)).
Proof. intro H. dependent destruction H. Qed.

Example distinct_returns_not_head_bisim :
  ~ bisim (FHRet true) (FHRet false).
Proof. rewrite head_bisim_ret_iff. discriminate. Qed.

Example heterogeneous_return_relation :
  @head_bisim head_testE SubEnum MF FI FC FreeOmegaMixedMeasure FO
    bool nat (fun b n => n = if b then 1 else 0) (FHRet true) (FHRet 1).
Proof. apply head_bisim_ret_iff. reflexivity. Qed.

Example head_equivalence_regression :
  Equivalence bisim.
Proof. apply head_bisim_equivalence. Qed.

(** A genuinely infinite interaction loop. The delayed implementation
    performs an internal Tau after every response. The proof is coinductive
    on selected visible heads, with complete successor hitting on each side. *)
CoFixpoint immediate_service : ptree head_testE SubEnum bool :=
  Vis Ask (fun _ => immediate_service).
CoFixpoint delayed_service : ptree head_testE SubEnum bool :=
  Vis Ask (fun _ => Tau delayed_service).

Definition immediate_head := FHVis Ask (fun _ => immediate_service).
Definition delayed_head := FHVis Ask (fun _ => Tau delayed_service).

Lemma immediate_service_hitting :
  hits immediate_service (FORet immediate_head).
Proof.
  change (hits (Vis Ask (fun _ => immediate_service)) (FORet immediate_head)).
  apply (stable_hitting_vis (FI := FI) (FO := FO)).
Qed.

Lemma delayed_service_hitting : hits (Tau delayed_service) (FORet delayed_head).
Proof.
  apply (proj2 (stable_hitting_tau_iff _ _)).
  change (hits (Vis Ask (fun _ => Tau delayed_service)) (FORet delayed_head)).
  apply (stable_hitting_vis (FI := FI) (FO := FO)).
Qed.

Theorem service_heads_bisimilar : bisim immediate_head delayed_head.
Proof.
  eapply head_bisim_coinduction with
    (sim := fun h1 h2 => h1 = immediate_head /\ h2 = delayed_head).
  - intros h1 h2 [-> ->]. constructor. intro answer.
    eapply stable_hitting_match_of_hitting_lift with
      (out1 := FORet immediate_head) (out2 := FORet delayed_head).
    + apply immediate_service_hitting.
    + apply delayed_service_hitting.
    + apply (@sem_lift_ret MF FI FC). split; reflexivity.
  - split; reflexivity.
Qed.

(** Acceptance formula at the actual chosen successor witnesses. *)
Example service_successors_coupled (answer : bool) :
  @sem_lift MF FI _ _ bisim
    (FORet immediate_head : MF (stable_head head_testE SubEnum bool))
    (FORet delayed_head).
Proof.
  exact (proj1 (head_bisim_vis_hitting_iff eq Ask
    (fun _ => immediate_service_hitting)
    (fun _ => delayed_service_hitting)) service_heads_bisimilar answer).
Qed.

(** A response may diverge internally. Step 1 is a SUBprobabilistic
    transition system, not the total MDP fragment planned for Step 2. *)
CoFixpoint silent_response : ptree head_testE SubEnum bool := Tau silent_response.

Definition silent_successors := FOLub (fun n =>
  ptree_hitting_approx (FI := FI) (FO := FO) n (observe silent_response)).

Example divergent_response_step answer :
  step (FHVis Ask (fun _ => silent_response)) (Obs Ask answer) silent_successors.
Proof.
  constructor. apply free_omega_qlift_refl. intro h. reflexivity.
Qed.

Example divergent_response_has_empty_support :
  free_omega_ae (fun _ => False) silent_successors.
Proof.
  apply FOAELub. intro n.
  assert (Hzero : ptree_hitting_approx (FI := FI) (FO := FO) n
    (observe silent_response) = FOZero).
  { induction n as [|n IH]; [reflexivity|].
    change (ptree_hitting_approx (FI := FI) (FO := FO) n
      (observe silent_response) = FOZero). exact IH. }
  rewrite Hzero. apply FOAEZero.
Qed.
