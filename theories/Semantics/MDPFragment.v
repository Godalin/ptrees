(** Role: Comparison semantics. Depends on canonical theory; not the canonical peutt relation or interpreter theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Program.
From Coq.Arith Require Import PeanoNat.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Semantics Require Import HeadTransition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MDPFragment.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.
Context {R : Type}.
Local Notation head := (stable_head E MN R).
Local Notation hits t out :=
  (ptree_stable_hitting (MF := MF) (observe t) out).

(** A unary invariant on selected states, not a behavioral relation.
    A response yields a total DISTRIBUTION of qualifying successor heads;
    its continuation need not itself denote a Dirac state. *)
Definition mdp_headF (P : head -> Prop) (h : head) : Prop :=
  match h with
  | FHRet _ => True
  | @FHVis _ _ _ X e k => forall x : X, exists out,
      head_step (MF := MF) (FHVis e k) (Obs e x) out /\
      sem_total out /\ sem_ae out P
  end.

Lemma mdp_headF_mono P Q :
  (forall h, P h -> Q h) -> forall h, mdp_headF P h -> mdp_headF Q h.
Proof.
  intros Hsub h H. destruct h as [r|X e k]; simpl in *; [exact I|].
  intro x. destruct (H x) as [out [Hstep [Htotal Hae]]].
  exists out. split; [exact Hstep|]. split; [exact Htotal|].
  eapply sem_ae_mono; eauto.
Qed.

Program Definition fmdp_head : mon (head -> Prop) := {| body := mdp_headF |}.
Next Obligation.
  intros P Q Hsub h H. eapply mdp_headF_mono; eauto.
Qed.

Definition mdp_head : head -> Prop := gfp fmdp_head.

Lemma mdp_head_unfold h : mdp_head h -> mdp_headF mdp_head h.
Proof. intro H. apply (gfp_pfp fmdp_head) in H. exact H. Qed.

Lemma mdp_head_fold h : mdp_headF mdp_head h -> mdp_head h.
Proof. intro H. unfold mdp_head. apply (gfp_fp fmdp_head). exact H. Qed.

Theorem mdp_head_coinduction (P : head -> Prop)
    (Hpost : forall h, P h -> mdp_headF P h) :
  forall h, P h -> mdp_head h.
Proof.
  intros h HP. unfold mdp_head.
  eapply (@leq_gfp _ _ fmdp_head P); eauto.
Qed.

Lemma mdp_head_ret r : mdp_head (FHRet r).
Proof. apply mdp_head_fold. exact I. Qed.

Lemma mdp_head_vis_iff {X} (e : E X) (k : X -> ptree E MN R) :
  mdp_head (FHVis e k) <->
  forall x, exists out, hits (k x) out /\ sem_total out /\ sem_ae out mdp_head.
Proof.
  split; intro H.
  - apply mdp_head_unfold in H. intro x.
    destruct (H x) as [out [Hstep Hrest]]. exists out. split; [|exact Hrest].
    apply head_step_vis_iff in Hstep. exact Hstep.
  - apply mdp_head_fold. intro x.
    destruct (H x) as [out [Hhit Hrest]]. exists out. split; [constructor|]; assumption.
Qed.

(** A single state, up to the backend's semantic equality. Hidden choices
    over distinct heads instead denote distributions of states. *)
Definition mdp_state (t : ptree E MN R) : Prop :=
  exists h out, hits t out /\ sem_eq out (sem_ret h) /\ mdp_head h.

Lemma mdp_state_of_hitting t h out :
  hits t out -> sem_eq out (sem_ret h) -> mdp_head h -> mdp_state t.
Proof. intros Hhit Heq Hhead. exists h, out. auto. Qed.

Lemma mdp_state_hitting_iff `{FOL : @SemanticOmegaLaws MF FI FO} t out
    (Hhit : hits t out) :
  mdp_state t <-> exists h, sem_eq out (sem_ret h) /\ mdp_head h.
Proof.
  split.
  - intros [h [w [Hw [Heq Hhead]]]]. exists h. split; [|exact Hhead].
    eapply sem_eq_trans; [eapply stable_hitting_unique; eassumption|exact Heq].
  - intros [h [Heq Hhead]]. eapply mdp_state_of_hitting; eauto.
Qed.

Section SuccessorClosure.
Context `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FTP : @SemanticTotalProperLaws MF FI FO}
  `{FCAE : @SemanticMeasureCouplingAELaws MF FI}.

(** Closure holds for ANY complete successor witness, not only the
    existential representative used to unfold the invariant. *)
Theorem mdp_head_successor_closed h label out :
  mdp_head h -> head_step h label out ->
  sem_total out /\ sem_ae out mdp_head.
Proof.
  intros Hhead Hstep. destruct Hstep as [X e k x out Hhit].
  destruct (proj1 (mdp_head_vis_iff e k) Hhead x)
    as [w [Hw [Htotal Hae]]].
  assert (Heq : sem_eq w out) by (eapply stable_hitting_unique; eassumption).
  split.
  - exact (proj1 (sem_total_proper Heq) Htotal).
  - assert (Hlift : sem_lift eq w out).
    { eapply sem_lift_proper_r; [exact Heq|].
      apply sem_lift_refl. intro a. reflexivity. }
    pose proof (sem_lift_ae_transport_r Hlift Hae) as Htransport.
    eapply sem_ae_mono; [|exact Htransport].
    intros a [b [-> Hb]]. exact Hb.
Qed.

Lemma mdp_head_vis_hitting_iff {X} (e : E X) (k : X -> ptree E MN R)
    (front : X -> MF head) (Hhit : forall x, hits (k x) (front x)) :
  mdp_head (FHVis e k) <->
  forall x, sem_total (front x) /\ sem_ae (front x) mdp_head.
Proof.
  split.
  - intros H x. eapply mdp_head_successor_closed; [exact H|].
    constructor. apply Hhit.
  - intro H. apply (proj2 (mdp_head_vis_iff e k)).
    intro x. exists (front x). split; [apply Hhit|apply H].
Qed.
End SuccessorClosure.

Section StateComputation.
Context `{FB : @SemanticMeasureBindLaws MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}.

Lemma mdp_state_ret r : mdp_state (Ret r).
Proof.
  eapply mdp_state_of_hitting with (h := FHRet r) (out := sem_ret (FHRet r)).
  - apply ptree_stable_hitting_ret.
  - apply sem_eq_refl.
  - apply mdp_head_ret.
Qed.

Lemma mdp_state_vis_of_head {X} (e : E X) (k : X -> ptree E MN R) :
  mdp_head (FHVis e k) -> mdp_state (Vis e k).
Proof.
  intro H. eapply mdp_state_of_hitting with
    (h := FHVis e k) (out := sem_ret (FHVis e k)).
  - apply ptree_stable_hitting_vis.
  - apply sem_eq_refl.
  - exact H.
Qed.

Lemma mdp_state_vis {X} (e : E X) (k : X -> ptree E MN R) :
  (forall x, exists out, hits (k x) out /\ sem_total out /\ sem_ae out mdp_head) ->
  mdp_state (Vis e k).
Proof.
  intro H. apply mdp_state_vis_of_head.
  exact (proj2 (mdp_head_vis_iff e k) H).
Qed.

Lemma mdp_state_tau_iff t : mdp_state (Tau t) <-> mdp_state t.
Proof.
  split; intros [h [out [Hhit Hrest]]]; exists h, out; split; [|exact Hrest| |exact Hrest].
  - exact (proj1 (ptree_stable_hitting_tau_iff t out) Hhit).
  - exact (proj2 (ptree_stable_hitting_tau_iff t out) Hhit).
Qed.

Lemma mdp_state_tau_iter_iff n t :
  mdp_state (Nat.iter n (fun u => Tau u) t) <-> mdp_state t.
Proof.
  induction n as [|n IH]; [reflexivity|].
  change (mdp_state (Tau (Nat.iter n (fun u => Tau u) t)) <-> mdp_state t).
  rewrite mdp_state_tau_iff. exact IH.
Qed.
End StateComputation.
End MDPFragment.
