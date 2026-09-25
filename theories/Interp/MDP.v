(** MDP-fragment preservation under interpretation, for arbitrary native and
    frontier models. Probability laws are explicit; no FreeOmega syntax. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed BindOrder.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Interp Require Import Kernel Scheduling Guarded.
From PTree.Semantics Require Import MDPFragment TreeTransitionBisim MDPCoincidence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MDPInterp.
Context {E F MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.
Variable handler : forall X, E X -> ptree F MN X.
Context {R : Type}.
Local Notation shead := (stable_head E MN R).
Local Notation sgood := (@mdp_head E MN MF FI FC MX FO R).
Local Notation sstate := (@mdp_state E MN MF FI FC MX FO R).
Local Notation tstate := (@mdp_state F MN MF FI FC MX FO R).

(** A selected-head invariant, not the desired raw-tree preservation result. *)
Definition mdp_handler : Prop :=
  forall h : shead, sgood h -> tstate (ptree_interp_head_tree handler h).

Context `{FB : @SemanticMeasureBindLaws MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{BindOrd : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MixedOrd : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.

Theorem mdp_state_interp_of_ret_l
    (Hret_l : forall A B (x : A) (k : A -> MF B),
      sem_eq (sem_bind (sem_ret x) k) (k x))
    (Hhandler : mdp_handler) (t : ptree E MN R) :
  sstate t -> tstate (PTree.interp handler t).
Proof.
  intros [h [mu [Hhit [Heq Hgood]]]].
  destruct (stable_hitting_front_choice (FI := FI) (FO := FO)
    (fun h : shead => ptree_interp_head_tree handler h)) as [front Hfront].
  destruct (Hhandler h Hgood) as [h' [out [Hout [Hdirac Hgood']]]].
  eapply mdp_state_of_hitting with (h := h') (out := sem_bind mu front).
  - eapply (ptree_stable_hitting_interp (FI := FI) (FO := FO));
      [apply Scheduling.ptree_interp_cofinal_all|exact Hhit|exact Hfront].
  - eapply sem_eq_trans; [apply sem_bind_eq_l; exact Heq|].
    eapply sem_eq_trans; [apply Hret_l|].
    eapply sem_eq_trans; [|exact Hdirac].
    eapply stable_hitting_unique; [apply Hfront|exact Hout].
  - exact Hgood'.
Qed.

(** Class-based convenience wrapper. The primitive proof above consumes
    only the left-unit field, not unrelated laws in the bind record. *)
Theorem mdp_state_interp (Hhandler : mdp_handler) (t : ptree E MN R) :
  sstate t -> tstate (PTree.interp handler t).
Proof.
  exact (mdp_state_interp_of_ret_l (@sem_bind_ret_l MF FI FB) Hhandler (t := t)).
Qed.

Context `{FCAE : @SemanticMeasureCouplingAELaws MF FI}
  `{FOAE : @SemanticOmegaAELaws MF FI FO}
  `{FD : @SemanticMeasureDiracAELaws MF FI}.

Theorem mdp_interp_peutt_tree_trans_iff (Hhandler : mdp_handler) t u :
  sstate t -> sstate u ->
  (@peutt F MN MF FI FC MX FO R R eq (PTree.interp handler t) (PTree.interp handler u) <->
   @tree_trans_bisim F MN MF FI FC MX FO R R eq
     (PTree.interp handler t) (PTree.interp handler u)).
Proof.
  intros Ht Hu. apply mdp_state_peutt_tree_trans_iff;
    apply mdp_state_interp; assumption.
Qed.

Theorem mdp_guarded_interp_tree_trans (Hhandler : mdp_handler)
    (Hguard : guarded_handler (MF := MF) handler) t u :
  sstate t -> sstate u ->
  @tree_trans_bisim E MN MF FI FC MX FO R R eq t u ->
  @tree_trans_bisim F MN MF FI FC MX FO R R eq
    (PTree.interp handler t) (PTree.interp handler u).
Proof.
  intros Ht Hu Htu.
  apply (proj1 (mdp_interp_peutt_tree_trans_iff Hhandler Ht Hu)).
  apply (Guarded.peutt_interp_guarded (MF := MF) Hguard).
  exact (mdp_state_tree_trans_bisim_peutt Ht Hu Htu).
Qed.
End MDPInterp.
