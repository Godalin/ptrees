(** Two-phase complete-frontier machine for interpreting effects. Returning
    from a handler is an INTERNAL transition back to a source configuration,
    not an unguarded appeal to target behavioral equivalence. This module
    proves relational simulation of that machine. Adequacy with the existing
    tree interpreter is a separate obligation; it is not assumed here. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed RelationalClosure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel
  PEutt RelationalHitting.
From PTree.Interp Require Import Preservation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section HandlerConfigurations.
Context {E F MN : Type -> Type}.

Inductive handler_config (A : Type) : Type :=
| SourceConfig (t : ptree E MN A)
| HandlerConfig {X : Type} (active : ptree F MN X) (k : X -> ptree E MN A).
Arguments SourceConfig {A} _.
Arguments HandlerConfig {A X} _ _.

Variable handler : forall X, E X -> ptree F MN X.

Definition handler_config_tree {A} (c : handler_config A) : ptree F MN A :=
  match c with
  | SourceConfig t => PTree.interp handler t
  | @HandlerConfig _ _ active k =>
      PTree.bind active (fun x => PTree.interp handler (k x))
  end.

Definition source_front_result {A} (h : stable_head E MN A) :
    stable_target (handler_config A) (stable_head F MN A) :=
  match h with
  | FHRet a => SHStable (FHRet a)
  | @FHVis _ _ _ X e k => SHInternal (HandlerConfig (handler e) k)
  end.

Definition handler_front_result {A X} (k : X -> ptree E MN A)
    (h : stable_head F MN X) : stable_target (handler_config A) (stable_head F MN A) :=
  match h with
  | FHRet x => SHInternal (SourceConfig (k x))
  | @FHVis _ _ _ Y e c => SHStable (FHVis e
      (fun y => PTree.bind (c y) (fun x => PTree.interp handler (k x))))
  end.
End HandlerConfigurations.
Arguments SourceConfig {E F MN A} _.
Arguments HandlerConfig {E F MN A X} _ _.

Section PrimitiveMachine.
Context {E F MN MF : Type -> Type} `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF}.
Variable handler : forall X, E X -> ptree F MN X.

(** The physical machine performs one native operation, rather than taking
    a complete frontier. Its extra handler-return transition is silent. *)
Definition handler_primitive_kernel {A} (c : @handler_config E F MN A) :
    MF (stable_target (@handler_config E F MN A) (stable_head F MN A)) :=
  match c with
  | SourceConfig t =>
      match observe t with
      | RetF a => sem_ret (SHStable (FHRet a))
      | TauF u => sem_ret (SHInternal (SourceConfig u))
      | @VisF _ _ _ _ X e k => sem_ret (SHInternal (HandlerConfig (handler e) k))
      | @ProbF _ _ _ _ X mu k =>
          mixed_bind mu (fun x => sem_ret (SHInternal (SourceConfig (k x))))
      end
  | @HandlerConfig _ _ _ _ X active k =>
      match observe active with
      | RetF x => sem_ret (SHInternal (SourceConfig (k x)))
      | TauF u => sem_ret (SHInternal (HandlerConfig u k))
      | @VisF _ _ _ _ Y e d => sem_ret (SHStable
          (FHVis e (fun y => PTree.bind (d y) (fun x => PTree.interp handler (k x)))))
      | @ProbF _ _ _ _ Y mu d =>
          mixed_bind mu (fun y => sem_ret (SHInternal (HandlerConfig (d y) k)))
      end
  end.
End PrimitiveMachine.

Section CompleteFrontier.
Context {MN MF : Type -> Type} `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.

(** An existing omega-selection capability chooses representatives. This is
    not a new probability capability or an equality reflection assumption. *)
Definition handler_complete_front {E A} (t : ptree E MN A) : MF (stable_head E MN A) :=
  proj1_sig (sem_lub_choose
    (chain := fun n => ptree_hitting_approx (MF := MF) n (observe t))
    (ptree_hitting_increasing (observe t))).

Lemma handler_complete_front_hitting {E A} (t : ptree E MN A) :
  ptree_stable_hitting (MF := MF) (observe t) (handler_complete_front t).
Proof. exact (proj2_sig (sem_lub_choose _)). Qed.

Context {E F : Type -> Type} (handler : forall X, E X -> ptree F MN X).

Definition handler_machine_kernel {A} (c : @handler_config E F MN A) :
    MF (stable_target (@handler_config E F MN A) (stable_head F MN A)) :=
  match c with
  | SourceConfig t =>
      sem_bind (handler_complete_front t) (fun h => sem_ret (source_front_result handler h))
  | @HandlerConfig _ _ _ _ _ active k =>
      sem_bind (handler_complete_front active) (fun h => sem_ret (handler_front_result handler k h))
  end.
End CompleteFrontier.

Section HandlerMachineSimulation.
Context {E F MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.
Variable Hbind : relational_bind FI.
Variable handler : forall X, E X -> ptree F MN X.
Context {A B : Type} (RR : A -> B -> Prop).

Local Notation source_rel := (@peutt E MN MF FI FC MX FO A B RR).
Local Notation candidate := (interp_bisim_candidate (MF := MF) RR handler).
Local Notation heads_rel := (@ptree_stable_head_rel F MN A B RR
  (@bind_upto_closure F MN MF FI FC MX FO A B RR candidate)).

Inductive handler_config_rel :
    @handler_config E F MN A -> @handler_config E F MN B -> Prop :=
| SourceConfigsRelated t u : source_rel t u ->
    handler_config_rel (SourceConfig t) (SourceConfig u)
| HandlerConfigsRelated {X} (active : ptree F MN X)
    (k1 : X -> ptree E MN A) (k2 : X -> ptree E MN B) :
    (forall x, source_rel (k1 x) (k2 x)) ->
    handler_config_rel (HandlerConfig active k1) (HandlerConfig active k2).

Lemma handler_front_result_related {X} (k1 : X -> ptree E MN A)
    (k2 : X -> ptree E MN B) :
  (forall x, source_rel (k1 x) (k2 x)) ->
  forall h : stable_head F MN X,
    stable_target_rel handler_config_rel heads_rel
      (handler_front_result handler k1 h) (handler_front_result handler k2 h).
Proof.
  intros Hk [x|Y e c]; cbn [handler_front_result stable_target_rel].
  - constructor. apply Hk.
  - constructor. intro y. right. right.
    exists X, X, (@eq X), (c y), (c y),
      (fun x => PTree.interp handler (k1 x)),
      (fun x => PTree.interp handler (k2 x)).
    split; [reflexivity|]. split; [reflexivity|].
    split; [apply peutt_refl|]. intros x x' ->. left.
    exists (k1 x'), (k2 x'). repeat split; try reflexivity. apply Hk.
Qed.

Theorem handler_machine_kernel_related c d :
  handler_config_rel c d ->
  sem_lift (stable_target_rel handler_config_rel heads_rel)
    (handler_machine_kernel handler c) (handler_machine_kernel handler d).
Proof.
  intro H. inversion H; subst; unfold handler_machine_kernel.
  - eapply Hbind.
    + eapply peutt_state_hitting_lift;
        [exact H0|apply handler_complete_front_hitting|apply handler_complete_front_hitting].
    + intros h1 h2 Hheads. inversion Hheads; subst; apply sem_lift_ret;
        cbn [source_front_result stable_target_rel]; constructor; assumption.
  - eapply Hbind.
    + apply sem_lift_refl. intro h. reflexivity.
    + intros h h' ->. apply sem_lift_ret. apply handler_front_result_related. exact H0.
Qed.

Variable Hzero : relational_zero FO.

Theorem handler_machine_finite_related fuel c d :
  handler_config_rel c d ->
  sem_lift heads_rel
    (stable_hitting_approx (handler_machine_kernel handler) fuel c)
    (stable_hitting_approx (handler_machine_kernel handler) fuel d).
Proof.
  apply (stable_hitting_approx_rel Hbind Hzero).
  exact handler_machine_kernel_related.
Qed.

Variable Hlimit : relational_lub FO.

(** Non-circular collapse: arbitrarily many internally returning handled
    events are traversed by finite kernel induction and an increasing lub,
    NOT by invoking target peutt before a visible guard. *)
Theorem handler_machine_complete_related c d mu nu :
  handler_config_rel c d ->
  stable_hitting (handler_machine_kernel handler) c mu ->
  stable_hitting (handler_machine_kernel handler) d nu ->
  sem_lift heads_rel mu nu.
Proof.
  apply (stable_hitting_rel Hbind Hzero handler_machine_kernel_related Hlimit).
Qed.
End HandlerMachineSimulation.
