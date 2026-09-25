(** Role: Interpreter compositionality. Depends on equational theory (and comparison semantics for Atomic/MDP); not primitive syntax. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Program Require Import Equality.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Eq.FreeOmega Require Import Base Bind.
From PTree.Interp.FreeOmega Require Import Base Guarded.
From PTree.Semantics Require Import HeadTransition TreeTransition TreeTransitionBisim.
Require Import PTree.Interp.Kernel.
From PTree.Interp.FreeOmega Require Import Cofinality.
Require PTree.Interp.Atomic.
From PTree.Prob.FreeOmega Require Import Coupling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AtomicInterp.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI} `{NO : @SemanticOmega MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NC := NC) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation hits t out := (@ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure FO _ (observe t) out).
Variable handler : forall X, E X -> ptree E MN X.

(** An explicit semantic certificate, not a typeclass or a necessary
    characterization. This first profile preserves response values and
    permits event permutations, not event merging. Both internal segments
    have complete Dirac behavior; no finite-fuel or syntactic constraint
    is imposed. In particular a second visible interaction is excluded. *)
Record atomic_handler := {
  atomic_rename : forall X, E X -> E X;
  atomic_unrename : forall X, E X -> E X;
  atomic_unrename_rename : forall X (e : E X), atomic_unrename (atomic_rename e) = e;
  atomic_rename_unrename : forall X (e : E X), atomic_rename (atomic_unrename e) = e;
  atomic_cont : forall X, E X -> X -> ptree E MN X;
  atomic_start : forall X (e : E X),
    hits (handler e) (FORet (FHVis (atomic_rename e) (atomic_cont e)));
  atomic_finish : forall X (e : E X) x,
    hits (atomic_cont e x) (FORet (FHRet x))
}.

(** Preserve the established certificate API; its fields instantiate the
    generic certificate definitionally. No second atomicity proof. *)
Definition atomic_generic (a : atomic_handler) :
  PTree.Interp.Atomic.atomic_handler (MF := MF) handler :=
  {| PTree.Interp.Atomic.atomic_rename := atomic_rename a;
     PTree.Interp.Atomic.atomic_unrename := atomic_unrename a;
     PTree.Interp.Atomic.atomic_unrename_rename := atomic_unrename_rename a;
     PTree.Interp.Atomic.atomic_rename_unrename := atomic_rename_unrename a;
     PTree.Interp.Atomic.atomic_cont := atomic_cont a;
     PTree.Interp.Atomic.atomic_start := atomic_start a;
     PTree.Interp.Atomic.atomic_finish := atomic_finish a |}.

Local Lemma atomic_bind_ret A (mu : MF A) :
  @sem_eq MF FI _ (sem_bind mu sem_ret) mu.
Proof. apply FOQLStructural, free_omega_bind_return_lift. Qed.

Local Lemma atomic_bind_ret_l A B (x : A) (k : A -> MF B) :
  @sem_eq MF FI _ (sem_bind (sem_ret x) k) (k x).
Proof. apply (sem_eq_refl (SI := FI)). Qed.

Local Lemma atomic_limit_proper A (c : nat -> MF A) mu nu :
  @sem_eq MF FI _ mu nu ->
  @sem_lub MF FI FO _ c mu -> @sem_lub MF FI FO _ c nu.
Proof. apply free_omega_observable_lub_limit_proper. Qed.

Variable atom : atomic_handler.

Lemma atomic_handler_guarded : guarded_handler (NI := NI) (NO := NO) handler.
Proof.
  exact (PTree.Interp.Atomic.atomic_handler_guarded
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
     (atomic_generic atom)).
Qed.

Definition atomic_label (label : obs_label E) : obs_label E :=
  match label with @Obs _ X e x => Obs (atomic_rename atom e) x end.
Definition atomic_unlabel (label : obs_label E) : obs_label E :=
  match label with @Obs _ X e x => Obs (atomic_unrename atom e) x end.
Lemma atomic_label_unlabel label : atomic_label (atomic_unlabel label) = label.
Proof. destruct label. cbn. rewrite atomic_rename_unrename. reflexivity. Qed.
Lemma atomic_unlabel_label label : atomic_unlabel (atomic_label label) = label.
Proof. destruct label. cbn. rewrite atomic_unrename_rename. reflexivity. Qed.

Definition atomic_offer (o : offered_event E) : offered_event E :=
  match o with @Offered _ X e => Offered (atomic_rename atom e) end.

Section Result.
Context {R : Type}.
Local Notation tree := (ptree E MN R).
Local Notation head := (stable_head E MN R).

Definition atomic_head (h : head) : head :=
  match h with
  | FHRet r => FHRet r
  | @FHVis _ _ _ X e k => FHVis (atomic_rename atom e)
      (fun x => PTree.bind (atomic_cont atom e x) (fun a => PTree.interp handler (k a)))
  end.
Definition atomic_map (mu : MF head) : MF head :=
  free_omega_bind mu (fun h => FORet (atomic_head h)).
Definition atomic_head_graph (h k : head) : Prop := k = atomic_head h.

Lemma atomic_map_lift mu : @sem_lift MF FI _ _ atomic_head_graph mu (atomic_map mu).
Proof.
  (** Keep this old helper's weaker native signature: the primitive quotient
      bind rule needs no native AELift capability. *)
  unfold atomic_map.
  eapply FOQLComp with (T := eq) (U := atomic_head_graph)
    (mid := free_omega_bind mu (fun x => FORet x)).
  - apply (sem_eq_sym (SI := FI)), FOQLStructural, free_omega_bind_return_lift.
  - eapply FOQLBind.
    + apply free_omega_qlift_refl. intro x. reflexivity.
    + intros x y ->. apply FOQLStructural, FOLRet. reflexivity.
  - intros x z [y [-> H]]. exact H.
Qed.

Lemma atomic_interp_head_hitting h :
  hits (ptree_interp_head_tree handler h) (FORet (atomic_head h)).
Proof.
  exact (PTree.Interp.Atomic.atomic_interp_head_hitting
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    atomic_limit_proper (atomic_generic atom) h).
Qed.

Lemma atomic_interp_hitting (t : tree) mu :
  hits t mu -> hits (PTree.interp handler t) (atomic_map mu).
Proof.
  exact (PTree.Interp.Atomic.atomic_interp_hitting
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    atomic_limit_proper (atomic_generic atom) (t := t) (mu := mu)).
Qed.

Lemma atomic_finish_bind {X} (e : E X) x (k : X -> tree) mu :
  hits (k x) mu -> hits (PTree.bind (atomic_cont atom e x) k) mu.
Proof.
  exact (PTree.Interp.Atomic.atomic_finish_bind_of_ret_l
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    atomic_limit_proper (atomic_generic atom) atomic_bind_ret_l e (x := x) (k := k) (mu := mu)).
Qed.

(** This normalization relation mentions complete hitting only, never a
    preservation theorem. It also covers the selected successor heads. *)
Definition atomic_normalizes (target source : tree) : Prop :=
  exists mu, hits source mu /\ hits target (atomic_map mu).

Lemma atomic_normalizes_interp t : atomic_normalizes (PTree.interp handler t) t.
Proof.
  exact (PTree.Interp.Atomic.atomic_normalizes_interp
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    atomic_limit_proper (atomic_generic atom) t).
Qed.

Lemma atomic_normalizes_head h :
  atomic_normalizes (stable_head_tree (atomic_head h)) (stable_head_tree h).
Proof.
  exact (PTree.Interp.Atomic.atomic_normalizes_head
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    atomic_limit_proper (atomic_generic atom) h).
Qed.

Lemma atomic_normalizes_heads target source mu nu :
  atomic_normalizes target source -> hits source mu -> hits target nu ->
  @sem_lift MF FI _ _ atomic_head_graph mu nu.
Proof.
  intros [front [Hs Ht]] Hmu Hnu.
  eapply sem_lift_proper_l.
  - eapply stable_hitting_unique; [exact Hs|exact Hmu].
  - eapply sem_lift_proper_r.
    + eapply stable_hitting_unique; [exact Ht|exact Hnu].
    + apply atomic_map_lift.
Qed.

Definition atomic_unhead (h : head) : head :=
  match h with FHRet r => FHRet r |
    @FHVis _ _ _ X e k => FHVis (atomic_unrename atom e) k end.

Lemma atomic_unhead_enabled h label : head_enabled h label ->
  head_enabled (atomic_unhead h) (atomic_unlabel label).
Proof. intro H. destruct H. constructor. Qed.

Lemma atomic_enabled h label :
  head_enabled (atomic_head h) (atomic_label label) -> head_enabled h label.
Proof.
  intro H. pose proof (atomic_unhead_enabled H) as Hb.
  rewrite atomic_unlabel_label in Hb.
  destruct h as [r|X e k]; cbn [atomic_unhead atomic_head] in Hb.
  - inversion Hb.
  - rewrite atomic_unrename_rename in Hb. dependent destruction Hb. constructor.
Qed.

Lemma atomic_action_result h label out :
  @head_action_result E MN MF FI FreeOmegaMixedMeasure FO R label h out ->
  @head_action_result E MN MF FI FreeOmegaMixedMeasure FO R
    (atomic_label label) (atomic_head h) (atomic_map out).
Proof.
  exact (PTree.Interp.Atomic.atomic_action_result
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    atomic_limit_proper (atomic_generic atom) (h := h) (label := label) (out := out)).
Qed.

Lemma atomic_action_lift h label mu nu :
  @head_action_result E MN MF FI FreeOmegaMixedMeasure FO R label h mu ->
  @head_action_result E MN MF FI FreeOmegaMixedMeasure FO R
    (atomic_label label) (atomic_head h) nu ->
  @sem_lift MF FI _ _ atomic_head_graph mu nu.
Proof.
  exact (PTree.Interp.Atomic.atomic_action_lift
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    atomic_bind_ret atomic_limit_proper (atom := atomic_generic atom) (h := h) (label := label) (mu := mu) (nu := nu)).
Qed.

Lemma atomic_normalizes_trans target source label mu nu :
  atomic_normalizes target source ->
  @tree_trans E MN MF FI FreeOmegaMixedMeasure FO R source label mu ->
  @tree_trans E MN MF FI FreeOmegaMixedMeasure FO R target (atomic_label label) nu ->
  @sem_lift MF FI _ _ atomic_head_graph mu nu.
Proof.
  exact (PTree.Interp.Atomic.atomic_normalizes_trans
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    atomic_bind_ret atomic_limit_proper (atom := atomic_generic atom) (target := target) (source := source) (label := label) (mu := mu) (nu := nu)).
Qed.

Lemma atomic_normalizes_projects {O1 O2} (OR : O1 -> O2 -> Prop)
    (p1 : head -> MF O1) (p2 : head -> MF O2)
    (Hp : forall h, @sem_lift MF FI _ _ OR (p1 h) (p2 (atomic_head h)))
    target source mu nu :
  atomic_normalizes target source ->
  @tree_head_observation E MN MF FI FreeOmegaMixedMeasure FO R _ p1 source mu ->
  @tree_head_observation E MN MF FI FreeOmegaMixedMeasure FO R _ p2 target nu ->
  @sem_lift MF FI _ _ OR mu nu.
Proof.
  exact (PTree.Interp.Atomic.atomic_normalizes_projects
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    atomic_bind_ret (atom := atomic_generic atom) (OR := OR) (p1 := p1) (p2 := p2) Hp (target := target) (source := source) (mu := mu) (nu := nu)).
Qed.

Lemma atomic_normalizes_returns target source mu nu :
  atomic_normalizes target source ->
  @tree_return_observation E MN MF FI FreeOmegaMixedMeasure FO R source mu ->
  @tree_return_observation E MN MF FI FreeOmegaMixedMeasure FO R target nu ->
  @sem_lift MF FI _ _ (fun r s => s = r) mu nu.
Proof.
  exact (PTree.Interp.Atomic.atomic_normalizes_returns
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    atomic_bind_ret (atom := atomic_generic atom) (target := target) (source := source) (mu := mu) (nu := nu)).
Qed.

Lemma atomic_normalizes_offers target source mu nu :
  atomic_normalizes target source ->
  @tree_offered_event_observation E MN MF FI FreeOmegaMixedMeasure FO R source mu ->
  @tree_offered_event_observation E MN MF FI FreeOmegaMixedMeasure FO R target nu ->
  @sem_lift MF FI _ _ (fun e f => f = atomic_offer e) mu nu.
Proof.
  exact (PTree.Interp.Atomic.atomic_normalizes_offers
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    atomic_bind_ret (atom := atomic_generic atom) (target := target) (source := source) (mu := mu) (nu := nu)).
Qed.

(** Push a source coupling across two graph couplings. This is ordinary
    coupling composition, not a whole-continuation comparison. *)
Lemma atomic_couple {A B} (f : A -> B) (AR : A -> A -> Prop) (BR : B -> B -> Prop)
    s1 s2 t1 t2 :
  @sem_lift MF FI _ _ (fun a b => b = f a) s1 t1 ->
  @sem_lift MF FI _ _ AR s1 s2 ->
  @sem_lift MF FI _ _ (fun a b => b = f a) s2 t2 ->
  (forall a b, AR a b -> BR (f a) (f b)) -> @sem_lift MF FI _ _ BR t1 t2.
Proof.
  exact (PTree.Interp.Atomic.atomic_couple (FI := FI)
    (f := f) (AR := AR) (BR := BR) (s1 := s1) (s2 := s2) (t1 := t1) (t2 := t2)).
Qed.

Variable RR : R -> R -> Prop.
Local Notation TB := (@tree_trans_bisim E MN MF FI FC FreeOmegaMixedMeasure FO R R RR).

Definition atomic_candidate (t u : tree) : Prop :=
  exists s v, atomic_normalizes t s /\ atomic_normalizes u v /\ TB s v.

Lemma atomic_candidate_postfixed t u : atomic_candidate t u ->
  @tree_trans_bisimF E MN MF FI FreeOmegaMixedMeasure FO R R RR atomic_candidate t u.
Proof.
  exact (PTree.Interp.Atomic.atomic_candidate_postfixed
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    atomic_bind_ret atomic_limit_proper (atom := atomic_generic atom) (RR := RR) (t := t) (u := u)).
Qed.

Theorem tree_trans_bisim_interp_atomic (t u : tree) :
  TB t u -> TB (PTree.interp handler t) (PTree.interp handler u).
Proof.
  exact (PTree.Interp.Atomic.tree_trans_bisim_interp_atomic
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    atomic_bind_ret atomic_limit_proper (atomic_generic atom) (RR := RR) (t := t) (u := u)).
Qed.

End Result.
End AtomicInterp.
