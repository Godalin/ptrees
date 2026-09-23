(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Morphisms.
From mathcomp Require Import eqtype.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.EnumQ.Representation.
From PTree.Prob.Interface Require Import FrontierLift.
Require Import PTree.Prob.Backend.EnumQ.FrontierLift.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.EnumQ.Iteration.
From PTree.Eq Require Import PTreeKernel ProbabilisticTrace.
From PTree.Eq.FreeOmega Require Import Base Hitting Relation Bind Algebra Iter.
From PTree.Interp.FreeOmega Require Import Base Guarded.
From PTree.Eq Require Import PEutt PStruct PStrong.
From PTree.Regression.Backend Require Import EnumQMeasureRegression.
Require Import PTree.Interp.FreeOmega.Translate.
Require Import PTree.Interp.Kernel.

From PTree.Interp.FreeOmega Require Import Cofinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.

Variant algebraE : Type -> Type := .
Local Notation MF := (FreeOmega EnumQ).
Local Notation peutt :=
  (@PEutt.peutt algebraE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega).

(** Pin this regression's observable profile before setoid search. These are
    local specializations of the single generic proofs, not backend laws. *)
#[local] Instance regression_bind_Proper {A B} :
  Proper (peutt eq ==> pointwise_relation A (peutt eq) ==> peutt eq)
    (@PTree.bind algebraE EnumQ A B).
Proof. apply peutt_bind_Proper. Qed.

#[local] Instance regression_fmap_Proper {A B} (f : A -> B) :
  Proper (peutt eq ==> peutt eq) (@PTree.fmap algebraE EnumQ A B f).
Proof. apply peutt_fmap_Proper. Qed.

(** Regression: all three monad equations elaborate at the canonical
    FreeOmega endpoint. *)
Lemma canonical_monad_laws_regression {A B C}
    (a : A) (t : ptree algebraE EnumQ A)
    (k : A -> ptree algebraE EnumQ B)
    (h : B -> ptree algebraE EnumQ C) :
  peutt eq (PTree.bind (Ret a) k) (k a) /\
  peutt eq (PTree.bind t (fun x => Ret x)) t /\
  peutt eq
    (PTree.bind (PTree.bind t k) h)
    (PTree.bind t (fun x => PTree.bind (k x) h)).
Proof.
  repeat split.
  - apply peutt_bind_ret_l.
  - apply peutt_bind_ret_r.
  - apply peutt_bind_assoc.
Qed.

(** Regression: the bind [Proper] instance supports rewriting a canonical
    equivalence underneath a continuation. *)
Lemma canonical_bind_setoid_rewrite {A B}
    (t1 t2 : ptree algebraE EnumQ A)
    (k : A -> ptree algebraE EnumQ B) :
  peutt eq t1 t2 ->
  peutt eq (PTree.bind t1 k) (PTree.bind t2 k).
Proof.
  intro Ht. setoid_rewrite Ht. reflexivity.
Qed.

(** Both return carriers and both relations are independent. In particular
    no equivalence or reflexivity premise on either relation is available. *)
Section HeterogeneousBind.
Context {E : Type -> Type}.
Local Notation W := (@PEutt.peutt E EnumQ MF
  (FreeOmegaObservableSemanticMeasure
    (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega))
  FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
  FreeOmegaObservableSemanticOmega).

Lemma canonical_heterogeneous_bind {R1 R2 A B}
    (RR : R1 -> R2 -> Prop) (RS : A -> B -> Prop)
    (t1 : ptree E EnumQ R1) (t2 : ptree E EnumQ R2)
    (k1 : R1 -> ptree E EnumQ A) (k2 : R2 -> ptree E EnumQ B) :
  W RR t1 t2 ->
  (forall x y, RR x y -> W RS (k1 x) (k2 y)) ->
  W RS (PTree.bind t1 k1) (PTree.bind t2 k2).
Proof. apply Bind.peutt_bind. Qed.
End HeterogeneousBind.

Variant bindE : Type -> Type := BindAsk : bindE bool.
Local Notation bindW := (@PEutt.peutt bindE EnumQ MF
  (FreeOmegaObservableSemanticMeasure
    (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega))
  FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
  FreeOmegaObservableSemanticOmega).

Definition bind_source_rel (b : bool) (n : nat) :=
  n = if b then 1 else 0.
Definition bind_result_rel (n : nat) (b : bool) :=
  n = if b then 2 else 3.

(** A real probabilistic/eventful client: bool/nat at the source and
    nat/bool at the result, with different non-equality relations. *)
Example eventful_heterogeneous_bind :
  bindW bind_result_rel
    (PTree.bind
      (Vis BindAsk (fun _ => Prob reg_fair (fun b => Ret b)))
      (fun b => Tau (Ret (if b then 2 else 3))))
    (PTree.bind
      (Vis BindAsk (fun _ => Prob reg_fair
        (fun b => Ret (if b then 1 else 0))))
      (fun n => Ret (Nat.eqb n 1))).
Proof.
  eapply Bind.peutt_bind with (RR := bind_source_rel).
  - apply peutt_of_pstruct.
    apply pstruct_fold. constructor. intro response.
    apply pstruct_fold. constructor. intro b.
    apply pstruct_fold. constructor. reflexivity.
  - intros b n Hn. unfold bind_source_rel in Hn. subst n.
    eapply peutt_of_hitting_lift.
    + apply (proj2 (stable_hitting_tau_iff _ _)).
      apply stable_hitting_ret.
    + apply stable_hitting_ret.
    + apply sem_lift_ret. constructor. destruct b; reflexivity.
Qed.

Lemma canonical_fmap_laws_regression {A B C}
    (f : A -> B) (g : B -> C) (t : ptree algebraE EnumQ A) :
  peutt eq (PTree.fmap (fun x => x) t) t /\
  peutt eq (PTree.fmap g (PTree.fmap f t))
    (PTree.fmap (fun x => g (f x)) t).
Proof.
  split.
  - apply peutt_fmap_id.
  - apply peutt_fmap_compose.
Qed.

(** Regression: the Functor [Proper] instance is registered with the setoid
    machinery, not merely available as a manually applied theorem. *)
Lemma canonical_fmap_setoid_rewrite {A B}
    (f : A -> B) (t1 t2 : ptree algebraE EnumQ A) :
  peutt eq t1 t2 -> peutt eq (PTree.fmap f t1) (PTree.fmap f t2).
Proof.
  intro Ht. setoid_rewrite Ht. reflexivity.
Qed.

(** Dirac elimination uses the explicit node-Dirac/mixed-unit capability of
    the EnumQ-to-FreeOmega backend. *)
Lemma canonical_prob_ret_regression {X R}
    (x : X) (k : X -> ptree algebraE EnumQ R) :
  peutt eq (Prob (ret_EnumQ x) k) (k x).
Proof.
  change (peutt eq
    (Prob (@sem_ret EnumQ EnumQ_SemanticMeasure X x) k) (k x)).
  apply peutt_prob_ret.
Qed.

Lemma canonical_prob_flatten_regression {X Y R}
    (mu : EnumQ X) (h : X -> EnumQ Y)
    (k : Y -> ptree algebraE EnumQ R) :
  peutt eq
    (Prob mu (fun x => Prob (h x) k))
    (Prob (bind_EnumQ mu h) k).
Proof.
  change (peutt eq
    (Prob mu (fun x => Prob (h x) k))
    (Prob (@sem_bind EnumQ EnumQ_SemanticMeasure X Y mu h) k)).
  apply peutt_prob_flatten.
Qed.

(** Measure rewriting uses coupling equality, so a split representation of
    the fair distribution rewrites under [Prob] without list equality. *)
Lemma canonical_prob_measure_setoid_rewrite {R}
    (k : bool -> ptree algebraE EnumQ R) :
  peutt eq (Prob reg_fair k) (Prob reg_fair_split k).
Proof.
  set (sample := fun mu : EnumQ bool =>
    (Prob mu k : ptree algebraE EnumQ R)).
  change (peutt eq (sample reg_fair) (sample reg_fair_split)).
  assert (Hsample : Proper
      (@sem_lift EnumQ EnumQ_SemanticMeasure bool bool eq ==>
       peutt eq) sample).
  { intros mu1 mu2 Hmu. unfold sample.
    apply peutt_prob_measure. exact Hmu. }
  setoid_rewrite reg_split_mass_lift_eq. reflexivity.
Qed.

Lemma enumQ_semantic_product_swap {X Y : eqType}
    (mu : EnumQ X) (nu : EnumQ Y) :
  @sem_lift EnumQ EnumQ_SemanticMeasure _ _
    semantic_pair_swap_rel
    (semantic_product mu nu) (semantic_product nu mu).
Proof.
  change (@meas_lift EnumQ EnumQ_MeasureInterface _ _
    semantic_pair_swap_rel
    (bind_EnumQ mu (fun x => bind_EnumQ nu
      (fun y => ret_EnumQ (x, y))))
    (bind_EnumQ nu (fun y => bind_EnumQ mu
      (fun x => ret_EnumQ (y, x))))).
  refine (@meas_lift_bind_ret_exchange EnumQ EnumQ_MeasureInterface
    EnumQ_MeasureCommutativeLaws X Y (X * Y)%type (Y * X)%type
    (@semantic_pair_swap_rel X Y) mu nu
    (fun x y => (x, y)) (fun y x => (y, x)) _).
  intros x y. split; reflexivity.
Qed.

Lemma canonical_prob_interchange_regression {X Y : eqType} {R}
    (mu : EnumQ X) (nu : EnumQ Y)
    (k : X -> Y -> ptree algebraE EnumQ R) :
  peutt eq
    (Prob mu (fun x => Prob nu (fun y => k x y)))
    (Prob nu (fun y => Prob mu (fun x => k x y))).
Proof.
  eapply peutt_prob_interchange_of.
  apply free_omega_mixed_exchange_of_product.
  apply enumQ_semantic_product_swap.
Qed.

Lemma canonical_iter_unfold_regression {I R}
    (step : I -> ptree algebraE EnumQ (I + R)) (i : I) :
  peutt eq (PTree.iter step i)
    (PTree.bind (step i) (fun lr =>
      match lr with
      | inl i' => Tau (PTree.iter step i')
      | inr r => Ret r
      end)).
Proof. apply peutt_iter_unfold. Qed.

Lemma canonical_iter_structural_regression {I R}
    (step1 step2 : I -> ptree algebraE EnumQ (I + R)) (i : I) :
  (forall j, pstruct eq (step1 j) (step2 j)) ->
  peutt eq (PTree.iter step1 i) (PTree.iter step2 i).
Proof. apply peutt_iter_structural. Qed.

Variant naturalityE : Type -> Type :=
  | ReadFlag : naturalityE bool.

Local Notation naturality_peutt :=
  (@PEutt.peutt naturalityE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega).

Definition naturality_step (_ : unit) :
    ptree naturalityE EnumQ (unit + bool) :=
  Vis ReadFlag (fun observed =>
    Prob reg_fair (fun retry =>
      Ret (if retry then inl tt else inr observed))).

Definition naturality_post (b : bool) : ptree naturalityE EnumQ nat :=
  Tau (Ret (if b then 1 else 0)).

(** Naturality is exercised by an eventful, probabilistic, potentially
    unbounded retry loop; it is not merely a finite countdown equation. *)
Lemma canonical_iter_natural_regression :
  naturality_peutt eq
    (PTree.bind (PTree.iter naturality_step tt) naturality_post)
    (PTree.iter
      (pstruct_iter_natural_step (E := naturalityE) (M := EnumQ)
        naturality_step naturality_post) tt).
Proof. apply peutt_iter_natural. Qed.

Definition codiagonal_step (_ : unit) :
    ptree naturalityE EnumQ (unit + (unit + bool)) :=
  Vis ReadFlag (fun observed : bool =>
    Prob reg_fair (fun choose_inner : bool =>
      Ret ((if observed then
        if choose_inner then inl tt else inr (inl tt)
      else inr (inr false)) : unit + (unit + bool)))).

(** Both retry layers are live: the visible answer selects termination versus
    retry, while the fair sample selects an inner versus outer retry. *)
Lemma canonical_iter_codiagonal_regression :
  naturality_peutt eq
    (PTree.iter (fun j => PTree.iter codiagonal_step j) tt)
    (PTree.iter
      (pstruct_iter_codiagonal_flat_step codiagonal_step) tt).
Proof. apply peutt_iter_codiagonal. Qed.

Definition countdown_nat (n : nat) :
    ptree algebraE EnumQ (nat + nat) :=
  match n with
  | O => Ret (inr O)
  | S n' => Ret (inl n')
  end.

Definition countdown_tagged (s : nat * unit) :
    ptree algebraE EnumQ ((nat * unit) + bool) :=
  match fst s with
  | O => Ret (inr true)
  | S n' => Ret (inl (n', tt))
  end.

Definition countdown_state_rel (n : nat) (s : nat * unit) : Prop :=
  fst s = n.

Definition countdown_result_rel (n : nat) (b : bool) : Prop :=
  n = O /\ b = true.

(** A relational-fusion regression: the two loops have different state and
    result types, so this is not an instance of homogeneous congruence. *)
Lemma canonical_iter_rel_fusion_regression n :
  peutt countdown_result_rel
    (PTree.iter countdown_nat n)
    (PTree.iter countdown_tagged (n, tt)).
Proof.
  eapply peutt_iter_rel
    with (SI := countdown_state_rel).
  - intros i1 [i2 []] Hi. cbn in Hi. inversion Hi; subst. destruct i2; cbn.
    + apply pstruct_fold. cbn. constructor. constructor. split; reflexivity.
    + apply pstruct_fold. cbn. constructor. constructor. reflexivity.
  - reflexivity.
Qed.

Definition retry_next (b : bool) : unit + bool :=
  if b then inr true else inl tt.

Definition retry_step_left (_ : unit) :
    ptree algebraE EnumQ (unit + bool) :=
  Tau (Prob reg_fair (fun b => Ret (retry_next b))).

Definition retry_step_right (_ : unit) :
    ptree algebraE EnumQ (unit + bool) :=
  Prob reg_fair (fun b => Tau (Ret (retry_next b))).

Lemma retry_steps_behaviorally_related u1 u2 :
  eq u1 u2 ->
  peutt (iter_behavioral_sum_rel eq eq)
    (retry_step_left u1) (retry_step_right u2).
Proof.
  intros ->. unfold retry_step_left, retry_step_right.
  eapply peutt_rel_mono with (RR := eq).
  - intros x y ->. destruct y as [[]|b]; reflexivity.
  - eapply peutt_trans.
    + apply peutt_tau_l.
    + eapply peutt_prob with (XR := eq).
      * apply sem_lift_refl. intro b. reflexivity.
      * intros b1 b2 ->. apply peutt_tau_r.
Qed.

(** Behavioral rather than structural iteration congruence: Tau occurs
    outside the sample on the left and inside every sampled continuation on
    the right.  A false sample retries, so the number of loop rounds is
    unbounded. *)
Lemma canonical_iter_behavioral_retry_regression :
  peutt eq
    (PTree.iter retry_step_left tt)
    (PTree.iter retry_step_right tt).
Proof.
  eapply peutt_iter_behavioral_rel with (SI := eq).
  - intros X e. destruct e.
  - exact retry_steps_behaviorally_related.
  - reflexivity.
Qed.

Variant sourceE : Type -> Type :=
  | AskBit : sourceE bool.

Variant renamedE : Type -> Type :=
  | GetBit : renamedE bool.

Variant finalE : Type -> Type :=
  | ReadBit : finalE bool.

Definition rename_bit (X : Type) (e : sourceE X) : renamedE X :=
  match e with
  | AskBit => GetBit
  end.

Definition rename_get (X : Type) (e : renamedE X) : finalE X :=
  match e with
  | GetBit => ReadBit
  end.

Lemma canonical_translate_compose_regression {R}
    (t : ptree sourceE EnumQ R) :
  @PEutt.peutt finalE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R R eq
    (PTree.translate rename_get (PTree.translate rename_bit t))
    (PTree.translate
      (fun (X : Type) (e : sourceE X) =>
        @rename_get X (@rename_bit X e)) t).
Proof. apply peutt_translate_compose. Qed.

(** Identity interpretation is genuinely weak on this program: interpreting
    [GetBit] inserts an administrative Tau before the visible event. *)
Lemma canonical_interp_trigger_regression {R}
    (k : bool -> ptree renamedE EnumQ R) :
  @PEutt.peutt renamedE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R R eq
    (PTree.interp (fun X e => @PTree.trigger renamedE EnumQ X e)
      (Vis GetBit k))
    (Vis GetBit k).
Proof. apply peutt_interp_trigger. Qed.

Definition bit_handler (X : Type) (e : sourceE X) : ptree algebraE EnumQ X :=
  match e with
  | AskBit => Tau (Ret true)
  end.

Definition bit_forward_handler (X : Type) (e : sourceE X) :
    ptree renamedE EnumQ X :=
  match e with
  | AskBit => Tau (Vis GetBit (fun b => Ret b))
  end.

Definition renamed_prob_handler (X : Type) (e : renamedE X) :
    ptree algebraE EnumQ X :=
  match e with
  | GetBit => Prob (ret_EnumQ true) (fun b => Ret b)
  end.

Definition bit_handler_eta (X : Type) (e : sourceE X) :
    ptree algebraE EnumQ X :=
  match e with
  | AskBit => Tau (PTree.bind (Ret true) (fun b => Ret b))
  end.

(** Regression: a visible source interaction is replaced by a target-side
    computation, and the heterogeneous continuation relation is retained. *)
Lemma canonical_interp_structural_regression
    (k1 k2 : bool -> ptree sourceE EnumQ nat) :
  (forall b, pstruct (fun n m => n = S m) (k1 b) (k2 b)) ->
  peutt (fun n m => n = S m)
    (PTree.interp bit_handler (Vis AskBit k1))
    (PTree.interp bit_handler (Vis AskBit k2)).
Proof.
  intro Hk. apply peutt_interp_structural.
  apply pstruct_fold. cbn. constructor. exact Hk.
Qed.

(** The direct interpreter fuel chain is cofinal with the semantic
    source-head/handler diagonal for every source tree. *)
Lemma canonical_interp_cofinal_regression {R}
    (t : ptree sourceE EnumQ R) :
  @PTree.Interp.Kernel.ptree_interp_cofinal sourceE algebraE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R bit_handler t.
Proof. apply ptree_interp_cofinal_all. Qed.

Lemma canonical_interp_bind_regression {A B}
    (t : ptree sourceE EnumQ A) (k : A -> ptree sourceE EnumQ B) :
  peutt eq
    (PTree.interp bit_handler (PTree.bind t k))
    (PTree.bind (PTree.interp bit_handler t)
      (fun x => PTree.interp bit_handler (k x))).
Proof. apply peutt_interp_bind. Qed.

Definition interactive_loop_step (state : bool) :
    ptree sourceE EnumQ (bool + bool) :=
  Vis AskBit (fun answer : bool =>
    let next : bool + bool :=
      if answer then inr state else inl (negb state) in
    Ret next).

(** Regression: an eventful guarded loop can be interpreted either before
    or after forming the loop.  The handler contributes an administrative
    [Tau], so the two programs are not definitionally equal. *)
Lemma canonical_interp_iter_regression state :
  peutt eq
    (PTree.interp bit_handler (PTree.iter interactive_loop_step state))
    (PTree.iter
      (fun s => PTree.interp bit_handler (interactive_loop_step s)) state).
Proof. apply peutt_interp_iter. Qed.

(** Both layers are operationally nontrivial: the first handler contributes
    Tau and Vis, while the second replaces that Vis by a probabilistic node. *)
Lemma canonical_interp_compose_regression {R} (t : ptree sourceE EnumQ R) :
  peutt eq
    (PTree.interp renamed_prob_handler
      (PTree.interp bit_forward_handler t))
    (PTree.interp
      (fun (X : Type) (e : sourceE X) =>
        PTree.interp renamed_prob_handler (@bit_forward_handler X e)) t).
Proof. apply peutt_interp_compose. Qed.

Lemma bit_handlers_structurally_related X (e : sourceE X) :
  pstruct eq (@bit_handler X e) (@bit_handler_eta X e).
Proof.
  destruct e. apply pstruct_fold. cbn. constructor.
  apply pstruct_fold. cbn. constructor. reflexivity.
Qed.

(** Handler replacement is not definitional: the right handler contains an
    extra monadic redex under Tau. *)
Lemma canonical_interp_handler_regression {R} (t : ptree sourceE EnumQ R) :
  peutt eq (PTree.interp bit_handler t) (PTree.interp bit_handler_eta t).
Proof.
  apply peutt_interp_handler.
  exact bit_handlers_structurally_related.
Qed.

Lemma canonical_translate_preservation_regression {A B}
    (RR : A -> B -> Prop)
    (t1 : ptree sourceE EnumQ A) (t2 : ptree sourceE EnumQ B) :
  @PEutt.peutt sourceE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A B RR t1 t2 ->
  @PEutt.peutt renamedE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A B RR
    (PTree.translate rename_bit t1) (PTree.translate rename_bit t2).
Proof. apply peutt_translate. Qed.

Lemma canonical_translate_setoid_rewrite {A}
    (t1 t2 : ptree sourceE EnumQ A) :
  @PEutt.peutt sourceE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A A eq t1 t2 ->
  @PEutt.peutt renamedE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A A eq
    (PTree.translate rename_bit t1) (PTree.translate rename_bit t2).
Proof.
  intro Ht. setoid_rewrite Ht. reflexivity.
Qed.
