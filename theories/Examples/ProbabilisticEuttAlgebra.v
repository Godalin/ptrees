Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Morphisms.
From mathcomp Require Import eqtype.
From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC FrontierLift FrontierLiftEnum
  TwoLevelMeasure TwoLevelMeasureEnum
  FreeOmegaMeasure MeasureIterationEnum.
From PTree.Eq Require Import OperationalProbabilisticPTS
  OperationalProbabilisticPTSFreeOmega ProbabilisticEutt PStrong.
From PTree.Examples Require Import EnumMeasureRegression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.

Variant algebraE : Type -> Type := .
Local Notation MF := (FreeOmega Enum).
Local Notation peutt :=
  (@probabilistic_eutt algebraE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface).

(** Regression: all three monad equations elaborate at the canonical
    FreeOmega endpoint. *)
Lemma canonical_monad_laws_regression {A B C}
    (a : A) (t : ptree algebraE Enum A)
    (k : A -> ptree algebraE Enum B)
    (h : B -> ptree algebraE Enum C) :
  peutt eq (PTree.bind (Ret a) k) (k a) /\
  peutt eq (PTree.bind t (fun x => Ret x)) t /\
  peutt eq
    (PTree.bind (PTree.bind t k) h)
    (PTree.bind t (fun x => PTree.bind (k x) h)).
Proof.
  repeat split.
  - apply free_probabilistic_eutt_bind_ret_l.
  - apply free_probabilistic_eutt_bind_ret_r.
  - apply free_probabilistic_eutt_bind_assoc.
Qed.

(** Regression: the bind [Proper] instance supports rewriting a canonical
    equivalence underneath a continuation. *)
Lemma canonical_bind_setoid_rewrite {A B}
    (t1 t2 : ptree algebraE Enum A)
    (k : A -> ptree algebraE Enum B) :
  peutt eq t1 t2 ->
  peutt eq (PTree.bind t1 k) (PTree.bind t2 k).
Proof.
  intro Ht. setoid_rewrite Ht. reflexivity.
Qed.

Lemma canonical_fmap_laws_regression {A B C}
    (f : A -> B) (g : B -> C) (t : ptree algebraE Enum A) :
  peutt eq (PTree.fmap (fun x => x) t) t /\
  peutt eq (PTree.fmap g (PTree.fmap f t))
    (PTree.fmap (fun x => g (f x)) t).
Proof.
  split.
  - apply free_probabilistic_eutt_fmap_id.
  - apply free_probabilistic_eutt_fmap_compose.
Qed.

(** Regression: the Functor [Proper] instance is registered with the setoid
    machinery, not merely available as a manually applied theorem. *)
Lemma canonical_fmap_setoid_rewrite {A B}
    (f : A -> B) (t1 t2 : ptree algebraE Enum A) :
  peutt eq t1 t2 -> peutt eq (PTree.fmap f t1) (PTree.fmap f t2).
Proof.
  intro Ht. setoid_rewrite Ht. reflexivity.
Qed.

(** Dirac elimination uses the explicit node-Dirac/mixed-unit capability of
    the Enum-to-FreeOmega backend. *)
Lemma canonical_prob_ret_regression {X R}
    (x : X) (k : X -> ptree algebraE Enum R) :
  peutt eq (Prob (ret_Enum x) k) (k x).
Proof.
  change (peutt eq
    (Prob (@sem_ret Enum Enum_SemanticMeasureInterface X x) k) (k x)).
  apply probabilistic_eutt_prob_ret.
Qed.

Lemma canonical_prob_flatten_regression {X Y R}
    (mu : Enum X) (h : X -> Enum Y)
    (k : Y -> ptree algebraE Enum R) :
  peutt eq
    (Prob mu (fun x => Prob (h x) k))
    (Prob (bind_Enum mu h) k).
Proof.
  change (peutt eq
    (Prob mu (fun x => Prob (h x) k))
    (Prob (@sem_bind Enum Enum_SemanticMeasureInterface X Y mu h) k)).
  apply probabilistic_eutt_prob_flatten.
Qed.

(** Measure rewriting uses coupling equality, so a split representation of
    the fair distribution rewrites under [Prob] without list equality. *)
Lemma canonical_prob_measure_setoid_rewrite {R}
    (k : bool -> ptree algebraE Enum R) :
  peutt eq (Prob reg_fair k) (Prob reg_fair_split k).
Proof.
  set (sample := fun mu : Enum bool =>
    (Prob mu k : ptree algebraE Enum R)).
  change (peutt eq (sample reg_fair) (sample reg_fair_split)).
  assert (Hsample : Proper
      (@sem_lift Enum Enum_SemanticMeasureInterface bool bool eq ==>
       peutt eq) sample).
  { intros mu1 mu2 Hmu. unfold sample.
    apply probabilistic_eutt_prob_measure. exact Hmu. }
  setoid_rewrite reg_split_mass_lift_eq. reflexivity.
Qed.

Lemma enum_semantic_product_swap {X Y : eqType}
    (mu : Enum X) (nu : Enum Y) :
  @sem_lift Enum Enum_SemanticMeasureInterface _ _
    semantic_pair_swap_rel
    (semantic_product mu nu) (semantic_product nu mu).
Proof.
  change (@meas_lift Enum Enum_MeasureInterface _ _
    semantic_pair_swap_rel
    (bind_Enum mu (fun x => bind_Enum nu
      (fun y => ret_Enum (x, y))))
    (bind_Enum nu (fun y => bind_Enum mu
      (fun x => ret_Enum (y, x))))).
  refine (@meas_lift_bind_ret_exchange Enum Enum_MeasureInterface
    Enum_MeasureCommutativeLaws X Y (X * Y)%type (Y * X)%type
    (@semantic_pair_swap_rel X Y) mu nu
    (fun x y => (x, y)) (fun y x => (y, x)) _).
  intros x y. split; reflexivity.
Qed.

Lemma canonical_prob_interchange_regression {X Y : eqType} {R}
    (mu : Enum X) (nu : Enum Y)
    (k : X -> Y -> ptree algebraE Enum R) :
  peutt eq
    (Prob mu (fun x => Prob nu (fun y => k x y)))
    (Prob nu (fun y => Prob mu (fun x => k x y))).
Proof.
  eapply probabilistic_eutt_prob_interchange_of.
  apply free_omega_mixed_exchange_of_product.
  apply enum_semantic_product_swap.
Qed.

Lemma canonical_iter_unfold_regression {I R}
    (step : I -> ptree algebraE Enum (I + R)) (i : I) :
  peutt eq (PTree.iter step i)
    (PTree.bind (step i) (fun lr =>
      match lr with
      | inl i' => Tau (PTree.iter step i')
      | inr r => Ret r
      end)).
Proof. apply free_probabilistic_eutt_iter_unfold. Qed.

Lemma canonical_iter_structural_regression {I R}
    (step1 step2 : I -> ptree algebraE Enum (I + R)) (i : I) :
  (forall j, pstructural eq (step1 j) (step2 j)) ->
  peutt eq (PTree.iter step1 i) (PTree.iter step2 i).
Proof. apply free_probabilistic_eutt_iter_structural. Qed.

Definition countdown_nat (n : nat) :
    ptree algebraE Enum (nat + nat) :=
  match n with
  | O => Ret (inr O)
  | S n' => Ret (inl n')
  end.

Definition countdown_tagged (s : nat * unit) :
    ptree algebraE Enum ((nat * unit) + bool) :=
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
  eapply free_probabilistic_eutt_iter_rel
    with (SI := countdown_state_rel).
  - intros i1 [i2 []] Hi. cbn in Hi. inversion Hi; subst. destruct i2; cbn.
    + apply pstructural_fold. cbn. constructor. constructor. split; reflexivity.
    + apply pstructural_fold. cbn. constructor. constructor. reflexivity.
  - reflexivity.
Qed.

Definition retry_next (b : bool) : unit + bool :=
  if b then inr true else inl tt.

Definition retry_step_left (_ : unit) :
    ptree algebraE Enum (unit + bool) :=
  Tau (Prob reg_fair (fun b => Ret (retry_next b))).

Definition retry_step_right (_ : unit) :
    ptree algebraE Enum (unit + bool) :=
  Prob reg_fair (fun b => Tau (Ret (retry_next b))).

Lemma retry_steps_behaviorally_related u1 u2 :
  eq u1 u2 ->
  peutt (free_iter_behavioral_sum_rel eq eq)
    (retry_step_left u1) (retry_step_right u2).
Proof.
  intros ->. unfold retry_step_left, retry_step_right.
  eapply probabilistic_eutt_rel_mono with (RR := eq).
  - intros x y ->. destruct y as [[]|b]; reflexivity.
  - eapply probabilistic_eutt_trans.
    + apply probabilistic_eutt_tau_l.
    + eapply probabilistic_eutt_prob with (XR := eq).
      * apply sem_lift_refl. intro b. reflexivity.
      * intros b1 b2 ->. apply probabilistic_eutt_tau_r.
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
  eapply free_probabilistic_eutt_iter_behavioral_rel with (SI := eq).
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
    (t : ptree sourceE Enum R) :
  @probabilistic_eutt finalE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.translate rename_get (PTree.translate rename_bit t))
    (PTree.translate
      (fun (X : Type) (e : sourceE X) =>
        @rename_get X (@rename_bit X e)) t).
Proof. apply free_probabilistic_eutt_translate_compose. Qed.

(** Identity interpretation is genuinely weak on this program: interpreting
    [GetBit] inserts an administrative Tau before the visible event. *)
Lemma canonical_interp_trigger_regression {R}
    (k : bool -> ptree renamedE Enum R) :
  @probabilistic_eutt renamedE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.interp (fun X e => @PTree.trigger renamedE Enum X e)
      (Vis GetBit k))
    (Vis GetBit k).
Proof. apply free_probabilistic_eutt_interp_trigger. Qed.

Definition bit_handler (X : Type) (e : sourceE X) : ptree algebraE Enum X :=
  match e with
  | AskBit => Tau (Ret true)
  end.

Definition bit_forward_handler (X : Type) (e : sourceE X) :
    ptree renamedE Enum X :=
  match e with
  | AskBit => Tau (Vis GetBit (fun b => Ret b))
  end.

Definition renamed_prob_handler (X : Type) (e : renamedE X) :
    ptree algebraE Enum X :=
  match e with
  | GetBit => Prob (ret_Enum true) (fun b => Ret b)
  end.

Definition bit_handler_eta (X : Type) (e : sourceE X) :
    ptree algebraE Enum X :=
  match e with
  | AskBit => Tau (PTree.bind (Ret true) (fun b => Ret b))
  end.

(** Regression: a visible source interaction is replaced by a target-side
    computation, and the heterogeneous continuation relation is retained. *)
Lemma canonical_interp_structural_regression
    (k1 k2 : bool -> ptree sourceE Enum nat) :
  (forall b, pstructural (fun n m => n = S m) (k1 b) (k2 b)) ->
  peutt (fun n m => n = S m)
    (PTree.interp bit_handler (Vis AskBit k1))
    (PTree.interp bit_handler (Vis AskBit k2)).
Proof.
  intro Hk. apply free_probabilistic_eutt_interp_structural.
  apply pstructural_fold. cbn. constructor. exact Hk.
Qed.

Lemma canonical_interp_bind_regression {A B}
    (t : ptree sourceE Enum A) (k : A -> ptree sourceE Enum B) :
  peutt eq
    (PTree.interp bit_handler (PTree.bind t k))
    (PTree.bind (PTree.interp bit_handler t)
      (fun x => PTree.interp bit_handler (k x))).
Proof. apply free_probabilistic_eutt_interp_bind. Qed.

Definition interactive_loop_step (state : bool) :
    ptree sourceE Enum (bool + bool) :=
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
Proof. apply free_probabilistic_eutt_interp_iter. Qed.

(** Both layers are operationally nontrivial: the first handler contributes
    Tau and Vis, while the second replaces that Vis by a probabilistic node. *)
Lemma canonical_interp_compose_regression {R} (t : ptree sourceE Enum R) :
  peutt eq
    (PTree.interp renamed_prob_handler
      (PTree.interp bit_forward_handler t))
    (PTree.interp
      (fun (X : Type) (e : sourceE X) =>
        PTree.interp renamed_prob_handler (@bit_forward_handler X e)) t).
Proof. apply free_probabilistic_eutt_interp_compose. Qed.

Lemma bit_handlers_structurally_related X (e : sourceE X) :
  pstructural eq (@bit_handler X e) (@bit_handler_eta X e).
Proof.
  destruct e. apply pstructural_fold. cbn. constructor.
  apply pstructural_fold. cbn. constructor. reflexivity.
Qed.

(** Handler replacement is not definitional: the right handler contains an
    extra monadic redex under Tau. *)
Lemma canonical_interp_handler_regression {R} (t : ptree sourceE Enum R) :
  peutt eq (PTree.interp bit_handler t) (PTree.interp bit_handler_eta t).
Proof.
  apply free_probabilistic_eutt_interp_handler.
  exact bit_handlers_structurally_related.
Qed.

Lemma canonical_translate_preservation_regression {A B}
    (RR : A -> B -> Prop)
    (t1 : ptree sourceE Enum A) (t2 : ptree sourceE Enum B) :
  @probabilistic_eutt sourceE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A B RR t1 t2 ->
  @probabilistic_eutt renamedE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A B RR
    (PTree.translate rename_bit t1) (PTree.translate rename_bit t2).
Proof. apply free_probabilistic_eutt_translate. Qed.

Lemma canonical_translate_setoid_rewrite {A}
    (t1 t2 : ptree sourceE Enum A) :
  @probabilistic_eutt sourceE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A A eq t1 t2 ->
  @probabilistic_eutt renamedE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A A eq
    (PTree.translate rename_bit t1) (PTree.translate rename_bit t2).
Proof.
  intro Ht. setoid_rewrite Ht. reflexivity.
Qed.
