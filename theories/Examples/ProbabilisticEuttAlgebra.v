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

Variant sourceE : Type -> Type :=
  | AskBit : sourceE bool.

Definition bit_handler (X : Type) (e : sourceE X) : ptree algebraE Enum X :=
  match e with
  | AskBit => Tau (Ret true)
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
