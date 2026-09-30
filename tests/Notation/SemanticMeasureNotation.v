(** Opt-in semantic algebra: expansions, inference and scope separation.
    This compilation client adds no mathematical assumptions or instances. *)
Set Universe Polymorphism.
From PTree.Prob.Interface Require Import Measure Omega.

Fail Check FreeOmega.
Fail Check ptree.

Import SemanticMeasureNotations SemanticOmegaNotations.
Fail Check (ηₘ tt).

Section Generic.
Context {M : Type -> Type} {MI : SemanticMeasure M}.
Context {MO : @SemanticOmega M MI}.

Example delimited_return {A} (a : A) : (ηₘ a)%sm = @sem_ret M MI A a.
Proof. reflexivity. Qed.

Local Open Scope semantic_measure_scope.

Example return_expansion {A} (a : A) : ηₘ a = @sem_ret M MI A a.
Proof. reflexivity. Qed.
Example bind_expansion {A B} (mu : M A) (k : A -> M B) :
  mu >>=ₘ k = @sem_bind M MI A B mu k.
Proof. reflexivity. Qed.
Example bind_associates_left {A B C} (mu : M A)
    (k : A -> M B) (h : B -> M C) :
  mu >>=ₘ k >>=ₘ h = sem_bind (sem_bind mu k) h.
Proof. reflexivity. Qed.
Example equality_expansion {A} (mu nu : M A) :
  (mu ≈ₘ nu) = (@sem_eq M MI A mu nu).
Proof. reflexivity. Qed.
Example heterogeneous_lifting {A B} (RR : A -> B -> Prop) (mu : M A) (nu : M B) :
  (mu ≈[RR]ₘ nu) = (@sem_lift M MI A B RR mu nu).
Proof. reflexivity. Qed.
Example relation_expression {A} (mu nu : M A) :
  (mu ≈[fun x y => x = y]ₘ nu) = (sem_lift eq mu nu).
Proof. reflexivity. Qed.
Example zero_expansion {A} : (⊥ₘ : M A) = @sem_zero M MI MO A.
Proof. reflexivity. Qed.
Example order_expansion {A} (mu nu : M A) :
  (mu ≤ₘ nu) = (@sem_le M MI MO A mu nu).
Proof. reflexivity. Qed.
Example lub_expansion {A} (chain : nat -> M A) (out : M A) :
  (chain ⇑ₘ out) = (@sem_lub M MI MO A chain out).
Proof. reflexivity. Qed.

Example left_unit {BL : @SemanticMeasureBindLaws M MI}
    {A B} (a : A) (k : A -> M B) :
  ηₘ a >>=ₘ k ≈ₘ k a.
Proof. apply sem_bind_ret_l. Qed.

(** A lub assertion is a proposition, not a value or a chain certificate. *)
Example lub_is_a_relation {A} (c : nat -> M A) : M A -> Prop := fun out => c ⇑ₘ out.
End Generic.

Fail Check (ηₘ tt).

Section HighCarrier.
Universe low high rep.
Constraint low < high.
Context {M : Type@{high} -> Type@{rep}} {MI : SemanticMeasure M}.
Example type_as_value (A : Type@{low}) :
  (ηₘ A : M Type@{low})%sm = sem_ret A.
Proof. reflexivity. Qed.
End HighCarrier.

From PTree Require Import PTree.
Require Import PTree.Prob.FreeOmega.Definition.
From ITree.Basics Require Import Monad.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope freeomega_scope.
Local Open Scope semantic_measure_scope.

(** The semantic notation has no hardwired FreeOmega or PTree instance. *)
Example native_and_raw {MN A} {NI : SemanticMeasure MN} (a : A) :
  (x <~ (ηₘ a : MN A) ;; η x) = FOSample (sem_ret a) (fun x => FORet x).
Proof. reflexivity. Qed.
Example program_bind_unchanged {E MN A} (mu : MN A) :
  (x <- sample mu ;; Ret x) =
  @PTree.bind E MN A A (sample mu) (fun x => Ret x).
Proof. reflexivity. Qed.

Local Close Scope semantic_measure_scope.
Fail Check (ηₘ tt).
Example raw_scope_still_open {MN A} (a : A) : η a = @FORet MN A a.
Proof. reflexivity. Qed.
