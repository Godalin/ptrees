(** Parsing, scope and universe contracts for opt-in client notation.
    These are definitional checks, not additional FreeOmega semantic laws. *)
Set Universe Polymorphism.
From Coq Require Import Utf8.
Require Import PTree.Prob.FreeOmega.Definition.

Fail Check (ηω tt).
Fail Check free_omega_qlift.
Fail Check FreeOmegaObservableSemanticMeasure.
Fail Check ptree.

Example delimited_return {MN A} (a : A) :
  (ηω a)%fo = @FORet MN A a.
Proof. reflexivity. Qed.

Example delimited_sample {MN A B} (mu : MN A) (k : A -> FreeOmega MN B) :
  (x ←ω mu ;; k x)%fo = FOSample mu k.
Proof. reflexivity. Qed.

Example delimited_bind {MN A B} (m : FreeOmega MN A) (k : A -> FreeOmega MN B) :
  (m >>=ω k)%fo = free_omega_bind m k.
Proof. reflexivity. Qed.

Example delimited_sup {MN A} (c : nat -> FreeOmega MN A) :
  (supω n, c n)%fo = FOLub c.
Proof. reflexivity. Qed.

Local Open Scope freeomega_scope.

(** Coq's logical binders compose with native sampling and formal limits;
    they elaborate to the same terms, not new probability operations. *)
Example utf8_sample_contract {MN A B} (mu : MN A) (k : A → FreeOmega MN B) :
  (∀ x, ∃ y, k x = ηω y) →
  ∃ out, out = (x ←ω mu ;; k x) ∧ out = FOSample mu k.
Proof. intros _. exists (FOSample mu k). split; reflexivity. Qed.

Example utf8_logic_expansion (P Q : Prop) {A} (x y : A) :
  (¬ P ∨ Q ↔ x ≠ y) = ((~ P \/ Q) <-> x <> y).
Proof. reflexivity. Qed.

Example utf8_nested_binders {MN A} (c : nat → MN A) :
  (∀ n, (x ←ω c n ;; ηω x) = ↑ω (c n)) ∧
  (supω n, ↑ω (c n)) = FOLub (fun n => free_omega_sample (c n)).
Proof. split; reflexivity. Qed.

(** Standard Utf8 lambdas keep the original binder and pattern semantics. *)
Example utf8_typed_lambda :
  (λ (A B : Type) (f : A → B) (x : A), f x) =
  (fun (A B : Type) (f : A → B) (x : A) => f x).
Proof. reflexivity. Qed.

Definition utf8_implicit_identity := λ {A : Type} (x : A), x.

Example utf8_implicit_lambda {A} (x : A) : utf8_implicit_identity x = x.
Proof. reflexivity. Qed.

Example utf8_pattern_lambda {A B} :
  ((λ '(x,y), (y,x)) : A * B → B * A) = (fun '(x,y) => (y,x)).
Proof. reflexivity. Qed.

Example utf8_lambda_match {MN A} (x : A) :
  (λ b, match b with true => ηω x | false => ⊥ω end) =
  (fun b => match b with true => @FORet MN A x | false => FOZero end).
Proof. reflexivity. Qed.

Example utf8_bind_lambda {MN A B} (m : FreeOmega MN A) (k : A → FreeOmega MN B) :
  (m >>=ω λ x, k x) = free_omega_bind m (fun x => k x).
Proof. reflexivity. Qed.

Example utf8_nested_lambda {MN A} (c : nat → MN A) :
  (supω n, (x ←ω c n ;; ηω x) >>=ω λ y, ηω y) =
  FOLub (fun n => free_omega_bind
    (FOSample (c n) (fun x => FORet x)) (fun y => FORet y)).
Proof. reflexivity. Qed.

Example return_expansion {MN A} (a : A) : ηω a = @FORet MN A a.
Proof. reflexivity. Qed.
Example zero_expansion {MN A} : (⊥ω : FreeOmega MN A) = FOZero.
Proof. reflexivity. Qed.
Example sample_expansion {MN A B} (mu : MN A) (k : A -> FreeOmega MN B) :
  (x ←ω mu ;; k x) = FOSample mu k.
Proof. reflexivity. Qed.
Example sup_expansion {MN A} (c : nat -> FreeOmega MN A) :
  (supω n, c n) = FOLub c.
Proof. reflexivity. Qed.
Example embedding_expansion {MN A} (mu : MN A) :
  ↑ω mu = FOSample mu (fun x => FORet x).
Proof. reflexivity. Qed.

(** Raw bind requires no native measure operations or laws. *)
Example bind_expansion {MN A B} (m : FreeOmega MN A) (k : A -> FreeOmega MN B) :
  m >>=ω k = free_omega_bind m k.
Proof. reflexivity. Qed.
Example bind_association {MN A B C}
    (m : FreeOmega MN A) (k : A -> FreeOmega MN B) (h : B -> FreeOmega MN C) :
  m >>=ω k >>=ω h = free_omega_bind (free_omega_bind m k) h.
Proof. reflexivity. Qed.
Example bind_lambda {MN A B} (m : FreeOmega MN A) (k : A -> FreeOmega MN B) :
  (m >>=ω fun x => k x) = free_omega_bind m k.
Proof. reflexivity. Qed.
Example sup_bind {MN A B} (c : nat -> FreeOmega MN A) (k : A -> FreeOmega MN B) :
  (supω n, c n >>=ω k) = FOLub (fun n => free_omega_bind (c n) k).
Proof. reflexivity. Qed.

Example nested_samples {MN A B} (mu : MN A) (k : A -> MN B) :
  (x ←ω mu ;; y ←ω k x ;; ηω (x,y)) =
  FOSample mu (fun x => FOSample (k x) (fun y => FORet (x,y))).
Proof. reflexivity. Qed.
Example sup_typed_binder {MN A} (mu : MN A) (k : nat -> A -> FreeOmega MN A) :
  (supω (n : nat), x ←ω mu ;; k n x) =
  FOLub (fun n => FOSample mu (fun x => k n x)).
Proof. reflexivity. Qed.

(** Raw syntax still accepts arbitrary sequences; no chain certificate is
    manufactured by the notation. This is not a semantic lub assertion. *)
Example arbitrary_sequence {MN} :
  (supω n, ηω (Nat.even n)) = @FOLub MN bool (fun n => FORet (Nat.even n)).
Proof. reflexivity. Qed.

Section HighResult.
Universe node rep high.
Constraint node < high.
Example high_result
    (MN : Type@{node} -> Type@{rep}) (mu : MN bool)
    (A : Type@{high}) (a : A) :
  (x ←ω mu ;; ηω a) = FOSample mu (fun _ => FORet a).
Proof. reflexivity. Qed.

Example high_embedding
    (MN : Type@{node} -> Type@{rep}) (mu : MN bool) (A : Type@{high}) :
  (↑ω mu : FreeOmegaAt MN A bool) = FOSample mu (fun x => FORet x).
Proof. reflexivity. Qed.

Example high_bind
    (MN : Type@{node} -> Type@{rep}) (mu : MN bool)
    (A : Type@{high}) (a : A) :
  (↑ω mu >>=ω fun _ => ηω a) = FOSample mu (fun _ => FORet a).
Proof. reflexivity. Qed.

End HighResult.

From PTree Require Import PTree.
From ITree.Basics Require Import Monad.
Import MonadNotation.
Local Open Scope monad_scope.

(** Opening the probability-expression scope does not reinterpret programs. *)
Example program_bind_unchanged {E MN A} (mu : MN A) :
  (x <- sample mu ;; Ret x) =
  @PTree.bind E MN A A (sample mu) (fun x => Ret x).
Proof. reflexivity. Qed.
Example program_as_value {E MN A} (mu : MN A) :
  (x ←ω mu ;; ηω (Ret x : ptree E MN A)) =
  FOSample mu (fun x => FORet (Ret x : ptree E MN A)).
Proof. reflexivity. Qed.

Local Close Scope freeomega_scope.
Fail Check (ηω tt).
Fail Check (FORet tt >>=ω (fun x => FORet x)).
Fail Check (supω n, FORet n).
Fail Check (x ←ω @None bool ;; FORet x).
