(** Parsing, scope and universe contracts for opt-in client notation.
    These are definitional checks, not additional FreeOmega semantic laws. *)
Set Universe Polymorphism.
Require Import PTree.Prob.FreeOmega.Definition.

Fail Check (η tt).
Fail Check free_omega_qlift.
Fail Check FreeOmegaObservableSemanticMeasure.
Fail Check ptree.

Example delimited_return {MN A} (a : A) :
  (η a)%fo = @FORet MN A a.
Proof. reflexivity. Qed.

Local Open Scope freeomega_scope.

Example return_expansion {MN A} (a : A) : η a = @FORet MN A a.
Proof. reflexivity. Qed.
Example zero_expansion {MN A} : (⊥ : FreeOmega MN A) = FOZero.
Proof. reflexivity. Qed.
Example sample_expansion {MN A B} (mu : MN A) (k : A -> FreeOmega MN B) :
  (x <~ mu ;; k x) = FOSample mu k.
Proof. reflexivity. Qed.
Example sup_expansion {MN A} (c : nat -> FreeOmega MN A) :
  (ωsup n, c n) = FOLub c.
Proof. reflexivity. Qed.
Example bind_expansion {MN A B} (m : FreeOmega MN A) (k : A -> FreeOmega MN B) :
  m >>=ω k = free_omega_bind m k.
Proof. reflexivity. Qed.
Example embedding_expansion {MN A} (mu : MN A) :
  ↑ω mu = FOSample mu (fun x => FORet x).
Proof. reflexivity. Qed.

Example nested_samples {MN A B} (mu : MN A) (k : A -> MN B) :
  (x <~ mu ;; y <~ k x ;; η (x,y)) =
  FOSample mu (fun x => FOSample (k x) (fun y => FORet (x,y))).
Proof. reflexivity. Qed.
Example bind_associates_left {MN A B C} (m : FreeOmega MN A)
    (k : A -> FreeOmega MN B) (h : B -> FreeOmega MN C) :
  m >>=ω k >>=ω h = free_omega_bind (free_omega_bind m k) h.
Proof. reflexivity. Qed.
Example sup_typed_binder {MN A} (mu : MN A) (k : nat -> A -> FreeOmega MN A) :
  (ωsup (n : nat), x <~ mu ;; k n x) =
  FOLub (fun n => FOSample mu (fun x => k n x)).
Proof. reflexivity. Qed.

(** Raw syntax still accepts arbitrary sequences; no chain certificate is
    manufactured by the notation. This is not a semantic lub assertion. *)
Example arbitrary_sequence {MN} :
  (ωsup n, η (Nat.even n)) = @FOLub MN bool (fun n => FORet (Nat.even n)).
Proof. reflexivity. Qed.

Section HighResult.
Universe node rep high.
Constraint node < high.
Example high_result
    (MN : Type@{node} -> Type@{rep}) (mu : MN bool)
    (A : Type@{high}) (a : A) :
  (x <~ mu ;; η a) = FOSample mu (fun _ => FORet a).
Proof. reflexivity. Qed.

Example high_embedding
    (MN : Type@{node} -> Type@{rep}) (mu : MN bool) (A : Type@{high}) :
  (↑ω mu : FreeOmegaAt MN A bool) = FOSample mu (fun x => FORet x).
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
  (x <~ mu ;; η (Ret x : ptree E MN A)) =
  FOSample mu (fun x => FORet (Ret x : ptree E MN A)).
Proof. reflexivity. Qed.

Local Close Scope freeomega_scope.
Fail Check (η tt).
