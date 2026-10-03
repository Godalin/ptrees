(** Purely probabilistic GCL: state updates/tests are shallow expressions;
    commands, including unbounded while, are an inductive syntax. [P] is a
    type of probability parameters, not a distribution representation. A
    concrete instance supplies bounded parameters and their native coins.
    There is no demonic choice, conditioning, or weakest-precondition layer. *)
From Coq Require Import Utf8 ZArith.
Set Universe Polymorphism.
Set Implicit Arguments.

Inductive command (S P : Type) : Type :=
| CSkip
| CDiverge
| CAssign (update : S → S)
| CSeq (first second : command S P)
| CIf (test : S → bool) (yes no : command S P)
| CChoice (probability : P) (left right : command S P)
| CWhile (test : S → bool) (body : command S P).

Arguments CSkip {S P}.
Arguments CDiverge {S P}.
Arguments CAssign {S P} _.
Arguments CSeq {S P} _ _.
Arguments CIf {S P} _ _ _.
Arguments CChoice {S P} _ _ _.
Arguments CWhile {S P} _ _.

(** Integer stores retain the original sketch's assignment language, without
    duplicating an effectful evaluator for pure arithmetic. Other examples
    may instantiate [S] with a tuple or record instead. *)
Definition store := nat → Z.
Definition update (s : store) (x : nat) (v : Z) : store :=
  λ y, if Nat.eqb x y then v else s y.
Definition assign {P} (x : nat) (e : store → Z) : command store P :=
  CAssign (λ s, update s x (e s)).

Declare Scope pgcl_scope.
Delimit Scope pgcl_scope with pgcl.
Bind Scope pgcl_scope with command.
Module PGCLNotations.
Notation "'SKIP'" := CSkip : pgcl_scope.
Notation "'DIVERGE'" := CDiverge : pgcl_scope.
Notation "'UPDATE' f" := (CAssign f) (at level 60) : pgcl_scope.
Notation "x '::=' e" := (assign x e) (at level 60) : pgcl_scope.
Notation "c ;; d" := (CSeq c d) (at level 100, right associativity) : pgcl_scope.
Notation "'IF' b 'THEN' c 'ELSE' d 'ENDIF'" := (CIf b c d)
  (at level 200, b at level 100, c at level 200, d at level 200) : pgcl_scope.
Notation "c '⊕[' p ']' d" := (CChoice p c d)
  (at level 85, p at level 0, right associativity) : pgcl_scope.
Notation "'WHILE' b 'DO' c 'OD'" := (CWhile b c)
  (at level 200, b at level 100, c at level 200) : pgcl_scope.
End PGCLNotations.
