(** Elaboration and rejection checks for the opt-in finite-list constructor.
    No new semantic interface and no equality requirement on payloads. *)
From Coq Require Import Utf8 List.
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool seq ssralg ssrnum order rat reals.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.
From PTree.Prob.Backend.SubEnumQ Require Import Representation.
From PTree.Prob.Backend.SubEnumR Require Import Representation.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Definition rational_literal {A : Type} (x y : A) : SubEnumQ A.
Proof. finite_distribution [:: (0,x); (1/4,y); (1/4,y)]. Defined.

Example literal_preserves_entries {A : Type} (x y : A) :
  subenumQ_data (rational_literal x y) = [:: (0,x); (1/4,y); (1/4,y)].
Proof. reflexivity. Qed.

Example literal_preserves_missing_mass {A : Type} (x y : A) :
  finite_subdist_expect (rational_literal x y) (λ _, 1) = 1/2.
Proof. vm_compute; reflexivity. Qed.

Definition empty_literal {A : Type} : SubEnumQ A.
Proof. finite_distribution (@nil (rat * A)). Defined.

Fail Definition negative_literal : SubEnumQ bool :=
  ltac:(finite_distribution [:: (-1,true)]).
Fail Definition excessive_literal : SubEnumQ bool :=
  ltac:(finite_distribution [:: (3/4,true); (3/4,false)]).

(** The same constructor infers the real backend. Only scalar facts remain;
    neither nonnegativity of a list nor membership needs a client proof. *)
Definition real_literal (R : realType) (p : R) (Hp : 0 <= p) (Hp1 : p <= 1) :
    SubEnumR R bool.
Proof.
  finite_distribution [:: (p,true); (1-p,false)].
  - by rewrite subr_ge0.
  - by rewrite addrC subrK.
Defined.

Example real_literal_preserves_entries (R : realType) (p : R)
    (Hp : 0 <= p) (Hp1 : p <= 1) :
  subenumR_raw (real_literal R p Hp Hp1) = [:: (p,true); (1-p,false)].
Proof. reflexivity. Qed.
