(** State effects carry store access; probability is a native PTree sample.
    [execute] is the explicit-state normal form used in the compositional
    proof, not the definition of the distribution semantics in Forward.v. *)
From Coq Require Import Utf8.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Interp Require Import State StateFold.
From PTree.Examples.PGCL Require Import Syntax.
Set Implicit Arguments.
Unset Strict Implicit.

CoFixpoint silent_forever {E MN A} : ptree E MN A := Tau silent_forever.

Section Programs.
Context {S P : Type} {MN E : Type → Type}.
Variable coin : P → MN bool.

Fixpoint elaborate (c : command S P) : ptree (stateE S +' E) MN unit :=
  match c with
  | CSkip => Ret tt
  | CDiverge => silent_forever
  | CAssign f => PTree.bind get (λ s, put (f s))
  | CSeq c d => PTree.bind (elaborate c) (λ _, elaborate d)
  | CIf b c d => PTree.bind get (λ s, if b s then elaborate c else elaborate d)
  | CChoice p c d => PTree.bind (PTree.sample (coin p))
      (λ v : bool, if v then elaborate c else elaborate d)
  | CWhile b c => PTree.iter (λ _ : unit,
      PTree.bind get (λ s, if b s
        then PTree.bind (elaborate c) (λ _, Ret (inl tt))
        else Ret (inr tt))) tt
  end.

Fixpoint execute (c : command S P) (s : S) : ptree E MN S :=
  match c with
  | CSkip => Ret s
  | CDiverge => silent_forever
  | CAssign f => Ret (f s)
  | CSeq c d => PTree.bind (execute c s) (execute d)
  | CIf b c d => if b s then execute c s else execute d s
  | CChoice p c d => Prob (coin p) (λ v : bool, if v then execute c s else execute d s)
  | CWhile b c => PTree.iter (λ t,
      if b t then PTree.bind (execute c t) (λ u, Ret (inl u))
      else Ret (inr t)) s
  end.

Definition run (c : command S P) (s : S) : ptree E MN S :=
  PTree.fmap fst (interp_state (@PTree.trigger E MN) (elaborate c) s).
End Programs.
