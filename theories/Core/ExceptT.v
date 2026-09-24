(** Laws for the existing ExtLib exception transformer and ITree iteration.
    Equality observes [unEitherT]; no new transformer or global instance is
    introduced. Clients opt into the explicit law constructors below. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms RelationClasses.
From ExtLib.Structures Require Import Monad.
From ExtLib.Data.Monads Require Import EitherMonad.
From ITree.Basics Require Import Basics Monad.
From PTree.Core Require Import IterationLaws.
Set Implicit Arguments.
Unset Strict Implicit.

Section ExceptT.
Context {Err : Type} {T : Type -> Type}.
Context `{MT : Monad T} `{QT : Eq1 T}.

Definition exceptT_eq1 : Eq1 (eitherT Err T) :=
  fun A x y => eq1 (unEitherT x) (unEitherT y).

Definition exceptT_eq_equivalence
    (QE : @Eq1Equivalence T MT QT) :
    @Eq1Equivalence (eitherT Err T) (@Monad_eitherT Err T MT) exceptT_eq1.
Proof.
  intro A. destruct (QE (Err+A)%type) as [Hr Hs Ht].
  split; unfold Reflexive, Symmetric, Transitive;
    cbn [eq1 exceptT_eq1]; eauto.
Defined.

Context `{QE : @Eq1Equivalence T MT QT} `{ML : @MonadLawsE T QT MT}.

Definition exceptT_monad_laws :
    @MonadLawsE (eitherT Err T) exceptT_eq1 (@Monad_eitherT Err T MT).
Proof.
  constructor; intros; unfold eq1, exceptT_eq1;
    cbn [Monad.bind Monad.ret Monad_eitherT unEitherT].
  - rewrite (@bind_ret_l T QT MT ML). reflexivity.
  - transitivity (bind (unEitherT x) (fun a => ret a)).
    + apply Proper_bind; [reflexivity|]. intros [e|a]; reflexivity.
    + apply (@bind_ret_r T QT MT ML).
  - rewrite bind_bind. apply Proper_bind; [reflexivity|]. intros [e|a]; cbn.
    + rewrite bind_ret_l. reflexivity.
    + reflexivity.
  - intros x y Hxy f g Hfg. apply Proper_bind; [exact Hxy|].
    intros [e|a]; [reflexivity|apply Hfg].
Defined.

Definition exceptT_step {I A} (f : I -> eitherT Err T (I+A)) (i : I) :
    T (I + (Err+A)) :=
  bind (unEitherT (f i)) (fun v => ret
    (match v with
     | inl e => inr (inl e)
     | inr (inl j) => inl j
     | inr (inr a) => inr (inr a)
     end)).

Theorem exceptT_iteration_uniform `{IT : MonadIter T}
    (Hunif : @iteration_uniform T MT IT QT) :
    @iteration_uniform (eitherT Err T) (@Monad_eitherT Err T MT)
      (@MonadIter_eitherT T Err MT IT) exceptT_eq1.
Proof.
  intros I J A f g h Hsquare i.
  change (eq1 (iter (exceptT_step f) i) (iter (exceptT_step g) (h i))).
  apply (Hunif I J (Err+A)%type (exceptT_step f) (exceptT_step g) h).
  intro j. unfold exceptT_step.
  specialize (Hsquare j).
  change (eq1
    (bind (unEitherT (f j)) (fun v => match v with
      | inl e => ret (inl e)
      | inr v => ret (inr (iteration_map h v)) end))
    (unEitherT (g (h j)))) in Hsquare.
  transitivity (bind
    (bind (unEitherT (f j)) (fun v => match v with
      | inl e => ret (inl e)
      | inr v => ret (inr (iteration_map h v)) end))
    (fun v => ret (match v with
      | inl e => inr (inl e)
      | inr (inl k) => inl k
      | inr (inr a) => inr (inr a) end))).
  - rewrite !bind_bind.
    apply Proper_bind; [reflexivity|]. intros [e|[k|a]];
      rewrite !bind_ret_l; reflexivity.
  - apply Proper_bind; [exact Hsquare|]. intro v. reflexivity.
Qed.
End ExceptT.
