(** Log-first WriterT on ITree's existing [Monads.writerT] carrier.
    Accumulation is old <> new, including in iteration. These operations
    and law constructors are explicit, not global typeclass candidates. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms RelationClasses.
From ExtLib.Structures Require Import Monad Monoid BinOps.
From ITree.Basics Require Import Basics Monad.
From PTree.Core Require Import IterationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Local Open Scope type_scope.

Section WriterT.
Context {W : Type} {T : Type -> Type} (op : Monoid W).
Context `{MT : Monad T}.

Definition writerT_monad : Monad (Monads.writerT W T) := {|
  ret := fun A a => @ret T MT _ (monoid_unit op, a);
  bind := fun A B t k => @bind T MT _ _ t (fun wa =>
    @bind T MT _ _ (k (snd wa))
      (fun wb => @ret T MT _ (monoid_plus op (fst wa) (fst wb), snd wb)))
|}.

Definition writerT_step {I A} (f : I -> Monads.writerT W T (I+A)) (wi : W*I) :
    T ((W*I) + (W*A)) :=
  @bind T MT _ _ (f (snd wi)) (fun wv => @ret T MT _ (match snd wv with
    | inl i => inl (monoid_plus op (fst wi) (fst wv), i)
    | inr a => inr (monoid_plus op (fst wi) (fst wv), a)
    end)).

Definition writerT_iter `{IT : MonadIter T} : MonadIter (Monads.writerT W T) :=
  fun A I f i => iter (writerT_step f) (monoid_unit op,i).

Context `{QT : Eq1 T}.
Definition writerT_eq1 : Eq1 (Monads.writerT W T) := fun A => @eq1 T QT (W*A).

Definition writerT_eq_equivalence (QE : @Eq1Equivalence T MT QT) :
    @Eq1Equivalence (Monads.writerT W T) writerT_monad writerT_eq1 :=
  fun A => QE (W*A).

Context `{QE : @Eq1Equivalence T MT QT} `{ML : @MonadLawsE T QT MT}.

Definition writerT_monad_laws (WL : MonoidLaws op) :
    @MonadLawsE (Monads.writerT W T) writerT_eq1 writerT_monad.
Proof.
  constructor; intros; unfold eq1, writerT_eq1;
    cbn [Monad.bind Monad.ret writerT_monad].
  - rewrite bind_ret_l. cbn. transitivity (@bind T MT _ _ (f x) (fun wa => @ret T MT _ wa)).
    + apply Proper_bind; [reflexivity|]. intros [w a]. cbn.
      rewrite (@monoid_lunit W op WL). reflexivity.
    + apply bind_ret_r.
  - transitivity (@bind T MT _ _ x (fun wa => @ret T MT _ wa)).
    + apply Proper_bind; [reflexivity|]. intros [w a]. cbn.
      rewrite bind_ret_l. cbn. rewrite (@monoid_runit W op WL). reflexivity.
    + apply bind_ret_r.
  - rewrite !bind_bind. apply Proper_bind; [reflexivity|]. intros [w a]. cbn.
    rewrite !bind_bind. apply Proper_bind; [reflexivity|]. intros [v b]. cbn.
    rewrite !bind_ret_l. cbn. rewrite !bind_bind.
    apply Proper_bind; [reflexivity|]. intros [z c]. cbn.
    rewrite !bind_ret_l. cbn. rewrite (@monoid_assoc W op WL). reflexivity.
  - intros x y Hxy f g Hfg. apply Proper_bind; [exact Hxy|]. intros [w a]. cbn.
    apply Proper_bind; [apply Hfg|]. intros [v b]. reflexivity.
Defined.

Theorem writerT_iteration_uniform (WL : MonoidLaws op) `{IT : MonadIter T}
    (Hunif : @iteration_uniform T MT IT QT) :
    @iteration_uniform (Monads.writerT W T) writerT_monad writerT_iter writerT_eq1.
Proof.
  intros I J A f g h Hsquare i.
  change (eq1 (iter (writerT_step f) (monoid_unit op,i))
    (iter (writerT_step g) (monoid_unit op,h i))).
  apply (Hunif (W*I) (W*J) (W*A) (writerT_step f) (writerT_step g)
    (fun wi => (fst wi,h (snd wi)))).
  intros [w j]. unfold writerT_step. cbn.
  specialize (Hsquare j).
  change (@eq1 T QT _ (@bind T MT _ _ (f j) (fun wv =>
    @bind T MT _ _ (@ret T MT _ (monoid_unit op, iteration_map h (snd wv)))
      (fun wu => @ret T MT _ (monoid_plus op (fst wv) (fst wu), snd wu)))) (g (h j))) in Hsquare.
  assert (Hs : @eq1 T QT _
    (@bind T MT _ _ (f j) (fun wv => @ret T MT _ (fst wv, iteration_map h (snd wv)))) (g (h j))).
  { transitivity (@bind T MT _ _ (f j) (fun wv =>
      @bind T MT _ _ (@ret T MT _ (monoid_unit op, iteration_map h (snd wv)))
        (fun wu => @ret T MT _ (monoid_plus op (fst wv) (fst wu), snd wu)))).
    - apply Proper_bind; [reflexivity|]. intros [v a]. cbn.
      rewrite bind_ret_l. cbn. rewrite (@monoid_runit W op WL). reflexivity.
    - exact Hsquare. }
  transitivity (@bind T MT _ _
    (@bind T MT _ _ (f j) (fun wv => @ret T MT _ (fst wv, iteration_map h (snd wv))))
    (fun wv => @ret T MT _ (match snd wv with
      | inl k => inl (monoid_plus op w (fst wv), k)
      | inr a => inr (monoid_plus op w (fst wv), a) end))).
  - rewrite !bind_bind. apply Proper_bind; [reflexivity|]. intros [v [k|a]];
      rewrite !bind_ret_l; reflexivity.
  - apply Proper_bind; [exact Hs|]. intro v. reflexivity.
Qed.
End WriterT.
