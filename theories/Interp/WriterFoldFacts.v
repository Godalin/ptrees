(** One-step normalization of canonical WriterT iteration. Only the base
    monad laws and ordered monoid laws are used. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms.
From ExtLib.Structures Require Import Monad Monoid BinOps.
From ITree.Basics Require Import Basics Monad.
From ITree.Events Require Import Writer.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold WriterT.
From PTree.Interp Require Import WriterFold.
Set Implicit Arguments.
Unset Strict Implicit.
Local Open Scope type_scope.

Section WriterFoldFacts.
Context {W : Type} {E MN T : Type -> Type} (op : Monoid W).
Context `{MT : Monad T} `{QT : Eq1 T}.
Context `{QE : @Eq1Equivalence T MT QT} `{ML : @MonadLawsE T QT MT}.
Context (WL : MonoidLaws op).
Variable handle : forall X, E X -> T X.
Variable sample : forall X, MN X -> T X.

Definition writer_next {A} (log : W) (t : ptree (writerE W +' E) MN A) :
    T ((W * ptree (writerE W +' E) MN A) + (W*A)) :=
  match observe t with
  | RetF a => ret (inr (log,a))
  | TauF u => ret (inl (log,u))
  | @VisF _ _ _ _ X e k => match e with
      | inl1 we => match we in writerE _ X return (X -> _) -> _ with
          | Tell w => fun k => ret (inl (monoid_plus op log w,k tt)) end k
      | inr1 fe => bind (@handle X fe) (fun x => ret (inl (log,k x)))
      end
  | @ProbF _ _ _ _ X mu k => bind (@sample X mu) (fun x => ret (inl (log,k x)))
  end.

Theorem writer_fold_step_normalize {A} (t : ptree (writerE W +' E) MN A) log :
  eq1 (writer_fold_step op handle sample (log,t)) (writer_next log t).
Proof.
  unfold writer_fold_step, writerT_step, fold_step, writer_next.
  cbn [fst snd]. destruct (observe t) as [a|u|X e k|X mu k];
    cbn [writer_effect writer_sample writerT_monad Monad.bind Monad.ret fst snd].
  - rewrite bind_ret_l. cbn. rewrite (@monoid_runit W op WL). reflexivity.
  - rewrite bind_ret_l. cbn. rewrite (@monoid_runit W op WL). reflexivity.
  - destruct e as [we|fe].
    + destruct we. cbn [writer_effect]. rewrite !bind_ret_l. cbn.
      rewrite (@monoid_runit W op WL). reflexivity.
    + cbn [writer_effect]. rewrite !bind_bind. apply Proper_bind; [reflexivity|].
      intro x. rewrite !bind_ret_l. cbn. rewrite !(@monoid_runit W op WL). reflexivity.
  - unfold writer_sample. rewrite !bind_bind. apply Proper_bind; [reflexivity|].
    intro x. rewrite !bind_ret_l. cbn. rewrite !(@monoid_runit W op WL). reflexivity.
Qed.
End WriterFoldFacts.
