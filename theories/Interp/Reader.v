(** Standard ITree Reader vocabulary, with no redefined event signature.
    The handler eliminates Ask and forwards all residual effects. *)
Set Universe Polymorphism.
From ITree.Events Require Import Reader.
From ITree.Core Require Import Subevent.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
Set Implicit Arguments.
Unset Strict Implicit.

Definition ask {Env E MN} `{readerE Env -< E} : ptree E MN Env :=
  PTree.trigger (subevent Env Ask).

Definition reader_handler {Env E MN} (env : Env) X (e : (readerE Env +' E) X) : ptree E MN X :=
  match e with
  | inl1 se => match se in readerE _ X return ptree E MN X with Ask => Ret env end
  | inr1 fe => Vis fe (fun x => Ret x)
  end.

Definition run_reader {Env E MN A} (t : ptree (readerE Env +' E) MN A) (env : Env) : ptree E MN A :=
  PTree.interp (reader_handler env) t.

Lemma reader_ask_returns {Env E MN} env :
  @reader_handler Env E MN env _ (inl1 Ask) = Ret env.
Proof. reflexivity. Qed.
Lemma reader_residual_forwards {Env E MN X} env (e : E X) :
  @reader_handler Env E MN env _ (inr1 e) = Vis e (fun x => Ret x).
Proof. reflexivity. Qed.
