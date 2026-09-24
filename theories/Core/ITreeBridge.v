(** A genuine datatype bridge. Sampling is an ITree visible event at the
    source and a native PTree node after elaboration. No probability model
    or preservation law is assumed by these definitions. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ITree.Core Require Import ITreeDefinition.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Handler.
Set Implicit Arguments.
Unset Strict Implicit.

Variant probE (MN : Type -> Type) : Type -> Type :=
| Sample {X} : MN X -> probE MN X.
Arguments Sample {MN X} _.

CoFixpoint from_itree {E MN A} (t : itree E A) : ptree E MN A :=
  match ITreeDefinition.observe t with
  | ITreeDefinition.RetF a => Ret a
  | ITreeDefinition.TauF u => Tau (from_itree u)
  | @ITreeDefinition.VisF _ _ _ X e k => Vis e (fun x => from_itree (k x))
  end.

Definition interp_itree {E F MN A} (h : Handler MN E F) (t : itree E A) :
    ptree F MN A := PTree.interp h (from_itree t).

Definition sample_handler {MN F} : Handler MN (probE MN) F :=
  fun X e => match e with @Sample _ X mu => Prob mu (fun x => Ret x) end.

Definition probability_handler {MN E} : Handler MN (probE MN +' E) E :=
  Handler.case_ sample_handler Handler.id_.

Definition elaborate {MN E A} (t : itree (probE MN +' E) A) : ptree E MN A :=
  interp_itree probability_handler t.

Definition elaborate_closed {MN A} (t : itree (probE MN) A) : ptree void1 MN A :=
  interp_itree sample_handler t.

Lemma observe_from_itree {E MN A} (t : itree E A) :
  observe (@from_itree E MN A t) =
  match ITreeDefinition.observe t with
  | ITreeDefinition.RetF a => RetF a
  | ITreeDefinition.TauF u => TauF (from_itree u)
  | @ITreeDefinition.VisF _ _ _ X e k => VisF e (fun x => from_itree (k x))
  end.
Proof. unfold observe. cbn. destruct (ITreeDefinition.observe t); reflexivity. Qed.
