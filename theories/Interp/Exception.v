(** Standard ITree exception vocabulary. Early exit changes the return type
    to [Err + A]; it cannot be expressed as a returning void-valued handler.
    In particular a Throw is not missing probability mass or divergence. *)
Set Universe Polymorphism.
From ITree.Events Require Import Exception.
From ITree.Basics Require Import Basics.
From ITree.Core Require Import Subevent.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
Set Implicit Arguments.
Unset Strict Implicit.

Definition throw {Err E MN A} `{exceptE Err -< E} (err : Err) : ptree E MN A :=
  Vis (subevent _ (Throw err)) (fun v : void => match v with end).

Definition exception_value {Err X} (e : exceptE Err X) : Err :=
  match e with Throw err => err end.

CoFixpoint run_exception {Err E MN A} (t : ptree (exceptE Err +' E) MN A) : ptree E MN (Err+A) :=
  match observe t with
  | RetF a => Ret (inr a)
  | TauF u => Tau (run_exception u)
  | @VisF _ _ _ _ X e k => match e with
      | inl1 ex => Ret (inl (exception_value ex))
      | inr1 fe => Vis fe (fun x => run_exception (k x)) end
  | @ProbF _ _ _ _ X mu k => Prob mu (fun x => run_exception (k x))
  end.

Definition exception_result_rel {Err A B} (RR : A -> B -> Prop) (x : Err+A) (y : Err+B) : Prop :=
  match x,y with
  | inl e, inl f => e = f
  | inr a, inr b => RR a b
  | _,_ => False
  end.

Lemma observe_run_exception {Err E MN A} (t : ptree (exceptE Err +' E) MN A) :
  observe (run_exception t) =
  match observe t with
  | RetF a => RetF (inr a)
  | TauF u => TauF (run_exception u)
  | @VisF _ _ _ _ X e k => match e with
      | inl1 ex => RetF (inl (exception_value ex))
      | inr1 fe => VisF fe (fun x => run_exception (k x)) end
  | @ProbF _ _ _ _ X mu k => ProbF mu (fun x => run_exception (k x))
  end.
Proof.
  unfold observe at 1. cbn. destruct (observe t); try reflexivity. destruct e; reflexivity.
Qed.
