(** Standard ITree state events, interpreted in PTree. The state is threaded
    along each execution branch; native probability nodes are preserved.
    Every eliminated event leaves one administrative Tau. No semantic or
    sampling law is needed for this productive tree transformation. *)
Set Universe Polymorphism.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From ITree.Core Require Import Subevent.
From PTree.Core Require Import PTreeDefinition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition get {S E MN} `{stateE S -< E} : ptree E MN S :=
  PTree.trigger (subevent S (Get S)).

Definition put {S E MN} `{stateE S -< E} (s : S) : ptree E MN unit :=
  PTree.trigger (subevent unit (Put S s)).

(** This is an ordinary state transition, not a fixed stateless handler. *)
Definition state_response {S X} (e : stateE S X) (s : S) : S * X :=
  match e in stateE _ X return S * X with
  | Get => (s, s)
  | Put s' => (s', tt)
  end.

CoFixpoint run_state {S E MN A}
    (t : ptree (stateE S +' E) MN A) (s : S) : ptree E MN (S * A) :=
  match observe t with
  | RetF a => Ret (s, a)
  | TauF u => Tau (run_state u s)
  | @ProbF _ _ _ _ X mu k => Prob mu (fun x => run_state (k x) s)
  | @VisF _ _ _ _ X e k =>
      match e with
      | inl1 se => let '(s', x) := state_response se s in Tau (run_state (k x) s')
      | inr1 fe => Vis fe (fun x => run_state (k x) s)
      end
  end.

Definition state_result_rel {S A B} (RR : A -> B -> Prop)
    (x : S * A) (y : S * B) : Prop := fst x = fst y /\ RR (snd x) (snd y).

(** The step equation keeps the coinductive tree abstract; clients rewrite
    observations rather than asserting intensional equality of cofixpoints. *)
Lemma observe_run_state {S E MN A} (t : ptree (stateE S +' E) MN A) s :
  observe (run_state t s) =
  match observe t with
  | RetF a => RetF (s, a)
  | TauF u => TauF (run_state u s)
  | @ProbF _ _ _ _ X mu k => ProbF mu (fun x => run_state (k x) s)
  | @VisF _ _ _ _ X e k =>
      match e with
      | inl1 se => let '(s', x) := state_response se s in TauF (run_state (k x) s')
      | inr1 fe => VisF fe (fun x => run_state (k x) s)
      end
  end.
Proof.
  unfold observe at 1. cbn.
  destruct (observe t) as [a|u|X e k|X mu k]; try reflexivity.
  destruct e as [se|fe]; try reflexivity.
  destruct (state_response se s). reflexivity.
Qed.
