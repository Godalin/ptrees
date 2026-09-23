(** Deterministic finite execution relative to a native sampler. Missing
    mass, program fuel exhaustion and exhausted replay entropy are distinct.
    This layer proves operational correctness; it does not assume or claim
    that an arbitrary supplied sampler has the right probability law. *)
Set Universe Polymorphism.
From Coq Require Import Arith Lia.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive draw_result (A : Type) := Drawn (a : A) | Missing | NoEntropy.
Arguments Drawn {A} _.
Arguments Missing {A}.
Arguments NoEntropy {A}.

Inductive outcome (A : Type) := Returned (a : A) | Lost | Timeout | EntropyExhausted.
Arguments Returned {A} _.
Arguments Lost {A}.
Arguments Timeout {A}.
Arguments EntropyExhausted {A}.

Definition finished {A} (r : outcome A) : Prop :=
  match r with Returned _ | Lost => True | _ => False end.

Section Runner.
Context {MN : Type -> Type} {Seed : Type}.
Variable sample : forall X, MN X -> Seed -> draw_result X * Seed.

(** A returned node requires no further transition fuel. Tau and Prob each
    consume one unit. A timeout never calls the sampler. *)
Fixpoint run {A} (fuel : nat) (t : ptree void1 MN A) (seed : Seed) : outcome A * Seed :=
  match observe t with
  | RetF a => (Returned a, seed)
  | @VisF _ _ _ _ X e k => match e with end
  | TauF u => match fuel with O => (Timeout, seed) | S n => run n u seed end
  | @ProbF _ _ _ _ X mu k =>
      match fuel with
      | O => (Timeout, seed)
      | S n =>
          let '(choice, seed') := @sample X mu seed in
          match choice with
          | Drawn x => run n (k x) seed'
          | Missing => (Lost, seed')
          | NoEntropy => (EntropyExhausted, seed')
          end
      end
  end.

(** Fuel-free finite operational paths. There is intentionally no timeout
    rule: a resource limit is not a terminal behavior of the program. *)
Inductive executes {A} : ptree void1 MN A -> Seed -> outcome A -> Seed -> Prop :=
| ExecRet t seed a : observe t = RetF a -> executes t seed (Returned a) seed
| ExecTau t u seed result seed' : observe t = TauF u ->
    executes u seed result seed' -> executes t seed result seed'
| ExecDraw t X (mu : MN X) k seed x next result seed' :
    observe t = ProbF mu k -> @sample X mu seed = (Drawn x, next) ->
    executes (k x) next result seed' -> executes t seed result seed'
| ExecLost t X (mu : MN X) k seed seed' :
    observe t = ProbF mu k -> @sample X mu seed = (Missing, seed') ->
    executes t seed Lost seed'.

Lemma executes_finished {A} t seed (result : outcome A) seed' :
  executes t seed result seed' -> finished result.
Proof. intro H. induction H; simpl; auto. Qed.

Theorem run_sound {A} fuel (t : ptree void1 MN A) seed result seed' :
  run fuel t seed = (result, seed') -> finished result -> executes t seed result seed'.
Proof.
  revert t seed result seed'. induction fuel as [|n IH]; intros t seed result seed' Hrun Hdone;
    destruct (observe t) as [a|u|X e k|X mu k] eqn:Ht;
    cbn [run] in Hrun; rewrite Ht in Hrun; try (destruct e).
  - inversion Hrun; subst. constructor. exact Ht.
  - inversion Hrun; subst. contradiction.
  - inversion Hrun; subst. contradiction.
  - inversion Hrun; subst. constructor. exact Ht.
  - eapply ExecTau; [exact Ht|eapply IH; eassumption].
  - destruct (@sample X mu seed) as [[x| |] next] eqn:Hs.
    + eapply ExecDraw; [exact Ht|exact Hs|eapply IH; eassumption].
    + inversion Hrun; subst. eapply ExecLost; eassumption.
    + inversion Hrun; subst. contradiction.
Qed.

Theorem executes_complete {A} (t : ptree void1 MN A) seed result seed' :
  executes t seed result seed' -> exists fuel, run fuel t seed = (result, seed').
Proof.
  intro H. induction H as [t seed a Ht|t u seed result seed' Ht Hpath [n IH]|
    t X mu k seed x next result seed' Ht Hs Hpath [n IH]|t X mu k seed seed' Ht Hs].
  - exists O. cbn [run]. rewrite Ht. reflexivity.
  - exists (S n). cbn [run]. rewrite Ht. exact IH.
  - exists (S n). cbn [run]. rewrite Ht, Hs. exact IH.
  - exists 1. cbn [run]. rewrite Ht, Hs. reflexivity.
Qed.

Theorem run_finished_iff {A} (t : ptree void1 MN A) seed result seed' :
  executes t seed result seed' <->
    finished result /\ exists fuel, run fuel t seed = (result, seed').
Proof.
  split.
  - intro H. split; [eapply executes_finished|apply executes_complete]; exact H.
  - intros [Hdone [n Hrun]]. eapply run_sound; eassumption.
Qed.

Theorem run_finished_more_fuel {A} n m (t : ptree void1 MN A) seed result seed' :
  n <= m -> run n t seed = (result, seed') -> finished result ->
  run m t seed = (result, seed').
Proof.
  revert m t seed result seed'. induction n as [|n IH]; intros m t seed result seed' Hnm Hrun Hdone;
    destruct (observe t) as [a|u|X e k|X mu k] eqn:Ht;
    cbn [run] in Hrun; rewrite Ht in Hrun; try (destruct e).
  - destruct m; cbn [run]; rewrite Ht; exact Hrun.
  - inversion Hrun; subst. contradiction.
  - inversion Hrun; subst. contradiction.
  - destruct m; cbn [run]; rewrite Ht; exact Hrun.
  - destruct m as [|m]; [lia|]. cbn [run]. rewrite Ht. eapply IH; eauto; lia.
  - destruct m as [|m]; [lia|]. cbn [run]. rewrite Ht.
    destruct (@sample X mu seed) as [[x| |] next] eqn:Hs.
    + eapply IH; eauto; lia.
    + exact Hrun.
    + inversion Hrun; subst. contradiction.
Qed.
End Runner.
