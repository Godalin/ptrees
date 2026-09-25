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

(** A loss is a completed result relative to the supplied sampler, not an
    execution-resource failure. No probability law for that sampler is implied.
    These views leave the existing runtime representation unchanged. *)
Inductive semantic_result (A : Type) :=
| ResultReturned (a : A)
| ResultLost.
Arguments ResultReturned {A} _.
Arguments ResultLost {A}.

Inductive runner_failure := FuelExhausted | EntropyUnavailable.

Definition outcome_view {A} (r : outcome A) : semantic_result A + runner_failure :=
  match r with
  | Returned a => inl (ResultReturned a)
  | Lost => inl ResultLost
  | Timeout => inr FuelExhausted
  | EntropyExhausted => inr EntropyUnavailable
  end.

Definition outcome_of_view {A} (r : semantic_result A + runner_failure) : outcome A :=
  match r with
  | inl (ResultReturned a) => Returned a
  | inl ResultLost => Lost
  | inr FuelExhausted => Timeout
  | inr EntropyUnavailable => EntropyExhausted
  end.

Lemma outcome_view_roundtrip {A} (r : outcome A) :
  outcome_of_view (outcome_view r) = r.
Proof. destruct r; reflexivity. Qed.

Lemma outcome_of_view_roundtrip {A} (r : semantic_result A + runner_failure) :
  outcome_view (outcome_of_view r) = r.
Proof. destruct r as [[a|]|[]]; reflexivity. Qed.

Lemma finished_iff_semantic_result {A} (r : outcome A) :
  finished r <-> exists result, outcome_view r = inl result.
Proof.
  destruct r; cbn; split; intros H; try contradiction.
  - exists (ResultReturned a). reflexivity.
  - exact I.
  - exists ResultLost. reflexivity.
  - exact I.
  - destruct H as [? H]. discriminate.
  - destruct H as [? H]. discriminate.
Qed.

Lemma unfinished_iff_runner_failure {A} (r : outcome A) :
  ~ finished r <-> exists failure, outcome_view r = inr failure.
Proof.
  destruct r; cbn; split; intros H.
  - exfalso. exact (H I).
  - destruct H as [? H]. discriminate.
  - exfalso. exact (H I).
  - destruct H as [? H]. discriminate.
  - exists FuelExhausted. reflexivity.
  - tauto.
  - exists EntropyUnavailable. reflexivity.
  - tauto.
Qed.

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

(* Typed view of the existing fuel-free relation; not another semantics. *)
Definition executes_result {A} (t : ptree void1 MN A) seed
    (result : semantic_result A) seed' : Prop :=
  executes t seed (outcome_of_view (inl result)) seed'.

Theorem run_result_iff {A} (t : ptree void1 MN A) seed result seed' :
  executes_result t seed result seed' <->
    exists fuel, run fuel t seed = (outcome_of_view (inl result), seed').
Proof.
  unfold executes_result. rewrite run_finished_iff.
  assert (Hdone : finished (outcome_of_view (inl result)))
    by (destruct result; exact I).
  tauto.
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
