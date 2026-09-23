(** Exact rational interval selection and deterministic replay. The input is
    a checked quantile in [0,1), NOT a claim that arbitrary rational replay
    tokens are uniformly distributed. A seeded generator and its discrete
    ticket-distribution correctness remain separate obligations. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
From PTree.Prob.Backend.EnumQ Require Import Representation.
From PTree.Prob.Backend.SubEnumQ Require Import Representation.
From PTree.Execution Require Import Runner.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Record quantile := {
  quantile_value : rat;
  quantile_nonnegative : 0 <= quantile_value;
  quantile_below_one : quantile_value < 1
}.

(** Lower endpoints are included, upper endpoints excluded. Zero-weight
    entries are skipped even at quantile zero; duplicate values need no
    decidable equality and simply occupy several intervals. *)
Fixpoint pick_interval {A} (mu : list (rat * A)) (q : rat) : option A :=
  match mu with
  | [] => None
  | (p,x) :: rest =>
      if q < p then Some x else pick_interval rest (q - p)
  end.

Lemma pick_interval_support {A} (mu : list (rat * A)) q x :
  0 <= q -> pick_interval mu q = Some x ->
  exists p, In (p,x) mu /\ 0 < p.
Proof.
  revert q. induction mu as [|[p y] rest IH]; intros q Hq Hpick.
  - discriminate.
  - change ((if q < p then Some y else pick_interval rest (q-p)) = Some x) in Hpick.
    case Hqp: (q < p) in Hpick.
    + inversion Hpick; subst. exists p. split; [left; reflexivity|].
      exact: le_lt_trans Hq Hqp.
    + have Hpq : p <= q by rewrite leNgt Hqp.
      have Hr : 0 <= q - p by rewrite subr_ge0.
      destruct (IH _ Hr Hpick) as [w [Hin Hw]].
      exists w. split; [right; exact Hin|exact Hw].
Qed.

Lemma pick_interval_missing {A} (mu : list (rat * A)) q :
  finite_nonnegative mu -> 0 <= q ->
  (pick_interval mu q = None <-> finite_expect (fun _ => 1) mu <= q).
Proof.
  revert q. induction mu as [|[p x] rest IH]; intros q Hnn Hq.
  - cbn. split; auto.
  - change ((if q < p then Some x else pick_interval rest (q-p)) = None <->
      p * 1 + finite_expect (fun _ => 1) rest <= q).
    rewrite mulr1.
    have Htail : finite_nonnegative rest.
    { intros w y Hy. exact (Hnn w y (or_intror Hy)). }
    case Hqp: (q < p).
    + split; [discriminate|]. intro Hmass.
      have Hnonneg : 0 <= finite_expect (fun _ => 1) rest.
      { apply finite_expect_nonnegative; [exact Htail|intro y; exact: ler01]. }
      have Hp : p <= q.
      { apply: le_trans Hmass. by rewrite lerDl. }
      have Hbad := lt_le_trans Hqp Hp. by rewrite ltxx in Hbad.
    + have Hpq : p <= q by rewrite leNgt Hqp.
      have Hr : 0 <= q - p by rewrite subr_ge0.
      rewrite (IH _ Htail Hr) lerBrDl. reflexivity.
Qed.

Definition replay_sample {A} (mu : SubEnumQ A) (entropy : list quantile) :
    draw_result A * list quantile :=
  match entropy with
  | [] => (NoEntropy, [])
  | q :: rest =>
      (match pick_interval (subenumQ_data mu) (quantile_value q) with
       | Some x => Drawn x
       | None => Missing
       end, rest)
  end.

Theorem replay_sample_support {A} (mu : SubEnumQ A) q rest x :
  replay_sample mu (q :: rest) = (Drawn x, rest) ->
  exists p, In (p,x) (subenumQ_data mu) /\ 0 < p.
Proof.
  cbn [replay_sample]. case Hpick: (pick_interval _ _) => [y|];
    intro H; inversion H; subst.
  eapply pick_interval_support; [exact: quantile_nonnegative|exact Hpick].
Qed.

Theorem replay_sample_missing {A} (mu : SubEnumQ A) q rest :
  replay_sample mu (q :: rest) = (Missing, rest) <->
  enumQ_mass (subenumQ_raw mu) <= quantile_value q.
Proof.
  change ((match pick_interval (subenumQ_data mu) (quantile_value q) with
      Some x => Drawn x | None => Missing end, rest) = (Missing, rest) <->
    finite_expect (fun _ => 1) (subenumQ_data mu) <= quantile_value q).
  rewrite <- (pick_interval_missing
    (enumQ_nonnegative (subenumQ_raw mu)) (quantile_nonnegative q)).
  destruct (pick_interval _ _); split; congruence.
Qed.
