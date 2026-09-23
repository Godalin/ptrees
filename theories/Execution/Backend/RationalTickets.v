(** Executable exact rational sampling by a finite uniform ticket space.
    The compiler uses numerators/denominators directly, not classical choice.
    Missing mass occupies its own tickets; it is never resampled. This first
    correctness-oriented implementation materializes tickets. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq ssralg ssrnum ssrint order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
From PTree.Prob.Backend.EnumQ Require Import Representation.
From PTree.Prob.Backend.SubEnumQ Require Import Representation.
From PTree.Execution Require Import Runner.
Import EnumQ GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition ticket_den (p : rat) : nat := `|denq p|%N.
Definition ticket_num (p : rat) : nat := `|numq p|%N.

Lemma ticket_den_positive p : (0 < ticket_den p)%N.
Proof. by rewrite /ticket_den absz_gt0 denq_neq0. Qed.

Lemma ticket_coefficient p : 0 <= p ->
  p * (ticket_den p)%:R = (ticket_num p)%:R.
Proof.
  rewrite /ticket_den /ticket_num.
  case: (ratP p)=> [z d Hcop]. case: z Hcop=> [n|n] Hcop Hnn.
  - cbn [absz]. apply divfK. by rewrite pnatr_eq0.
  - have Hd : (0 : rat) < d.+1%:R by rewrite ltr0n.
    have Hneg : (-(n.+1%:R) / d.+1%:R : rat) < 0.
    { by rewrite ltr_pdivrMr // mul0r oppr_lt0 ltr0n. }
    have Hbad := lt_le_trans Hneg Hnn. by rewrite ltxx in Hbad.
Qed.

Fixpoint ticket_sum {A} (f : A -> rat) (xs : list A) : rat :=
  match xs with [] => 0 | x :: rest => f x + ticket_sum f rest end.

Lemma ticket_sum_app {A} (f : A -> rat) xs ys :
  ticket_sum f (xs ++ ys) = ticket_sum f xs + ticket_sum f ys.
Proof.
  induction xs as [|x xs IH]; cbn [List.app cat ticket_sum].
  - by rewrite add0r.
  - by rewrite IH addrA.
Qed.

Lemma ticket_sum_repeat {A} (f : A -> rat) x n :
  ticket_sum f (List.repeat x n) = n%:R * f x.
Proof.
  induction n as [|n IH]; cbn [List.repeat ticket_sum]; [by rewrite mul0r|].
  by rewrite IH -addn1 natrD mulrDl mul1r addrC.
Qed.

Lemma ticket_sum_expand {A} (f : A -> rat) xs n :
  ticket_sum f (List.flat_map (fun x => List.repeat x n) xs) =
    n%:R * ticket_sum f xs.
Proof.
  induction xs as [|x xs IH]; cbn [List.flat_map ticket_sum]; [by rewrite mulr0|].
  by rewrite ticket_sum_app ticket_sum_repeat IH mulrDr.
Qed.

Lemma ticket_sum_map {A B} (f : B -> rat) (g : A -> B) xs :
  ticket_sum f (List.map g xs) = ticket_sum (fun x => f (g x)) xs.
Proof. induction xs; cbn; congruence. Qed.

Lemma ticket_sum_size {A} (xs : list A) :
  ticket_sum (fun _ => 1) xs = (size xs)%:R.
Proof.
  induction xs; cbn [ticket_sum size]; [reflexivity|].
  by rewrite IHxs -addn1 natrD addrC.
Qed.

(** Keep original entry order and multiplicity. A zero coefficient contributes
    no tickets. Products of denominators provide a common scale, not a gcd
    optimization; this makes the executable construction especially simple. *)
Fixpoint compile_tickets {A} (mu : list (rat * A)) : nat * list A :=
  match mu with
  | [] => (1%nat, [])
  | (p,x) :: rest =>
      let '(d, xs) := compile_tickets rest in
      ((ticket_den p * d)%N,
       List.repeat x (ticket_num p * d)%N ++
       List.flat_map (fun y => List.repeat y (ticket_den p)) xs)
  end.

Lemma compile_tickets_positive {A} (mu : list (rat * A)) :
  (0 < (compile_tickets mu).1)%N.
Proof.
  induction mu as [|[p x] rest IH]; [reflexivity|].
  cbn [compile_tickets]. destruct (compile_tickets rest) as [d xs].
  cbn [fst snd] in IH |- *. by rewrite muln_gt0 ticket_den_positive IH.
Qed.

Theorem compile_tickets_expectation {A} (mu : list (rat * A)) (f : A -> rat) :
  finite_nonnegative mu ->
  ticket_sum f (compile_tickets mu).2 =
    (compile_tickets mu).1%:R * finite_expect f mu.
Proof.
  induction mu as [|[p x] rest IH]; intro Hnn.
  - cbn [compile_tickets ticket_sum finite_expect fst snd]. by rewrite mulr0.
  - have Hp : 0 <= p := Hnn p x (or_introl (Logic.eq_refl _)).
    have Htail : finite_nonnegative rest.
    { intros w y Hin. exact (Hnn w y (or_intror Hin)). }
    specialize (IH Htail).
    cbn [compile_tickets]. destruct (compile_tickets rest) as [d xs].
    cbn [fst snd] in IH |- *.
    rewrite ticket_sum_app ticket_sum_repeat ticket_sum_expand IH !natrM.
    rewrite -(ticket_coefficient Hp).
    cbn [finite_expect]. rewrite mulrDr !mulrA.
    congr (_ + _).
    congr (_ * f x). by rewrite [p * (ticket_den p)%:R]mulrC mulrAC.
Qed.

Lemma compile_tickets_bound {A} (mu : SubEnumQ A) :
  (size (compile_tickets (subenumQ_data mu)).2 <=
    (compile_tickets (subenumQ_data mu)).1)%N.
Proof.
  have H := compile_tickets_expectation (fun _ => 1)
    (enumQ_nonnegative (subenumQ_raw mu)).
  rewrite ticket_sum_size in H.
  have Hle : ((size (compile_tickets (subenumQ_data mu)).2)%:R : rat) <=
      (compile_tickets (subenumQ_data mu)).1%:R.
  { rewrite H.
    have Hd : (0 : rat) <= (compile_tickets (subenumQ_data mu)).1%:R by rewrite ler0n.
    have Hmass : finite_expect (fun _ => 1) (subenumQ_data mu) <= 1 := subenumQ_bound mu.
    have Hmul := ler_wpM2l Hd Hmass.
    by rewrite mulr1 in Hmul. }
  by move: Hle; rewrite ler_nat.
Qed.

Definition ticket_outcomes {A} (mu : SubEnumQ A) : list (option A) :=
  let '(d,xs) := compile_tickets (subenumQ_data mu) in
  List.map (@Some A) xs ++ List.repeat None (d - size xs)%N.

Definition ticket_count {A} (mu : SubEnumQ A) : nat :=
  (compile_tickets (subenumQ_data mu)).1.

Definition draw_ticket {A} (mu : SubEnumQ A) (i : nat) : option A :=
  nth None (ticket_outcomes mu) i.

Lemma ticket_outcomes_size {A} (mu : SubEnumQ A) :
  size (ticket_outcomes mu) = ticket_count mu.
Proof.
  have Hbound := compile_tickets_bound mu.
  unfold ticket_outcomes, ticket_count.
  destruct (compile_tickets (subenumQ_data mu)) as [d xs]. cbn [fst snd] in Hbound |- *.
  rewrite size_cat size_map.
  change ((size xs + List.length (List.repeat (@None A) (d-size xs)))%N = d).
  rewrite List.repeat_length. by rewrite subnKC.
Qed.

Lemma ticket_outcomes_enumerated {A} (mu : SubEnumQ A) :
  map (draw_ticket mu) (iota 0 (ticket_count mu)) = ticket_outcomes mu.
Proof.
  rewrite /draw_ticket -ticket_outcomes_size.
  by rewrite map_nth_iota0 // take_size.
Qed.

Definition ticket_expectation {A} (mu : SubEnumQ A) (f : option A -> rat) : rat :=
  (ticket_count mu)%:R^-1 *
  ticket_sum f (map (draw_ticket mu) (iota 0 (ticket_count mu))).

(** Exact law for a uniform index in [0,ticket_count). It includes the lost
    outcome explicitly, for arbitrary signed tests and arbitrary carriers. *)
Theorem uniform_ticket_expectation {A} (mu : SubEnumQ A) (f : option A -> rat) :
  ticket_expectation mu f =
    finite_expect (fun x => f (Some x)) (subenumQ_data mu) +
    (1 - enumQ_mass (subenumQ_raw mu)) * f None.
Proof.
  rewrite /ticket_expectation ticket_outcomes_enumerated /ticket_outcomes /ticket_count.
  have Hb := compile_tickets_bound mu.
  have Hd := compile_tickets_positive (subenumQ_data mu).
  have He := compile_tickets_expectation (fun x => f (Some x))
    (enumQ_nonnegative (subenumQ_raw mu)).
  have Hm := compile_tickets_expectation (fun _ => 1)
    (enumQ_nonnegative (subenumQ_raw mu)).
  fold (subenumQ_data mu) in He, Hm.
  destruct (compile_tickets (subenumQ_data mu)) as [d xs]. cbn [fst snd] in *.
  rewrite ticket_sum_app ticket_sum_map ticket_sum_repeat He.
  rewrite ticket_sum_size in Hm.
  rewrite natrB // Hm mulrDr mulrA mulVf ?mul1r; last by rewrite pnatr_eq0 -lt0n.
  have Hnz : (d%:R : rat) != 0 by rewrite pnatr_eq0 -lt0n.
  congr (_ + _). by rewrite mulrA mulrBr !mulrA !mulVf // mul1r.
Qed.

Theorem uniform_ticket_returns {A} (mu : SubEnumQ A) (f : A -> rat) :
  ticket_expectation mu (fun v => match v with Some x => f x | None => 0 end) =
    finite_expect f (subenumQ_data mu).
Proof. by rewrite uniform_ticket_expectation mulr0 addr0. Qed.

Theorem uniform_ticket_loss {A} (mu : SubEnumQ A) :
  ticket_expectation mu (fun v => match v with Some _ => 0 | None => 1 end) =
    1 - enumQ_mass (subenumQ_raw mu).
Proof. by rewrite uniform_ticket_expectation finite_expect_zero mulr1 add0r. Qed.

(** An entropy provider receives the required bound. Invalid or absent input
    cannot silently become missing probability mass. No statistical claim
    about a provider/PRNG is built into this executable interface. *)
Definition ticket_sample {Seed A}
    (next : nat -> Seed -> option nat * Seed) (mu : SubEnumQ A) (seed : Seed) :
    draw_result A * Seed :=
  let '(oi, rest) := next (ticket_count mu) seed in
  match oi with
  | None => (NoEntropy, rest)
  | Some i => if (i < ticket_count mu)%N then
      (match draw_ticket mu i with Some x => Drawn x | None => Missing end, rest)
    else (NoEntropy, rest)
  end.

Definition ticket_replay_source (bound : nat) (xs : list nat) : option nat * list nat :=
  match xs with [] => (None, []) | i :: rest => (Some i, rest) end.

Definition ticket_replay {A} (mu : SubEnumQ A) (xs : list nat) :=
  ticket_sample ticket_replay_source mu xs.

Lemma ticket_sample_valid {Seed A} next (mu : SubEnumQ A) (s s' : Seed) i :
  next (ticket_count mu) s = (Some i, s') -> (i < ticket_count mu)%N ->
  ticket_sample next mu s =
    (match draw_ticket mu i with Some x => Drawn x | None => Missing end, s').
Proof. by move=> Hnext Hi; rewrite /ticket_sample Hnext Hi. Qed.

Lemma ticket_sample_invalid {Seed A} next (mu : SubEnumQ A) (s s' : Seed) i :
  next (ticket_count mu) s = (Some i, s') -> (ticket_count mu <= i)%N ->
  ticket_sample next mu s = (NoEntropy, s').
Proof. move=> Hnext Hi. by rewrite /ticket_sample Hnext ltnNge Hi. Qed.
