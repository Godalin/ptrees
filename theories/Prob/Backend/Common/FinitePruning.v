(** Finite weighted-list pruning, independent of backend equality/coupling.
    A discard predicate removes entries without reordering or merging them.
    Zero pruning preserves every expectation, even for signed observables;
    arbitrary pruning only decreases nonnegative observations. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section RawPruning.
Context {W : Type} (discard : W -> bool).

Fixpoint finite_prune {A : Type} (mu : list (W * A)) : list (W * A) :=
  match mu with
  | [] => []
  | (p,x)::tl => if discard p then finite_prune tl
                 else (p,x)::finite_prune tl
  end.

Lemma finite_prune_app {A} (mu nu : list (W * A)) :
  finite_prune (mu ++ nu) = finite_prune mu ++ finite_prune nu.
Proof.
  induction mu as [|[p x] tl IH]; cbn; first reflexivity.
  by case: (discard p); cbn; rewrite IH.
Qed.

Lemma finite_prune_map {A B} (f : A -> B) (mu : list (W * A)) :
  finite_prune (List.map (fun px => (fst px, f (snd px))) mu) =
  List.map (fun px => (fst px, f (snd px))) (finite_prune mu).
Proof.
  induction mu as [|[p x] tl IH]; cbn; first reflexivity.
  by case: (discard p); cbn; rewrite IH.
Qed.

Lemma finite_prune_in {A} (mu : list (W * A)) p (x : A) :
  List.In (p,x) (finite_prune mu) <->
  List.In (p,x) mu /\ discard p = false.
Proof.
  induction mu as [|[q y] tl IH]; cbn; first tauto.
  case Hq: (discard q); cbn; rewrite IH.
  - split; first tauto.
    intros [[He|Hin] Hp]; last tauto.
    inversion He; subst; congruence.
  - split.
    + intros [He|[Hin Hp]]; last tauto.
      inversion He; subst; tauto.
    + intros [[He|Hin] Hp]; [left; exact He|right; tauto].
Qed.

Lemma finite_prune_idempotent {A} (mu : list (W * A)) :
  finite_prune (finite_prune mu) = finite_prune mu.
Proof.
  induction mu as [|[p x] tl IH]; cbn; first reflexivity.
  case Hp: (discard p); cbn; [exact IH|by rewrite Hp IH].
Qed.
End RawPruning.

Lemma finite_prune_map_weights {W V A : Type}
    (d : W -> bool) (e : V -> bool) (f : W -> V) (mu : list (W * A)) :
  (forall p, e (f p) = d p) ->
  finite_prune e (List.map (fun px => (f (fst px), snd px)) mu) =
  List.map (fun px => (f (fst px), snd px)) (finite_prune d mu).
Proof.
  intro H; induction mu as [|[p x] tl IH]; cbn; first reflexivity.
  by rewrite H; case: (d p); cbn; rewrite IH.
Qed.

Section CheckedPruning.
Variable R : numDomainType.

Lemma finite_prune_nonnegative {A} d (mu : list (R * A)) :
  finite_nonnegative mu -> finite_nonnegative (finite_prune d mu).
Proof.
  intros H p x Hin; apply finite_prune_in in Hin; exact (H p x (proj1 Hin)).
Qed.

Lemma finite_expect_prune_le {A} d (mu : list (R * A)) f :
  finite_nonnegative mu -> (forall x, 0 <= f x) ->
  finite_expect f (finite_prune d mu) <= finite_expect f mu.
Proof.
  induction mu as [|[p x] tl IH]; intros Hnn Hf; cbn; first exact: lexx.
  have Htl : finite_nonnegative tl.
  { intros q y Hy; exact (Hnn q y (or_intror Hy)). }
  have Hle := IH Htl Hf.
  case: (d p); last exact: lerD (lexx _) Hle.
  apply: le_trans Hle _.
  rewrite lerDr; apply mulr_ge0; [exact (Hnn p x (or_introl (Logic.eq_refl _)))|exact: Hf].
Qed.

Lemma finite_expect_prune_zero {A} (mu : list (R * A)) f :
  finite_expect f (finite_prune (fun p => p == 0) mu) = finite_expect f mu.
Proof.
  induction mu as [|[p x] tl IH]; cbn; first reflexivity.
  case Hp: (p == 0); last by cbn; rewrite IH.
  move/eqP: Hp=> ->; by rewrite mul0r add0r IH.
Qed.

Definition finite_enum_prune {A} d (mu : FiniteEnum R A) : FiniteEnum R A :=
  finite_enum_of_list (@finite_prune_nonnegative A d _ (finite_enum_nonnegative mu)).

Lemma finite_enum_prune_mass_le {A} d (mu : FiniteEnum R A) :
  finite_mass (finite_enum_prune d mu) <= finite_mass mu.
Proof. apply finite_expect_prune_le; [exact: finite_enum_nonnegative|intro; exact: ler01]. Qed.

Lemma finite_enum_prune_zero_expect {A} (mu : FiniteEnum R A) f :
  finite_enum_expect (finite_enum_prune (fun p => p == 0) mu) f = finite_enum_expect mu f.
Proof. exact: finite_expect_prune_zero. Qed.

Definition finite_subdist_prune {A} (d : R -> bool) (mu : FiniteSubdist R A) : FiniteSubdist R A.
Proof.
  refine (@Build_FiniteSubdist R A (finite_enum_prune d (finite_subdist_enum mu)) _).
  exact: le_trans (finite_enum_prune_mass_le d _) (finite_subdist_mass_bound mu).
Defined.

Lemma finite_subdist_prune_zero_expect {A} (mu : FiniteSubdist R A) f :
  finite_subdist_expect (finite_subdist_prune (fun p => p == 0) mu) f = finite_subdist_expect mu f.
Proof. exact: finite_enum_prune_zero_expect. Qed.
End CheckedPruning.
