(** Position-preserving operations on weighted lists and shared finite records.
    Raw indexing is independent of scalar algebra. Its checked specializations
    preserve the original nonnegative/mass invariants, order and zero entries.
    No coupling, support quotient or native backend is defined here. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section RawPositions.
Context {W : Type}.

Fixpoint finite_index_from {A : Type} (n : nat) (mu : list (W * A)) : list (W * nat) :=
  match mu with
  | [] => []
  | (p,_) :: tl => (p,n) :: finite_index_from (S n) tl
  end.

Fixpoint finite_value_index_from {A : Type} (n : nat) (mu : list (W * A)) : list (W * (A * nat)) :=
  match mu with
  | [] => []
  | (p,x) :: tl => (p,(x,n)) :: finite_value_index_from (S n) tl
  end.

Lemma finite_index_nil {A} n : finite_index_from n (@nil (W * A)) = [].
Proof. reflexivity. Qed.
Lemma finite_index_cons {A} n p (x : A) tl :
  finite_index_from n ((p,x)::tl) = (p,n)::finite_index_from (S n) tl.
Proof. reflexivity. Qed.
Lemma finite_value_index_nil {A} n : finite_value_index_from n (@nil (W * A)) = [].
Proof. reflexivity. Qed.
Lemma finite_value_index_cons {A} n p (x : A) tl :
  finite_value_index_from n ((p,x)::tl) = (p,(x,n))::finite_value_index_from (S n) tl.
Proof. reflexivity. Qed.

Lemma finite_index_length {A} n (mu : list (W * A)) : length (finite_index_from n mu) = length mu.
Proof. induction mu as [|[p x] tl IH] in n |- *; cbn; [reflexivity|by rewrite IH]. Qed.

Lemma finite_value_index_fst {A} n (mu : list (W * A)) :
  List.map (fun px => (fst px, fst (snd px))) (finite_value_index_from n mu) = mu.
Proof. induction mu as [|[p x] tl IH] in n |- *; cbn; [reflexivity|by rewrite IH]. Qed.

Lemma finite_value_index_snd {A} n (mu : list (W * A)) :
  List.map (fun px => (fst px, snd (snd px))) (finite_value_index_from n mu) =
  finite_index_from n mu.
Proof. induction mu as [|[p x] tl IH] in n |- *; cbn; [reflexivity|by rewrite IH]. Qed.

Lemma finite_index_nth {A} n (mu : list (W * A)) i :
  nth_error (finite_index_from n mu) i =
  option_map (fun px => (fst px, Nat.add n i)) (nth_error mu i).
Proof.
  induction mu as [|[p x] tl IH] in n, i |- *; destruct i; cbn; try reflexivity.
  - by rewrite Nat.add_0_r.
  - rewrite IH Nat.add_succ_r; reflexivity.
Qed.

Lemma finite_value_index_nth {A} n (mu : list (W * A)) i :
  nth_error (finite_value_index_from n mu) i =
  option_map (fun px => (fst px, (snd px, Nat.add n i))) (nth_error mu i).
Proof.
  induction mu as [|[p x] tl IH] in n, i |- *; destruct i; cbn; try reflexivity.
  - by rewrite Nat.add_0_r.
  - rewrite IH Nat.add_succ_r; reflexivity.
Qed.
End RawPositions.

Lemma finite_index_map_weights {W V A : Type} (f : W -> V) n (mu : list (W * A)) :
  finite_index_from n (List.map (fun px => (f (fst px), snd px)) mu) =
  List.map (fun pi => (f (fst pi), snd pi)) (finite_index_from n mu).
Proof. induction mu as [|[p x] tl IH] in n |- *; cbn; [reflexivity|by rewrite IH]. Qed.

Lemma finite_value_index_map_weights {W V A : Type} (f : W -> V) n (mu : list (W * A)) :
  finite_value_index_from n (List.map (fun px => (f (fst px), snd px)) mu) =
  List.map (fun pxi => (f (fst pxi), snd pxi)) (finite_value_index_from n mu).
Proof. induction mu as [|[p x] tl IH] in n |- *; cbn; [reflexivity|by rewrite IH]. Qed.

Section CheckedPositions.
Variable R : numDomainType.

Lemma finite_index_nonnegative {A} n (mu : list (R * A)) :
  finite_nonnegative mu -> finite_nonnegative (finite_index_from n mu).
Proof.
  induction mu as [|[p x] tl IH] in n |- *; intros H q i Hin; cbn in Hin.
  - contradiction.
  - destruct Hin as [He|Hin].
    + inversion He; subst; exact (H q x (or_introl (Logic.eq_refl _))).
    + refine (IH (S n) _ q i Hin); intros r y Hy; exact (H r y (or_intror Hy)).
Qed.

Lemma finite_value_index_nonnegative {A} n (mu : list (R * A)) :
  finite_nonnegative mu -> finite_nonnegative (finite_value_index_from n mu).
Proof.
  induction mu as [|[p x] tl IH] in n |- *; intros H q yi Hin; cbn in Hin.
  - contradiction.
  - destruct Hin as [He|Hin].
    + inversion He; subst; exact (H q x (or_introl (Logic.eq_refl _))).
    + refine (IH (S n) _ q yi Hin); intros r y Hy; exact (H r y (or_intror Hy)).
Qed.

Lemma finite_index_mass {A} n (mu : list (R * A)) :
  finite_expect (fun _ => 1) (finite_index_from n mu) = finite_expect (fun _ => 1) mu.
Proof. induction mu as [|[p x] tl IH] in n |- *; cbn; [reflexivity|by rewrite IH]. Qed.

Lemma finite_value_index_expect {A} n (mu : list (R * A)) (f : A -> R) :
  finite_expect (fun xi => f (fst xi)) (finite_value_index_from n mu) = finite_expect f mu.
Proof. induction mu as [|[p x] tl IH] in n |- *; cbn; [reflexivity|by rewrite IH]. Qed.

Definition finite_enum_index_from {A} n (mu : FiniteEnum R A) : FiniteEnum R nat :=
  finite_enum_of_list (@finite_index_nonnegative A n _ (finite_enum_nonnegative mu)).

Definition finite_enum_value_index_from {A} n (mu : FiniteEnum R A) : FiniteEnum R (A * nat) :=
  finite_enum_of_list (@finite_value_index_nonnegative A n _ (finite_enum_nonnegative mu)).

Lemma finite_enum_index_mass {A} n (mu : FiniteEnum R A) :
  finite_mass (finite_enum_index_from n mu) = finite_mass mu.
Proof. exact: finite_index_mass. Qed.

Lemma finite_enum_value_index_mass {A} n (mu : FiniteEnum R A) :
  finite_mass (finite_enum_value_index_from n mu) = finite_mass mu.
Proof. exact: finite_value_index_expect. Qed.

Definition finite_subdist_index_from {A} (n : nat) (mu : FiniteSubdist R A) : FiniteSubdist R nat.
Proof.
  refine (@Build_FiniteSubdist R nat (finite_enum_index_from n (finite_subdist_enum mu)) _).
  rewrite finite_enum_index_mass; exact (finite_subdist_mass_bound mu).
Defined.

Definition finite_subdist_value_index_from {A} (n : nat) (mu : FiniteSubdist R A) : FiniteSubdist R (A * nat).
Proof.
  refine (@Build_FiniteSubdist R (A * nat) (finite_enum_value_index_from n (finite_subdist_enum mu)) _).
  rewrite finite_enum_value_index_mass; exact (finite_subdist_mass_bound mu).
Defined.
End CheckedPositions.
