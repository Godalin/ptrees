(** Phase 4a migration certificate, NOT a second maintained rational backend.
    Relate the still-current nnQ lists to ordinary-rat shared records before
    replacing their many indexed/support clients. Conversions are confined to
    Regression: no library or public facade may consume this file.

    Compare raw projections, not equality of invariant proofs. No quotient,
    normalization, proof-irrelevance axiom or carrier equality is needed. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist RatSubTypes.
From PTree.Prob.Backend.EnumQ Require Import Representation Map FrontierLift Iteration.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.
Local Notation Q := rat_rat__canonical__Num_NumDomain.

Definition rational_raw {A : Type} (mu : EnumQ A) : list (rat * A) :=
  List.map (fun px => (Qval (fst px), snd px)) mu.

Lemma rational_raw_nonnegative {A} (mu : EnumQ A) :
  @finite_nonnegative Q A (rational_raw mu).
Proof.
  intros p x H; apply List.in_map_iff in H.
  destruct H as [[q y] [He Hin]]; cbn in He; inversion He; subst.
  exact: Qval_nnQ_ge0.
Qed.

Definition rational_shared {A} (mu : EnumQ A) : FiniteEnum Q A :=
  finite_enum_of_list (@rational_raw_nonnegative A mu).

Fixpoint rational_restore {A} (mu : list (rat * A)) :
    @finite_nonnegative Q A mu -> EnumQ A :=
  match mu as xs return @finite_nonnegative Q A xs -> EnumQ A with
  | [] => fun _ => []
  | (p,x)::tl => fun H =>
      (mknnQ p (H p x (or_introl (Logic.eq_refl _))), x) ::
      rational_restore (fun q y Hy => H q y (or_intror Hy))
  end.

Definition rational_unshare {A} (mu : FiniteEnum Q A) : EnumQ A :=
  rational_restore (finite_enum_nonnegative mu).

Lemma rational_raw_restore {A} (mu : list (rat * A))
    (H : @finite_nonnegative Q A mu) :
  rational_raw (rational_restore H) = mu.
Proof.
  induction mu as [|[p x] tl IH]; cbn; first reflexivity.
  f_equal; exact: IH.
Qed.

Lemma rational_restore_raw {A} (mu : EnumQ A)
    (H : @finite_nonnegative Q A (rational_raw mu)) :
  rational_restore H = mu.
Proof.
  induction mu as [|[p x] tl IH]; cbn; first reflexivity.
  f_equal; last exact: IH.
  f_equal; apply val_inj; reflexivity.
Qed.

Theorem rational_old_roundtrip {A} (mu : EnumQ A) :
  rational_unshare (rational_shared mu) = mu.
Proof. exact: rational_restore_raw. Qed.

Theorem rational_shared_roundtrip {A} (mu : FiniteEnum Q A) :
  finite_enum_raw (rational_shared (rational_unshare mu)) = finite_enum_raw mu.
Proof. exact: rational_raw_restore. Qed.

Lemma rational_raw_app {A} (mu nu : EnumQ A) :
  rational_raw (mu ++ nu) = rational_raw mu ++ rational_raw nu.
Proof. exact: List.map_app. Qed.

Lemma rational_raw_scale {A} (p : nnQ) (mu : EnumQ A) :
  rational_raw (scale_EnumQ p mu) = finite_weight_map (Qval p) (rational_raw mu).
Proof. induction mu as [|[q x] tl IH]; cbn; first reflexivity. f_equal; exact IH. Qed.

Theorem rational_shared_ret {A} (x : A) :
  finite_enum_raw (rational_shared (ret_EnumQ x)) = finite_enum_raw (finite_enum_ret Q x).
Proof. reflexivity. Qed.

Theorem rational_shared_zero {A} :
  finite_enum_raw (rational_shared (@nil (nnQ * A))) = finite_enum_raw (@finite_enum_zero Q A).
Proof. reflexivity. Qed.

Theorem rational_shared_scale {A} (p : nnQ) (mu : EnumQ A) :
  finite_enum_raw (rational_shared (scale_EnumQ p mu)) =
  finite_enum_raw (finite_enum_scale (Qval_nnQ_ge0 p) (rational_shared mu)).
Proof. exact: rational_raw_scale. Qed.

Lemma rational_raw_bind {A B} (mu : EnumQ A) (k : A -> EnumQ B) :
  rational_raw (bind_EnumQ mu k) =
  finite_bind (rational_raw mu) (fun x => rational_raw (k x)).
Proof.
  induction mu as [|[p x] tl IH]; first reflexivity.
  change (rational_raw (scale_EnumQ p (k x) ++ bind_EnumQ tl k) =
    finite_weight_map (Qval p) (rational_raw (k x)) ++
    finite_bind (rational_raw tl) (fun x => rational_raw (k x))).
  by rewrite rational_raw_app rational_raw_scale IH.
Qed.

Theorem rational_shared_bind {A B} (mu : EnumQ A) (k : A -> EnumQ B) :
  finite_enum_raw (rational_shared (bind_EnumQ mu k)) =
  finite_enum_raw (finite_enum_bind (rational_shared mu) (fun x => rational_shared (k x))).
Proof. exact: rational_raw_bind. Qed.

Theorem rational_shared_map {A B} (h : A -> B) (mu : EnumQ A) :
  finite_enum_raw (rational_shared (EnumQMap.emap h mu)) =
  finite_enum_raw (finite_enum_map h (rational_shared mu)).
Proof.
  induction mu as [|[p x] tl IH]; cbn; first reflexivity.
  f_equal; exact IH.
Qed.

Theorem rational_shared_index {A} (mu : EnumQ A) (i : nat) :
  nth_error (finite_enum_raw (rational_shared mu)) i =
  option_map (fun px => (Qval (fst px), snd px)) (nth_error mu i).
Proof. exact: nth_error_map. Qed.

Theorem rational_shared_ae {A} (mu : EnumQ A) (P : A -> Prop) :
  enumQ_ae mu P <->
  (forall p x, In (p,x) (finite_enum_raw (rational_shared mu)) -> p <> 0 -> P x).
Proof.
  split.
  - intros H p x Hin Hnz; apply List.in_map_iff in Hin.
    destruct Hin as [[q y] [He Hin]]; cbn in He; inversion He; subst.
    apply (H q x Hin); intro Hz; apply Hnz; by rewrite Hz.
  - intros H p x Hin Hnz.
    apply (H (Qval p) x).
    + apply List.in_map_iff; exists (p,x); split; [reflexivity|exact Hin].
    + intro Hz; apply Hnz; apply val_inj; exact Hz.
Qed.

Theorem rational_shared_expect {A} (mu : EnumQ A) (f : A -> rat) :
  finite_enum_expect (rational_shared mu) f = enumQ_expect f mu.
Proof.
  induction mu as [|[p x] tl IH]; first reflexivity.
  change (Qval p * f x + finite_enum_expect (rational_shared tl) f =
    Qval p * f x + enumQ_expect f tl).
  by rewrite IH.
Qed.

Theorem rational_unshare_expect {A} (mu : FiniteEnum Q A) (f : A -> rat) :
  enumQ_expect f (rational_unshare mu) = finite_enum_expect mu f.
Proof.
  rewrite -rational_shared_expect /finite_enum_expect rational_shared_roundtrip.
  reflexivity.
Qed.

Theorem rational_shared_mass {A} (mu : EnumQ A) :
  finite_mass (rational_shared mu) = enumQ_mass mu.
Proof. exact: rational_shared_expect. Qed.

Theorem rational_shared_subprob {A} (mu : EnumQ A) :
  enumQ_subprob mu <-> finite_mass (rational_shared mu) <= 1.
Proof. by rewrite rational_shared_mass. Qed.

Definition rational_subshared {A} (mu : SubEnumQ A) : FiniteSubdist Q A.
Proof.
  refine (@Build_FiniteSubdist Q A (rational_shared (subenumQ_raw mu)) _).
  rewrite rational_shared_mass; exact (subenumQ_bound mu).
Defined.

Definition rational_subunshare {A} (mu : FiniteSubdist Q A) : SubEnumQ A.
Proof.
  refine (@Build_SubEnumQ A (rational_unshare (finite_subdist_enum mu)) _).
  rewrite /enumQ_subprob /enumQ_mass rational_unshare_expect.
  exact (finite_subdist_mass_bound mu).
Defined.

Theorem rational_sub_old_roundtrip {A} (mu : SubEnumQ A) :
  subenumQ_raw (rational_subunshare (rational_subshared mu)) = subenumQ_raw mu.
Proof. exact: rational_old_roundtrip. Qed.

Theorem rational_sub_shared_roundtrip {A} (mu : FiniteSubdist Q A) :
  finite_enum_raw (finite_subdist_enum (rational_subshared (rational_subunshare mu))) =
  finite_enum_raw (finite_subdist_enum mu).
Proof. exact: rational_shared_roundtrip. Qed.

Theorem rational_subshared_ret {A} (x : A) :
  finite_enum_raw (finite_subdist_enum (rational_subshared (subenumQ_ret x))) =
  finite_enum_raw (finite_subdist_enum (finite_subdist_ret Q x)).
Proof. reflexivity. Qed.

Theorem rational_subshared_zero {A} :
  finite_enum_raw (finite_subdist_enum (rational_subshared (@subenumQ_zero A))) =
  finite_enum_raw (finite_subdist_enum (@finite_subdist_zero Q A)).
Proof. reflexivity. Qed.

Theorem rational_subshared_bind {A B} (mu : SubEnumQ A) (k : A -> SubEnumQ B) :
  finite_enum_raw (finite_subdist_enum (rational_subshared (subenumQ_bind mu k))) =
  finite_enum_raw (finite_subdist_enum
    (finite_subdist_bind (rational_subshared mu) (fun x => rational_subshared (k x)))).
Proof. exact: rational_raw_bind. Qed.

Theorem rational_subshared_expect {A} (mu : SubEnumQ A) (f : A -> rat) :
  finite_subdist_expect (rational_subshared mu) f = enumQ_expect f (subenumQ_raw mu).
Proof. exact: rational_shared_expect. Qed.

(** These tests deliberately preserve the complete list, including order,
    duplicate values and zero entries; equality of expectations alone would
    not protect the indexed-coupling clients during the next migration. *)
Example rational_duplicates_and_zero :
  finite_enum_raw (rational_shared [(1,true); (0,false); (1,true)]) =
  [(1,true); (0,false); (1,true)].
Proof. reflexivity. Qed.

Example rational_overweight_allowed :
  finite_mass (rational_shared [(1,true); (1,true)]) = (2 : rat).
Proof. by rewrite rational_shared_mass /enumQ_mass /= !mulr1 !addr0. Qed.

Example rational_partial_mass_preserved :
  finite_mass (rational_shared [(one_div_two,true); (0,false)]) = (1 : rat) / 2.
Proof. by rewrite rational_shared_mass /enumQ_mass /= mulr1 mul0r !addr0. Qed.

Example rational_null_branch_ignored :
  forall p x, In (p,x) (finite_enum_raw (rational_shared [(1,true); (0,false)])) ->
    p <> 0 -> x = true.
Proof.
  intros p x [H|[H|[]]] Hnz; inversion H; subst; first reflexivity.
  exfalso; exact (Hnz (Logic.eq_refl _)).
Qed.

Example rational_empty_carrier :
  rational_unshare (@finite_enum_zero Q Empty_set) = [].
Proof. reflexivity. Qed.

Section LargeCarrier.
Universe u.
Example rational_high_carrier (X : Type@{u}) :
  rational_unshare (rational_shared (ret_EnumQ X)) = ret_EnumQ X.
Proof. exact: rational_old_roundtrip. Qed.
End LargeCarrier.
