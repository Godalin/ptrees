(** Rational bind algebra over the shared checked carrier. All positional
    equations compare raw data; semantic congruence compares atom masses. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
From Coq Require Import List PeanoNat Arith.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq ssrnat ssralg ssrnum rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteAtoms FiniteListAlgebra.
From PTree.Prob.Backend.EnumQ Require Import Representation Map.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory.
Local Open Scope ring_scope.

Lemma bind_EnumQ_app {A B} (mu nu : EnumQ A) (k : A -> EnumQ B) :
  enumQ_raw (bind_EnumQ (enumQ_app mu nu) k) =
  enumQ_raw (enumQ_app (bind_EnumQ mu k) (bind_EnumQ nu k)).
Proof. exact: finite_bind_app. Qed.

Definition enumQ_weightQ {A} (f : A -> rat) (mu : EnumQ A) : rat := enumQ_expect f mu.

Lemma enumQ_weightQ_filter_split {A : eqType} (f : A -> rat) (mu : EnumQ A) a :
  enumQ_weightQ f mu = acc_mass a mu*f a +
    enumQ_weightQ f (enumQ_filter (fun px => px.2 != a) mu).
Proof.
  change (finite_expect f (enumQ_raw mu) = finite_atom a (enumQ_raw mu)*f a +
    finite_expect f (List.filter (fun px => px.2 != a) (enumQ_raw mu))).
  elim: (enumQ_raw mu)=> [|[p x] tl IH]; first by rewrite /= mul0r add0r.
  rewrite /= finite_atom_cons.
  case Hxa: (x == a)=> /=.
  - move/eqP: Hxa=> He; subst x; by rewrite IH mulrDl addrA.
  - by rewrite IH add0r addrCA.
Qed.
Lemma enumQ_weightQ_zero {A : eqType} (f : A -> rat) (mu : EnumQ A) :
  (forall a, acc_mass a mu = 0) -> enumQ_weightQ f mu = 0.
Proof.
  move=> H; change (finite_expect f (enumQ_raw mu) = finite_expect f [::]).
  apply finite_expect_atoms_eq=> x; exact (H x).
Qed.
Lemma enumQ_weightQ_proper {A : eqType} (f : A -> rat) (mu nu : EnumQ A) :
  mu ==EnumQ nu -> enumQ_weightQ f mu = enumQ_weightQ f nu.
Proof. exact: finite_expect_atoms_eq. Qed.
Lemma acc_mass_scale {A : eqType} (x : A) p (Hp : 0 <= p) (mu : EnumQ A) :
  acc_mass x (scale_EnumQ Hp mu) = p * acc_mass x mu.
Proof. exact: finite_atom_scale. Qed.
Lemma acc_mass_bind_EnumQ {A} {B : eqType} (mu : EnumQ A) (k : A -> EnumQ B) b :
  acc_mass b (bind_EnumQ mu k) = enumQ_weightQ (fun a => acc_mass b (k a)) mu.
Proof. exact: finite_atom_bind. Qed.
Lemma bind_EnumQ_outer_proper {A B : eqType} (mu nu : EnumQ A) (k : A -> EnumQ B) :
  mu ==EnumQ nu -> bind_EnumQ mu k ==EnumQ bind_EnumQ nu k.
Proof. move=> H b; rewrite !acc_mass_bind_EnumQ; exact: enumQ_weightQ_proper H. Qed.

Lemma bind_EnumQ_scale {A B} p (Hp : 0 <= p) (mu : EnumQ A) (k : A -> EnumQ B) :
  enumQ_raw (bind_EnumQ (scale_EnumQ Hp mu) k) =
  enumQ_raw (scale_EnumQ Hp (bind_EnumQ mu k)).
Proof. exact: finite_bind_scale. Qed.
Lemma bind_EnumQ_assoc {A B C} (mu : EnumQ A) (k : A -> EnumQ B) (h : B -> EnumQ C) :
  enumQ_raw (bind_EnumQ (bind_EnumQ mu k) h) =
  enumQ_raw (bind_EnumQ mu (fun x => bind_EnumQ (k x) h)).
Proof. exact: finite_bind_assoc. Qed.
Lemma bind_EnumQ_ext {A B} (mu : EnumQ A) (k h : A -> EnumQ B) :
  (forall x, enumQ_raw (k x) = enumQ_raw (h x)) ->
  enumQ_raw (bind_EnumQ mu k) = enumQ_raw (bind_EnumQ mu h).
Proof. exact: finite_bind_ext. Qed.
Lemma bind_EnumQ_ext_in {A B} (mu : EnumQ A) (k h : A -> EnumQ B) :
  (forall p x, List.In (p,x) (enumQ_raw mu) -> enumQ_raw (k x) = enumQ_raw (h x)) ->
  enumQ_raw (bind_EnumQ mu k) = enumQ_raw (bind_EnumQ mu h).
Proof.
  change ((forall p x, List.In (p,x) (enumQ_raw mu) -> enumQ_raw (k x) = enumQ_raw (h x)) ->
    finite_bind (enumQ_raw mu) (fun x => enumQ_raw (k x)) =
    finite_bind (enumQ_raw mu) (fun x => enumQ_raw (h x))).
  elim: (enumQ_raw mu)=> [|[p x] tl IH] H //=.
  rewrite (H p x (or_introl (Logic.eq_refl _))).
  rewrite IH // => q y Hy; exact (H q y (or_intror Hy)).
Qed.
Lemma scale_EnumQ_proper {A : eqType} p (Hp : 0 <= p) (mu nu : EnumQ A) :
  mu ==EnumQ nu -> scale_EnumQ Hp mu ==EnumQ scale_EnumQ Hp nu.
Proof. move=> H x; by rewrite !acc_mass_scale H. Qed.
Lemma app_EnumQ_proper {A : eqType} (mu nu rho sigma : EnumQ A) :
  mu ==EnumQ nu -> rho ==EnumQ sigma ->
  enumQ_app mu rho ==EnumQ enumQ_app nu sigma.
Proof. move=> H K x; by rewrite !acc_app H K. Qed.
Lemma bind_EnumQ_pointwise_proper {A} {B : eqType} (mu : EnumQ A) (k h : A -> EnumQ B) :
  (forall a, k a ==EnumQ h a) -> bind_EnumQ mu k ==EnumQ bind_EnumQ mu h.
Proof.
  move=> H b; rewrite !acc_mass_bind_EnumQ.
  apply finite_expect_ext=> x; exact (H x b).
Qed.

Definition bind_offset {A B} (mu : EnumQ A) (k : A -> EnumQ B) i :=
  finite_bind_offset (enumQ_raw mu) (fun x => enumQ_raw (k x)) i.
Lemma size_scale_EnumQ {A} p (Hp : 0 <= p) (mu : EnumQ A) :
  size (enumQ_raw (scale_EnumQ Hp mu)) = size (enumQ_raw mu).
Proof. exact: size_map. Qed.
Lemma nth_error_scale_EnumQ {A} p (Hp : 0 <= p) (mu : EnumQ A) i q a :
  nth_error (enumQ_raw mu) i = Some (q,a) ->
  nth_error (enumQ_raw (scale_EnumQ Hp mu)) i = Some (p*q,a).
Proof.
  change (nth_error (enumQ_raw mu) i = Some (q,a) ->
    nth_error (finite_weight_map p (enumQ_raw mu)) i = Some (p*q,a)).
  rewrite -finite_scale_with_weight_map; exact: finite_scale_with_nth.
Qed.
Lemma nth_error_scale_EnumQ_inv {A} p (Hp : 0 <= p) (mu : EnumQ A) i w a :
  nth_error (enumQ_raw (scale_EnumQ Hp mu)) i = Some (w,a) ->
  exists q, nth_error (enumQ_raw mu) i = Some (q,a) /\ w = p*q.
Proof.
  change (nth_error (finite_weight_map p (enumQ_raw mu)) i = Some (w,a) ->
    exists q, nth_error (enumQ_raw mu) i = Some (q,a) /\ w = p*q).
  rewrite -finite_scale_with_weight_map; exact: finite_scale_with_nth_inv.
Qed.
Lemma nth_error_app_right {A} (xs ys : list A) i y :
  nth_error ys i = Some y ->
  nth_error (xs++ys) (size xs+i)%N = Some y.
Proof. exact: finite_nth_app_right. Qed.
Lemma nth_error_app_left {A} (xs ys : list A) i x :
  nth_error xs i = Some x -> nth_error (xs++ys) i = Some x.
Proof. exact: finite_nth_app_left. Qed.
Lemma nth_error_app_inv {A} (xs ys : list A) n z :
  nth_error (xs++ys) n = Some z ->
  (Peano.lt n (size xs) /\ nth_error xs n = Some z) \/
  exists j, n = (size xs+j)%N /\ nth_error ys j = Some z.
Proof. exact: finite_nth_app_inv. Qed.

Lemma nth_error_bind_EnumQ {A B} (mu : EnumQ A) (k : A -> EnumQ B) i j p a q b :
  nth_error (enumQ_raw mu) i = Some (p,a) ->
  nth_error (enumQ_raw (k a)) j = Some (q,b) ->
  nth_error (enumQ_raw (bind_EnumQ mu k)) (bind_offset mu k i+j)%N = Some (p*q,b).
Proof.
  change (nth_error (enumQ_raw mu) i = Some (p,a) ->
    nth_error (enumQ_raw (k a)) j = Some (q,b) ->
    nth_error (finite_bind (enumQ_raw mu) (fun x => enumQ_raw (k x)))
      (bind_offset mu k i+j)%N = Some (p*q,b)).
  rewrite -finite_bind_with_numeric; exact: finite_bind_with_nth.
Qed.
Lemma nth_error_bind_EnumQ_inv {A B} (mu : EnumQ A) (k : A -> EnumQ B) n w b :
  nth_error (enumQ_raw (bind_EnumQ mu k)) n = Some (w,b) ->
  exists i j p a q, nth_error (enumQ_raw mu) i = Some (p,a) /\
    nth_error (enumQ_raw (k a)) j = Some (q,b) /\
    n = (bind_offset mu k i+j)%N /\ w = p*q.
Proof.
  change (nth_error (finite_bind (enumQ_raw mu) (fun x => enumQ_raw (k x))) n = Some (w,b) ->
    exists i j p a q, nth_error (enumQ_raw mu) i = Some (p,a) /\
      nth_error (enumQ_raw (k a)) j = Some (q,b) /\
      n = (bind_offset mu k i+j)%N /\ w = p*q).
  rewrite -finite_bind_with_numeric; exact: finite_bind_with_nth_inv.
Qed.

Lemma enumQ_Fubini_Tonelli {A B : eqType} (mu : EnumQ A) (nu : EnumQ B) :
  bind_EnumQ mu (fun x => bind_EnumQ nu (fun y => ret_EnumQ (x,y))) ==EnumQ
  bind_EnumQ nu (fun y => bind_EnumQ mu (fun x => ret_EnumQ (x,y))).
Proof.
  move=> z; change
    (enumQ_expect (fun xy => if xy == z then 1 else 0)
      (bind_EnumQ mu (fun x => bind_EnumQ nu (fun y => ret_EnumQ (x,y)))) =
     enumQ_expect (fun xy => if xy == z then 1 else 0)
      (bind_EnumQ nu (fun y => bind_EnumQ mu (fun x => ret_EnumQ (x,y))))).
  rewrite !enumQ_expect_bind.
  transitivity (enumQ_expect (fun x => enumQ_expect
    (fun y => if (x,y) == z then 1 else 0) nu) mu).
  - apply finite_expect_ext=> x; rewrite enumQ_expect_bind.
    apply finite_expect_ext=> y; exact: enumQ_expect_ret.
  - rewrite /enumQ_expect /finite_enum_expect finite_expect_swap.
    apply finite_expect_ext=> y; symmetry.
    change (enumQ_expect (fun xy => if xy == z then 1 else 0)
      (bind_EnumQ mu (fun x => ret_EnumQ (x,y))) =
      enumQ_expect (fun x => if (x,y) == z then 1 else 0) mu).
    rewrite enumQ_expect_bind; apply finite_expect_ext=> x; exact: enumQ_expect_ret.
Qed.
