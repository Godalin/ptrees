(** Atom mass for finite ordinary-scalar lists. These are algebraic identities,
    not a new equality or coupling relation. Repeated atoms are summed; the
    original representation is never rewritten into a deduplicated list. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq fintype bigop ssralg ssrnum order.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section FiniteAtoms.
Variable R : numDomainType.

Definition finite_atom {A : eqType} (x : A) (mu : list (R * A)) : R :=
  finite_expect (fun y => if y == x then 1 else 0) mu.

Lemma finite_atom_nil {A : eqType} (x : A) : finite_atom x [::] = 0.
Proof. reflexivity. Qed.

Lemma finite_atom_cons {A : eqType} (x y : A) p mu :
  finite_atom x ((p,y)::mu) = (if y == x then p else 0) + finite_atom x mu.
Proof. rewrite /finite_atom /=; by case: (y == x); rewrite ?mulr0 ?mulr1. Qed.

Lemma finite_atom_app {A : eqType} (x : A) mu nu :
  finite_atom x (mu ++ nu) = finite_atom x mu + finite_atom x nu.
Proof. exact: finite_expect_app. Qed.

Lemma finite_atom_scale {A : eqType} (x : A) p mu :
  finite_atom x (finite_weight_map p mu) = p * finite_atom x mu.
Proof. exact: finite_expect_weight_map. Qed.

Lemma finite_atom_bind {A} {B : eqType} (x : B) (mu : list (R * A)) k :
  finite_atom x (finite_bind mu k) = finite_expect (fun a => finite_atom x (k a)) mu.
Proof. exact: finite_expect_bind. Qed.

Lemma finite_atom_nonnegative {A : eqType} (x : A) mu :
  finite_nonnegative mu -> 0 <= finite_atom x mu.
Proof.
  move=> H; apply finite_expect_nonnegative; first exact H.
  move=> y; case: (y == x); [exact: ler01|exact: lexx].
Qed.

Lemma finite_expect_by_atoms {A : finType} (mu : list (R * A)) f :
  finite_expect f mu = \sum_x finite_atom x mu * f x.
Proof.
  elim: mu=> [|[p a] mu IH].
  - rewrite /= big1 // => x _. exact: mul0r.
  - rewrite /= IH. transitivity
      (\sum_x ((if a == x then p else 0) * f x + finite_atom x mu * f x)).
    + rewrite big_split. apply congr1 with (f := fun z => z + \sum_x finite_atom x mu * f x).
      transitivity (\sum_x (if a == x then p * f x else 0)).
      * by rewrite -big_mkcond (big_pred1 a).
      * apply eq_bigr=> x _. by case: (a == x); rewrite ?mul0r.
    + apply eq_bigr=> x _. by rewrite finite_atom_cons mulrDl.
Qed.

Lemma finite_mass_by_atoms {A : finType} (mu : FiniteEnum R A) :
  finite_mass mu = \sum_x finite_atom x (finite_enum_raw mu).
Proof.
  rewrite /finite_mass /finite_enum_expect finite_expect_by_atoms.
  apply eq_bigr=> x _; exact: mulr1.
Qed.

Lemma finite_expect_atoms_ext {A : finType} (mu nu : list (R * A)) f :
  (forall x, finite_atom x mu = finite_atom x nu) -> finite_expect f mu = finite_expect f nu.
Proof. move=> H; rewrite !finite_expect_by_atoms; apply eq_bigr=> x _; by rewrite H. Qed.

(** A finite carrier is unnecessary: the finite list supplies its own cover.
    This is purely algebraic and also holds for signed raw weightings. *)
Lemma finite_atom_delta_sum {A : eqType} (xs : list A) a (c : R) :
  uniq xs -> a \in xs -> \sum_(x <- xs) (if a == x then c else 0) = c.
Proof.
  move=> Hu Ha; rewrite (bigD1_seq a Ha Hu) eq_refl.
  have Hz : \sum_(x <- xs | x != a) (if a == x then c else 0) = 0.
  { apply big1=> x Hx; by rewrite eq_sym (negbTE Hx). }
  rewrite Hz; change (c + 0 = c); exact: addr0.
Qed.

Lemma finite_expect_by_cover {A : eqType} (mu : list (R*A)) (xs : list A) f :
  uniq xs -> (forall p x, List.In (p,x) mu -> x \in xs) ->
  finite_expect f mu = \sum_(x <- xs) finite_atom x mu * f x.
Proof.
  move=> Hu; elim: mu=> [|[p a] mu IH] Hcover.
  - rewrite /= big1 // => x _; exact: mul0r.
  - have Ha := Hcover p a (or_introl (Logic.eq_refl _)).
    have Htail : forall q x, List.In (q,x) mu -> x \in xs.
    { move=> q x H; exact (Hcover q x (or_intror H)). }
    rewrite /= (IH Htail).
    transitivity (\sum_(x <- xs)
      ((if a == x then p else 0)*f x + finite_atom x mu*f x)).
    + rewrite big_split; congr (_ + _).
      transitivity (\sum_(x <- xs) (if a == x then p*f a else 0)).
      * symmetry; exact (finite_atom_delta_sum (p*f a) Hu Ha).
      * apply eq_bigr=> x _; case Hax: (a == x).
        -- by move/eqP: Hax=> ->.
        -- by rewrite mul0r.
    + apply eq_bigr=> x _; by rewrite finite_atom_cons mulrDl.
Qed.

Lemma finite_raw_value_mem {A : eqType} (mu : list (R*A)) p x :
  List.In (p,x) mu -> x \in [seq px.2 | px <- mu].
Proof.
  elim: mu=> [|[q y] mu IH]; first by move=> [].
  move=> [He|H]; rewrite /= in_cons; apply/orP.
  - inversion He; subst; left; exact: eqxx.
  - right; exact (IH H).
Qed.

Lemma finite_expect_atoms_eq {A : eqType} (mu nu : list (R*A)) f :
  (forall x, finite_atom x mu = finite_atom x nu) ->
  finite_expect f mu = finite_expect f nu.
Proof.
  move=> H; pose xs := undup ([seq px.2 | px <- mu] ++ [seq px.2 | px <- nu]).
  have Hu : uniq xs := undup_uniq _.
  have Hmu : forall p x, List.In (p,x) mu -> x \in xs.
  { move=> p x Hin; rewrite /xs mem_undup mem_cat; apply/orP; left.
    exact (finite_raw_value_mem Hin). }
  have Hnu : forall p x, List.In (p,x) nu -> x \in xs.
  { move=> p x Hin; rewrite /xs mem_undup mem_cat; apply/orP; right.
    exact (finite_raw_value_mem Hin). }
  rewrite (finite_expect_by_cover f Hu Hmu) (finite_expect_by_cover f Hu Hnu).
  apply eq_bigr=> x _; by rewrite H.
Qed.
Lemma finite_expect_atom_split {A : eqType} (mu : list (R*A)) f a :
  finite_expect f mu = finite_atom a mu * f a +
    finite_expect f (List.filter (fun px => px.2 != a) mu).
Proof.
  elim: mu=> [|[p x] tl IH]; first by rewrite /= mul0r add0r.
  rewrite /= finite_atom_cons; case H: (x == a)=> /=.
  - move/eqP: H=> H; subst x; by rewrite IH mulrDl addrA.
  - by rewrite IH add0r addrCA.
Qed.
End FiniteAtoms.
