(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8.
Require Import Setoid.
Require Import Program.
Require Import Morphisms.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq ssrfun.
From mathcomp Require Import order ssralg ssrint rat.

Require Import PTree.Prob.Backend.Common.RatSubTypes.
From PTree.Prob.Backend.Common Require Import FiniteListAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Open Scope subrat_scope.

(** The Inference Problem Representation for discrete cases *)
Section Interface.
Import NonnegQNotations.

(* The semantics is defined as [Mass] functions. *)
(* Definition Mass (X : Type) := X → ℚ≥0. *)

(* Record Mass_Monad := *)
(*   { ret_mass := fun A x y => if x == y then 1 else 0 *)
(*   ; bind_mass := fun A B f g x => fun y => f x y * g y; *)
(*   }. *)



Class Discrete (m : Type → Type) := {
  disc_ret : forall {A}, A → m A;
  disc_bind : forall {A B}, m A → (A → m B) → m B;
  disc_flip : () → m bool;
  disc_score : nnQ → m ()%type;
}.

(** Discrete Laws:
  bind (ret x) f ≃ f x
  bind m ret ≃ m
  bind m (λ x, bind (f x) g) ≃ bind (bind m f) g
  bind m (λ x, bind n (λ y, f x y)) ≃ bind n (λ y, bind m (λ x, f x y))
  *)

Class DiscreteLaws (m : Type → Type) `{Discrete m}
  (R : forall {a}, m a → m a → Prop) :=

  { disc_ret_bind : forall A B (x : A) (f : A → m B),
    R (disc_bind (disc_ret x) f) (f x)

  ; disc_bind_ret : forall A (u : m A),
    R (disc_bind u disc_ret) u

  ; disc_bind_assoc : forall A B C (u : m A) (f : A → m B) (g : B → m C),
    R (disc_bind u (λ x, disc_bind (f x) g))
      (disc_bind (disc_bind u f) g)

  ; disc_comm_law : forall A B C (u : m A) (v : m B) (f : A → B → m C),
    R (disc_bind u (λ x, disc_bind v (λ y, f x y)))
      (disc_bind v (λ y, disc_bind u (λ x, f x y)))
  }.

Class DiscreteInterface (M : Type → Type) : Type :=
  { disc_rep :: Discrete M

  (* ; disc_laws :: DiscreteLaws *)

  (** The equality for discrete representations *)
  ; disc_eq : ∀ {R : eqType}, M R → M R → Prop

  (** The equality should be some [Equivalence] *)
  ; disc_eq_equiv :: ∀ R : eqType,
      Equivalence (@disc_eq R)

  (** We need a relation transformer *)
  ; disc_RT : ∀ {R1 R2 : eqType},
      (R1 → R2 → Prop) → M R1 → M R2 → Prop

  (** The transformed [disc_RT eq] should coincide with [disc_eq] *)
  ; disc_RTeq : ∀ (R : eqType) (μ1 μ2 : M R),
      disc_eq μ1 μ2 ↔ disc_RT eq μ1 μ2

  (** A mass operator for getting the probability mass *)
  ; disc_mass {R : eqType} : R → M R → nnQ

  (** The mass operator should be proper.  *)
  ; disc_mass_proper {R : eqType} {x : R} ::
      Proper (disc_RT eq ==> eq) (disc_mass x)

  (** supp *)
  ; disc_supp {R : eqType} : M R → seq R
  }.

Context {M : Type → Type}.
Context `{DiscreteInterface M}.

(** "easy-to-use" [Equivalence] for [disc_RT] when  is given *)
#[global] Instance dist_RT_equiv {X : eqType}
  : @Equivalence (M X) (disc_RT eq).
Proof. split.
  - unfold Reflexive. intros. apply disc_RTeq. reflexivity.
  - unfold Symmetric. intros. apply disc_RTeq. symmetry.
    apply disc_RTeq. assumption.
  - unfold Transitive. intros. apply disc_RTeq.
    etransitivity; apply disc_RTeq; eassumption.
Qed.

End Interface.



(** The [Term] Representation *)
Module Term.
Import NonnegQNotations.

Inductive Term (A : Type) :=
  | Return : nnQ → A → Term A
  | Flip : Term A → Term A → Term A.

Arguments Return {A} _ _.
Arguments Flip {A} _ _.

Fixpoint scale_Term {A} (s : nnQ) (t : Term A) : Term A :=
  match t with
  | Return p x => Return (s * p) x
  | Flip k_false k_true =>
    Flip (scale_Term s k_false) (scale_Term s k_true)
  end.

Fixpoint bind_Term {A B} (a : Term A) (f : A → Term B) :=
  match a with
    | Return r x => scale_Term r (f x)
    | Flip k_true k_false =>
      Flip (bind_Term k_true f) (bind_Term k_false f)
  end.

#[global]
Instance Term_Discrete : Discrete Term :=
  {|disc_ret := λ A x, Return 1 x
  ; disc_bind := @bind_Term
  ; disc_flip := λ _, Flip
      (Return 1 true)
      (Return 1 false)
  ; disc_score := λ r : ℚ≥0, Return r tt
  |}.

End Term.





(** The [EnumQ] Representation *)
Module EnumQ.
Import NonnegQNotations.
Import GRing.Theory.
Import Order.Theory.

Definition EnumQ (A : Type) := seq (ℚ≥0 * A).

Declare Scope enumQ_scope.
Bind Scope enumQ_scope with EnumQ.
Delimit Scope enumQ_scope with enumQ.
#[local] Open Scope enumQ_scope.

Definition scale_EnumQ {A} (r : ℚ≥0) (e : EnumQ A) : EnumQ A :=
  finite_scale_with (fun p q => p * q) r e.

Lemma scale_app : ∀ A r (u v : EnumQ A),
  scale_EnumQ r (u ++ v) = scale_EnumQ r u ++ scale_EnumQ r v.
Proof. exact: finite_scale_with_app. Qed.

Lemma scale_scale : ∀ {A} r s (u : EnumQ A),
  scale_EnumQ r (scale_EnumQ s u) = scale_EnumQ (r * s) u.
Proof. move=> A r s u; apply finite_scale_with_comp=> p q t; exact: mulrA. Qed.

Definition ret_EnumQ {A} (x : A) : EnumQ A := [:: (1, x)].

Definition bind_EnumQ {A B} (xs : EnumQ A) (f : A → EnumQ B) : EnumQ B :=
  finite_bind_with (fun p q => p * q) xs f.

#[global] Instance EnumQ_Discrete : Discrete EnumQ :=
  {|disc_ret := @ret_EnumQ
  ; disc_bind := @bind_EnumQ
  ; disc_flip := λ _, [:: (1, true); (1, false)]
  ; disc_score := λ r, [:: (r, tt)]
  |}.


Definition scale_bind : ∀ {A B} r (u : EnumQ A) (f : A → EnumQ B),
  scale_EnumQ r (bind_EnumQ u f) = bind_EnumQ u (λ x, scale_EnumQ r (f x)).
Proof.
  move=> A B r u f; apply finite_scale_with_bind.
  - move=> p q t; exact: mulrA.
  - move=> p q; exact: mulrC.
Qed.



(** We need the decidable equality for the base type [A] of
    the enumeration. *)

Definition sumq (l : seq ℚ≥0) : ℚ≥0
  := foldr (λ (x acc : ℚ≥0), x + acc) 0 l.

Lemma sumq_cons {x : ℚ≥0} {l : seq ℚ≥0} : sumq (x :: l) = x + sumq l.
Proof. unfold sumq, foldr. reflexivity. Qed.

Lemma sumq_app {l1 l2 : seq ℚ≥0} : sumq (l1 ++ l2) = sumq l1 + sumq l2.
Proof. rewrite /sumq. elim: l1 => [//=| x s iH //=]. rewrite add0r //=.
rewrite iH //= addrA. reflexivity. Qed.

Lemma sumq_nil : sumq [::] = 0.
Proof. cbn. reflexivity. Qed.

Lemma sumq_filter_0 {l : seq ℚ≥0} : sumq [seq i <- l | i == 0] = 0.
Proof.
  elim : l => [//=|a l IH]. rewrite /filter. remember (a == 0) as a_0.
  case: a_0 Heqa_0 => [a_eq_0|a_ne_0].
  - symmetry in a_eq_0. rewrite a_eq_0 sumq_cons IH addr0 (eqP a_eq_0) //=.
  - rewrite -a_ne_0 IH //=.
Qed.


Lemma sumq_ne_0_cons {l : seq ℚ≥0} {a: ℚ≥0} : a != 0 -> sumq (a :: l) != 0.
Proof.
  move => a_ne_0. rewrite sumq_cons. exact: (ne0_of_ne0_add a_ne_0).
Qed.


Definition acc_mass {A : eqType} (x : A) (μ : EnumQ A) : ℚ≥0
  := sumq (unzip1 [seq i <- μ | snd i == x]).

Definition mass {X : eqType} (μ : EnumQ X) (s : seq X) : ℚ≥0
  := sumq [seq acc_mass x μ | x <- s].

Lemma acc_mass_nil {A : eqType} {x : A} : acc_mass x ([::] : EnumQ A) = 0.
Proof. cbn. reflexivity. Qed.

Lemma mass_nil {A : eqType} (μ : EnumQ A) : mass μ [::] = 0.
Proof. cbn. reflexivity. Qed.

Definition enumQk {Y} {X : eqType} (μ : EnumQ X) (k : X → Y) (x : X) : ℚ≥0 * Y
  := (acc_mass x μ, k x).

Lemma acc_nil : ∀ (A : eqType) (x : A), acc_mass x [::] = 0.
Proof. move=> //=. Qed.

Lemma acc_app {A : eqType} {x : A} {μ1 μ2 : EnumQ A}
  : acc_mass x (μ1 ++ μ2) = acc_mass x μ1 + acc_mass x μ2.
Proof. rewrite /acc_mass filter_cat /unzip1 map_cat sumq_app //=. Qed.

Definition EqEnumQ {A : eqType} (μ1 μ2 : EnumQ A) : Prop :=
  ∀ x : A, acc_mass x μ1 = acc_mass x μ2.

Infix "==EnumQ" := EqEnumQ (at level 70).

Lemma enumQ_eq_eq {A : eqType} : ∀ {μ1 μ2 : EnumQ A},
  μ1 = μ2 → EqEnumQ μ1 μ2.
Proof. intros. unfold EqEnumQ. intros.
  rewrite H. reflexivity.
Qed.

Lemma enumQ_eq_refl : ∀ {A : eqType} {μ : EnumQ A},
  μ ==EnumQ μ.
Proof. intros. unfold EqEnumQ. intros. reflexivity. Qed.

Lemma enumQ_eq_sym {A : eqType} : ∀ {μ ν : EnumQ A},
  μ ==EnumQ ν → ν ==EnumQ μ.
Proof. intros. unfold EqEnumQ. intros. symmetry. apply H. Qed.

Lemma enumQ_eq_trans {A : eqType} : ∀ {x y z : EnumQ A},
  x ==EnumQ y → y ==EnumQ z → x ==EnumQ z.
Proof. intros. unfold EqEnumQ. intros. etransitivity; eauto. Qed.



#[global] Instance enumQ_eq_equiv {A : eqType}
  : @Equivalence (EnumQ A) EqEnumQ.
Proof. split. unfold Reflexive. intros. apply enumQ_eq_refl.
  unfold Symmetric. intros. now apply enumQ_eq_sym.
  unfold Transitive. intros. now eapply enumQ_eq_trans.
Qed.

Add Parametric Morphism {A : eqType} : (@app (ℚ≥0 * A))
  with signature EqEnumQ ==> EqEnumQ ==> EqEnumQ
  as app_proper.
Proof. intros. intros a. repeat rewrite acc_app.
  rewrite H. rewrite H0. reflexivity.
Qed.



Lemma app_comm {A : eqType} (u v : EnumQ A) : u ++ v ==EnumQ v ++ u.
Proof. unfold EqEnumQ. intros. induction u.
  simpl. now rewrite cats0. destruct a.
  repeat rewrite acc_app. rewrite addrC //.
Qed.

Lemma enumQ_nil_bind : ∀ A B (f : A → EnumQ B),
  bind_EnumQ [:: ] f = [:: ].
Proof. intros. simpl. reflexivity. Qed.

Lemma enumQ_cons_bind : ∀ A B x r (u : EnumQ A) (f : A → EnumQ B),
  bind_EnumQ ((r, x) :: u) f = scale_EnumQ r (f x) ++ bind_EnumQ u f.
Proof. intros. simpl. reflexivity. Qed.

Lemma enumQ_bind_nil : ∀ A B (u : EnumQ A),
  bind_EnumQ u (λ _, [::] : EnumQ B) = [::].
Proof.
  intros. simpl. induction u.
  now simpl. destruct a. rewrite enumQ_cons_bind.
  now simpl.
Qed.

Lemma enumQ_bind_app : ∀ A {B : eqType} (u : EnumQ A) (f g : A → EnumQ B),
  bind_EnumQ u (λ x, (f x) ++ (g x))
    ==EnumQ
  bind_EnumQ u (λ x, f x) ++ bind_EnumQ u (λ x, g x).
Proof. intros. induction u. now simpl.
  destruct a. repeat rewrite enumQ_cons_bind.
  rewrite scale_app. rewrite IHu. repeat rewrite <- catA.
  rewrite (catA (bind_EnumQ u (λ x : A, f x))).
  rewrite (app_comm (bind_EnumQ u (λ x : A, f x)) (scale_EnumQ n (g a))).
  repeat rewrite <- catA. reflexivity.
Qed.

Lemma enumQ_comm_nil : ∀ A B C (v : EnumQ B) (f : A → B → EnumQ C),
  bind_EnumQ [::] (λ x, bind_EnumQ v (λ y, f x y)) =
  bind_EnumQ v (λ y, bind_EnumQ [::] (λ x, f x y)).
Proof.
  intros A B C v f.
  rewrite enumQ_bind_nil. simpl. reflexivity.
Qed.

Lemma enumQ_comm_cons : ∀
  {A : eqType} {B : eqType} {C : eqType} r a
  (u : EnumQ A) (v : EnumQ B) (f : A → B → EnumQ C),
    bind_EnumQ ((r, a) :: u) (λ x, bind_EnumQ v (λ y, f x y))
      ==EnumQ
    bind_EnumQ v (λ y, bind_EnumQ ((r, a) :: u) (λ x, f x y)).
Proof.
  intros. rewrite enumQ_cons_bind.
  induction v.
  - simpl. rewrite enumQ_bind_nil. now apply enumQ_eq_eq.
  - destruct a0. rewrite !enumQ_cons_bind. repeat rewrite scale_app.
    repeat rewrite enumQ_bind_app.
    repeat rewrite <- catA.
    rewrite (catA (scale_EnumQ r (bind_EnumQ v (λ y : B, f a y)))).
    rewrite (app_comm (scale_EnumQ r (bind_EnumQ v (λ y : B, f a y)))).
    rewrite <- catA.
    rewrite IHv. repeat rewrite scale_scale.
    rewrite scale_bind. rewrite enumQ_bind_app.
    apply enumQ_eq_eq. congr app. congr scale_EnumQ.
    rewrite mulrC //.
Qed.

Theorem enumQ_Fubini_Tonelli : ∀
  {A : eqType} {B : eqType} {C : eqType}
  (u : EnumQ A) (v : EnumQ B) (f : A → B → EnumQ C),
    bind_EnumQ u (λ x, bind_EnumQ v (λ y, f x y))
      ==EnumQ
    bind_EnumQ v (λ y, bind_EnumQ u (λ x, f x y)).
Proof. destruct u.
  - intros. apply enumQ_eq_eq. apply enumQ_comm_nil.
  - intros. destruct p. now eapply enumQ_comm_cons.
Qed.

(** * the relation transformer for [EnumQ] *)

Definition enumQRT {R1 : eqType} {R2 : eqType}
    (RR : R1 → R2 → Prop) : EnumQ R1 → EnumQ R2 → Prop
  := λ μx μy, ∀ x y, RR x y → acc_mass x μx = acc_mass y μy.

Infix "==EnumQRT" := (enumQRT _) (at level 70).

Lemma enumRT_eq {R : eqType} {a b}: @enumQRT R R eq a b <-> EqEnumQ a b.
Proof.
  rewrite /enumQRT /EqEnumQ. split.
  - move => h1 x. eapply h1. by [].
  - move => h1 x y x_eq_y. rewrite -x_eq_y. exact: (h1 x).
Qed.

(** Convenient Distribution Constructors *)
Section Dists.

Definition dirac {A} (x : A) : EnumQ A :=
  ret_EnumQ x.

#[program] Definition one_div_two := [nn 1/2].
#[program] Definition one_div_three := [nn 1/3].

Definition unif2 {A} (x y : A) : EnumQ A :=
  [:: (one_div_two, x); (one_div_two, y)].

Definition unif3 {A} (x y z : A) : EnumQ A :=
  [:: (one_div_three, x); (one_div_three, y); (one_div_three, z)].

End Dists.



Section int.

Definition integral {A : eqType} (f : A → ℚ≥0) (μ : EnumQ A)
  := foldr (λ '(p, x) s, (f x) * p + s) 0.

End int.



(* Properties about Support Set *)

Section Supp.

Lemma eta {A : eqType} (μ : EnumQ A)
  : μ = [seq (p, x) | '(p, x) <- μ].
Proof. elim: μ => [//|[p x] μ IH]. rewrite map_cons.
congr cons. exact: IH.
Qed.

Definition supp {A : eqType} (μ : EnumQ A)
  := undup (unzip2 [seq i <- μ | i.1 != 0]).

Lemma supp_uniq {A : eqType} (μ : EnumQ A) : uniq (supp μ).
Proof. apply: undup_uniq. Qed.

Lemma supp_spec {A: eqType} (μ : EnumQ A)
  : (supp μ =i unzip2 [seq i <- μ | i.1 != 0]).
Proof. apply: mem_undup. Qed.

Lemma supp_nil {A : eqType} : supp ([::] : EnumQ A) = [::].
Proof. cbn. reflexivity. Qed.

Lemma sumq_filter {A} {C : A -> nnQ} (l : seq A) (P : A -> bool) : sumq (map C l) = sumq [seq C i  | i <- l  & P i] + sumq [seq C i  | i <- l  & ~~ P i].
Proof.
  induction l. rewrite //= addr0 //=.
  rewrite map_cons /filter. case: (P a).
  - rewrite //= IHl addrA //=.
  - rewrite //= IHl addrA addrA (addrC (C a) (sumq [seq C i  | i <- l  & P i])) //=.
Qed.

Lemma filter_cons {A} {l: seq A} {a : A} {P: A -> bool}: filter P (a :: l) = if P a then a :: filter P l else filter P l.
Proof. reflexivity. Qed.

Lemma undup_cons {A: eqType} {l: seq A} {a : A}: undup (a :: l) = if a \in l then undup l else a :: undup l.
Proof. reflexivity. Qed.

Lemma undup_filter_item {A: eqType} {l: seq A} {a : A} : undup [seq i <- l | i == a] = if a \in l then [:: a] else [::].
Proof.
  elim/last_ind: l => [//=|l x IH]. rewrite filter_rcons. remember (x == a) as x_a. elim : x_a Heqx_a => [x_eq_a | x_ne_a].
  - rewrite undup_rcons IH mem_rcons in_cons. rewrite eq_sym in x_eq_a. rewrite -x_eq_a //=.
    remember (a \in l) as a_in_l. case: a_in_l Heqa_in_l IH => [Heqa_in_l IH //= | Heqa_in_l IH //=].
    rewrite -x_eq_a //=. clear - x_eq_a. symmetry in x_eq_a. rewrite (eqP x_eq_a) //=. symmetry in x_eq_a. rewrite (eqP x_eq_a) //=.
  - rewrite IH mem_rcons in_cons. rewrite eq_sym in x_ne_a. rewrite -x_ne_a //=.
Qed.

Lemma acc_mass_cons {A : eqType} {μ : EnumQ A} {a : A} {h : nnQ * A} : acc_mass a (h :: μ) = acc_mass a μ + if h.2 == a then h.1 else 0.
Proof.
  rewrite /acc_mass filter_cons.
  remember (h.2 == a) as snd_h_a. destruct snd_h_a.
  - rewrite /unzip1 map_cons sumq_cons addrC //=.
  - rewrite addr0 //=.
Qed.

Lemma acc_mass_cons_zero {A : eqType} {μ : EnumQ A} {a : A} {h : nnQ * A} : h.1 = 0 -> acc_mass a (h :: μ) = acc_mass a μ.
Proof.
  move =>eq_0. rewrite acc_mass_cons eq_0.
  case : (h.2 == a). rewrite addr0 //=. rewrite addr0 //=.
Qed.

Lemma predI_comm {T} (p1 p2 : pred T) : predI p1 p2 = predI p2 p1.
Proof.
  rewrite /predI /xpredI. congr SimplPred.
  apply functional_extensionality. move => x. exact: Bool.andb_comm.
Qed.

Lemma notin_supp_iff_acc_mass_eq_0 {A : eqType} (x : A) (μ : EnumQ A) : x \notin (supp μ) <-> acc_mass x μ = 0.
Proof.
  split.
  + move => h. rewrite /acc_mass. rewrite /supp mem_undup /unzip2 in h.
    elim: μ h => [//= | h t ih x_notin].
    rewrite filter_cons in x_notin.
    remember (h.1 != 0) as h_0. elim : h_0 Heqh_0 => [h_eq_0 | h_ne_0].
    - rewrite -{}h_eq_0 in x_notin. rewrite map_cons in_cons in x_notin.
      move : x_notin => /norP [x_ne_h x_not_in]. move : ih => /(_ x_not_in) ih. rewrite {x_not_in}.
      rewrite /is_true Bool.negb_true_iff eq_sym in x_ne_h. rewrite filter_cons x_ne_h. exact: ih.
    - symmetry in h_ne_0. rewrite h_ne_0 in x_notin. move : ih => /(_ x_notin) ih. rewrite filter_cons.
      remember (h.2 == x) as h_x. elim : h_x Heqh_x => [h_eq_x | h_ne_x].
      + rewrite /unzip1 map_cons sumq_cons ih addr0. rewrite Bool.negb_false_iff in h_ne_0. exact: eqP h_ne_0.
      + exact: ih.
  + move => acc_mass_eq_zero. apply/negP. rewrite /supp mem_undup /unzip2.
    elim : μ acc_mass_eq_zero => [//= | a l IH acc_mass_eq_0 x_in_cons].
    rewrite filter_cons in x_in_cons. rewrite /acc_mass /unzip1 filter_cons in acc_mass_eq_0.
    remember (a.2 == x) as a_x. case : a_x Heqa_x acc_mass_eq_0 => [a_eq_x acc_mass_eq_0 | a_ne_x acc_mass_eq_0].
    - rewrite map_cons in acc_mass_eq_0. remember (a.1 == 0) as a_0. 
      case : a_0 Heqa_0 acc_mass_eq_0 => [a_eq_0 acc_mass_eq_0 | a_ne_0 acc_mass_eq_0].
      + symmetry in a_eq_0. rewrite a_eq_0 //= in x_in_cons. move : a_eq_0 => /eqP a_eq_0. rewrite sumq_cons a_eq_0 add0r in acc_mass_eq_0.
        move : IH => /(_ acc_mass_eq_0 x_in_cons) IH. exact: IH.
      + rewrite -a_ne_0 //= in x_in_cons. move : acc_mass_eq_0. apply/eqP. apply sumq_ne_0_cons. rewrite -a_ne_0 //=.
    - remember (a.1 == 0) as a_0. case : a_0 Heqa_0 acc_mass_eq_0 => [a_eq_0 acc_mass_eq_0 | a_ne_0 acc_mass_eq_0].
      + rewrite -a_eq_0 //= in x_in_cons. move : IH => /(_ acc_mass_eq_0 x_in_cons) IH. exact: IH.
      + rewrite -a_ne_0 //= in_cons eq_sym -a_ne_x //= in x_in_cons. move : IH => /(_ acc_mass_eq_0 x_in_cons) IH. exact: IH.
Qed.

Lemma in_supp_iff_acc_mass_ne_0 {A : eqType} (x : A) (μ : EnumQ A) : x \in (supp μ) <-> acc_mass x μ != 0.
Proof.
  have n := not_iff_compat (notin_supp_iff_acc_mass_eq_0 x μ).
  rewrite /is_true Bool.eq_true_negb_classical_iff in n.
  rewrite /is_true {}n. split. move => l. apply/eqP. exact l.
  move => l. apply/eqP. exact l.
Qed.

Lemma supp_enumQ_eq_mem_eq {A : eqType} : Proper (EqEnumQ (A:= A) ==> eq_mem) (mem \o supp).
Proof.
  rewrite /Proper /respectful /comp //=.
  have : forall x y : EnumQ A, x ==EnumQ y -> forall m, m \in supp x -> m \in supp y. 
  - move => x y x_eq_y m m_in_x. rewrite /EqEnumQ in x_eq_y.
    rewrite in_supp_iff_acc_mass_ne_0 x_eq_y -in_supp_iff_acc_mass_ne_0 in m_in_x.
    exact m_in_x.
  move => lem l1 l2 enumQeq x. rewrite Bool.eq_iff_eq_true. split.
  - apply lem. exact: enumQeq.
  - apply lem. symmetry. exact: enumQeq.
Qed.

Lemma acc_mass_eq_filter_ne_item {A : eqType} {x m : A} (μ : EnumQ A) : x != m → acc_mass x μ = acc_mass x [seq i <- μ | i.2 != m].
Proof.
  move => x_ne_m. rewrite /acc_mass /unzip1 -filter_predI. congr sumq. congr map. apply eq_in_filter.
  move => i hi. rewrite /predI /in_mem //=. symmetry. apply andb_idr. move => /eqP i_eq_x. rewrite -i_eq_x //= in x_ne_m.
Qed.

Lemma seq_strong_induction {A: Type} {P : seq A -> Prop} (Pn : ∀ L, (∀ l, size l < size L -> P l) -> P L ): ∀ l, P l.
Proof.
  enough (H0: ∀ (n: nat) l, lt (size l) n -> P l).
  - move=> l. eapply (H0 (plus 1 (size l))). auto.
  - elim => [l fal| n IHn l sizel_lt_n_add_1].
    + cbn in fal. apply except. exact (PeanoNat.Nat.nle_succ_0 _ fal).
    + eapply (Pn l). move => l' size_l'_lt_l. eapply (IHn l').
      rewrite /is_true -(Bool.reflect_iff _ _ ssrnat.ltP) in size_l'_lt_l.
      rewrite /lt -PeanoNat.Nat.succ_le_mono in sizel_lt_n_add_1.
      exact: (PeanoNat.Nat.le_trans _ _ _ size_l'_lt_l sizel_lt_n_add_1).
Qed.

Lemma mass_eq2_of_mem_eq {A : eqType} {m1 m2 : seq A} {μ : EnumQ A} (mem_eq: m1 =i m2) (uniq_m1: uniq m1) (uniq_m2: uniq m2): mass μ m1 = mass μ m2.
Proof.
  have : size m1 = size m2 => [|size_eq]. rewrite (uniq_size_uniq uniq_m1 mem_eq) in uniq_m2. symmetry. exact: (eqP uniq_m2).
  remember (size m1) as sz. elim: sz m1 m2 Heqsz size_eq mem_eq uniq_m1 uniq_m2 => [m1 m2 Heqsz size_eq mem_eq uniq_m1 uniq_m2|n IH m1 m2 Heqsz size_eq mem_eq uniq_m1 uniq_m2].
  - have : m1 = [::] => [|m1_eq_nil]. move : Heqsz => /eqP Heqsz. rewrite eq_sym size_eq0 in Heqsz. exact: eqP Heqsz.
    have : m2 = [::] => [|m2_eq_nil]. move : size_eq => /eqP size_eq. rewrite eq_sym size_eq0 in size_eq. exact: eqP size_eq.
    rewrite m1_eq_nil m2_eq_nil //=.
  - case: m1 Heqsz uniq_m1 mem_eq => [Heqsz uniq_m1 mem_eq|a m1 Heqsz uniq_m1 mem_eq]. rewrite //= in Heqsz.
    rewrite /mass map_cons sumq_cons. rewrite //= in Heqsz. move : Heqsz => /PeanoNat.Nat.succ_inj Heqsz.
    rewrite /uniq -/uniq in uniq_m1. move : uniq_m1 => /andP [a_notin_m1 uniq_m1]. rewrite -/(mass μ m1) (sumq_filter m2 (fun x => x == a)).
    have : a \in m2 => [|a_in_m2]. move : mem_eq => /(_ a) mem_eq. rewrite in_cons eq_refl //= in mem_eq.
    congr GRing.add.
    + rewrite (filter_pred1_uniq uniq_m2 a_in_m2) //= addr0 //=.
    + apply IH; try assumption.
      - rewrite size_filter. have count_a := count_uniq_mem a uniq_m2. rewrite a_in_m2 //= in count_a.
        have count_eq_add := count_predC (λ i : A, i == a) m2. rewrite -size_eq {}count_a add1n in count_eq_add.
        move : count_eq_add => /PeanoNat.Nat.succ_inj count_eq_add. rewrite count_eq_add //=.
      - move => i. rewrite mem_filter. symmetry. move : mem_eq => /(_ i) mem_eq. rewrite in_cons in mem_eq. rewrite -{}mem_eq.
        rewrite Bool.andb_orb_distrib_r andNb //= andb_idl //=. move => i_in_m. apply/eqP. move => i_eq_a. rewrite /is_true i_eq_a in i_in_m.
        rewrite i_in_m //= in a_notin_m1.
      - apply filter_uniq. exact: uniq_m2.
Qed.

Lemma mass_eq1_of_enumeq {A : eqType} {m : seq A} {μ1 μ2 : EnumQ A} (eq: μ1 ==EnumQ μ2): mass μ1 m = mass μ2 m.
Proof.
  congr sumq. apply eq_in_map. move => i _. rewrite eq //=.
Qed.

Lemma mass_le_of_subset {A : eqType} {m1 m2 : seq A} {μ : EnumQ A} (subset: {subset m1 <= m2}) (uniq_m1: uniq m1) (uniq_m2: uniq m2): mass μ m1 <= mass μ m2.
Proof.
  rewrite /mass (sumq_filter m2 [in m1]).
  have sumeq : sumq [seq acc_mass x μ  | x <- m1] = sumq [seq acc_mass i μ  | i <- m2  & i  \in m1].
  - apply mass_eq2_of_mem_eq; try assumption.
    + move => i. rewrite mem_filter andb_idr //=. exact: subset i.
    + apply filter_uniq. exact: uniq_m2.
  rewrite {}sumeq. apply le_nnQ_of_le_Q. rewrite ssrnum.Num.Theory.lerDl. apply le_nnQ0.
Qed.


Lemma mass_supp_eq_mass_undup {A: eqType} (μ : EnumQ A) : mass μ (supp μ) = mass μ (undup (unzip2 μ)).
Proof.
  rewrite /mass /supp /unzip2. move : μ. apply seq_strong_induction. move => [//= | a l IH].

  have in_map_of_in_map_filter : forall (A: eqType) (a: ℚ≥0 * A) (l:EnumQ A), (a.2 \in [seq i.2  | i <- l  & i.1 != 0] -> a.2 \in [seq i.2  | i <- l]).
  - move => A' a' l' in_filter. exact: (sub_map (mem_subseq (filter_subseq (fun i => i.1 != 0) l')) in_filter).

  have size_lt_cons : forall (A: Type) (a: A) (l: seq A), size l < size (a :: l).
  - rewrite //= /Order.lt /Order.NatOrder.Datatypes_nat__canonical__Order_POrder //=.

  rewrite filter_cons. remember (a.1 == 0) as a_0. elim : a_0 Heqa_0 => [a_eq_0 | a_ne_0].
  - rewrite -a_eq_0 //=. symmetry in a_eq_0.
    rewrite (functional_extensionality _ _ (fun a => (acc_mass_cons_zero (μ:=l) (a:=a) (eqP a_eq_0)))) IH.
    remember (a.2  \in [seq i.2  | i <- l]) as a_l. elim : a_l Heqa_l => [//= | a_notin_l]. rewrite map_cons sumq_cons.
    have: (acc_mass a.2 l = 0) => [|acc_mass_eq_0]. rewrite -notin_supp_iff_acc_mass_eq_0 /supp mem_undup /unzip2.
    have not_in := contra (@in_map_of_in_map_filter A a l). rewrite -a_notin_l //= in not_in. apply not_in. rewrite //=. 
    rewrite acc_mass_eq_0 add0r //=. rewrite size_lt_cons //=.
  - rewrite -a_ne_0 //=. remember (a.2  \in [seq i.2  | i <- l & i.1 != 0]) as a_l. elim : a_l Heqa_l => [a_in_l_ne0 | a_notin_l_ne0].
    + have : [fun x0:ℚ≥0 * A => x0.2 != a.2] = preim snd [fun x0 =>  x0 != a.2] => [|prem_eq]. rewrite //=.
      symmetry in a_in_l_ne0. rewrite a_in_l_ne0 (in_map_of_in_map_filter _ _ _ a_in_l_ne0)
        (sumq_filter (undup [seq i.2  | i <- l  & i.1 != 0]) (fun (i : A) => i == a.2))
        filter_undup filter_undup undup_filter_item a_in_l_ne0 //=
        addr0 filter_map /preim -filter_predI predI_comm filter_predI  //=
        (sumq_filter (undup [seq i.2  | i <- l]) (fun (i : A) => i == a.2))
        filter_undup filter_undup undup_filter_item (in_map_of_in_map_filter _ _ _ a_in_l_ne0) //=
        addr0 filter_map /preim /SimplPred //=. congr GRing.add.
      have : {in undup [seq i.2  | i <- [seq x <- l  | [fun x => x.2 != a.2] x]  & i.1 != 0], 
                (fun i => acc_mass i (a :: l)) =1 (fun i => acc_mass i [seq x <- l  | [fun x =>  x.2 != a.2] x])} 
        => [m hm |transform_map].
        - have : m != a.2 => [| a_ne_m]. 
          + rewrite mem_undup -filter_predI predI_comm filter_predI prem_eq -filter_map mem_filter //= in hm.
            exact: (andP hm).1.
          rewrite (acc_mass_eq_filter_ne_item (a :: l) a_ne_m) filter_cons eq_refl //=.
      rewrite eq_in_map in transform_map. rewrite {}transform_map. rewrite IH. congr sumq. rewrite -eq_in_map. move => m hm.
      have : m != a.2 => [| a_ne_m]. rewrite mem_undup prem_eq -filter_map mem_filter //= in hm. exact: (andP hm).1.
      rewrite (acc_mass_eq_filter_ne_item (a :: l) a_ne_m) filter_cons eq_refl //=.
      rewrite size_filter. eapply le_lt_trans. exact: (count_size _ _). rewrite size_lt_cons //=.
    + rewrite -a_notin_l_ne0. remember (a.2  \in [seq i.2 | i <- l]) as a_l. elim : a_l Heqa_l => [a_in_l | a_notin_l].
      - rewrite map_cons sumq_cons acc_mass_cons eq_refl.
        have : {in undup [seq i.2  | i <- l  & i.1 != 0], (fun x => acc_mass x (a :: l)) =1 (fun x => acc_mass x l)} => [m hm| transform_map].
        + rewrite /acc_mass /unzip1 filter_cons. have : a.2 == m = false => [| a_ne_m].
          - apply/eqP. move => a_eq_m. rewrite -a_eq_m mem_undup in hm. rewrite hm //= in a_notin_l_ne0.
          rewrite a_ne_m //=.
        rewrite eq_in_map in transform_map. rewrite {}transform_map {}IH.
        rewrite (sumq_filter (C:= (fun x => acc_mass x (a :: l))) (undup [seq i.2  | i <- l]) (fun (i : A) => i == a.2)) 
          filter_undup undup_filter_item -a_in_l //= addr0 acc_mass_cons eq_refl //= filter_undup. 
        congr GRing.add. 
        have : {in undup [seq i <- [seq i.2  | i <- l]  | i != a.2], (fun x => acc_mass x (a :: l)) =1 (fun x => acc_mass x l)} => [m hm| transform_map].
        + rewrite acc_mass_cons. have : (a.2 == m) = false => [| a_ne_m]. 
          - rewrite mem_undup mem_filter in hm. move : (andP hm) => [m_ne_a _]. rewrite /is_true Bool.negb_true_iff eq_sym //= in m_ne_a.
          rewrite a_ne_m addr0 //=.
        rewrite eq_in_map in transform_map. rewrite {}transform_map (sumq_filter (undup [seq i.2  | i <- l]) (fun (i : A) => i == a.2))
          filter_undup filter_undup undup_filter_item -a_in_l //= addr0.
        have : acc_mass a.2 l = 0 => [|acc_mass_eq_0].
        + clear - a_notin_l_ne0. rewrite /acc_mass /unzip1 (sumq_filter [seq i <- l | i.2 == a.2] (fun (i : ℚ≥0 * A) => i.1 == 0)).
          have : (fun (i : ℚ≥0 * A) => i.1 == 0) = preim fst (fun x => x == 0 ) => [//=|eq_preim]. rewrite {}eq_preim -filter_map sumq_filter_0 add0r.
          rewrite -filter_predI predI_comm filter_predI. have : {in [seq i <- l  | i.1 != 0], (fun (i: ℚ≥0 * A) => i.2 == a.2) =i pred0 } => [m hm|eq_pred0].
          - rewrite /pred0 /in_mem //=. apply/eqP. move => m_eq_a. have m_eq_a' := map_f snd hm. rewrite m_eq_a /is_true in m_eq_a'.
            rewrite m_eq_a' //= in a_notin_l_ne0.
          rewrite (eq_in_filter eq_pred0) filter_pred0 //=.
        rewrite acc_mass_eq_0 add0r //=. rewrite size_lt_cons //=.
      - rewrite map_cons map_cons sumq_cons sumq_cons. congr GRing.add.
        have : {in undup [seq i.2  | i <- l  & i.1 != 0], (fun x => acc_mass x (a :: l)) =1 (fun x => acc_mass x l)} => [m hm| transform_map].
        + rewrite acc_mass_cons. have : a.2 == m = false => [| a_ne_m]. apply/eqP. move => a_eq_m. rewrite -a_eq_m mem_undup in hm. rewrite hm //= in a_notin_l_ne0.
          rewrite a_ne_m addr0 //=.
        rewrite eq_in_map in transform_map. rewrite {}transform_map.
        have : {in undup [seq i.2  | i <- l], (fun x => acc_mass x (a :: l)) =1 (fun x => acc_mass x l)} => [m hm| transform_map].
        + rewrite acc_mass_cons. have : a.2 == m = false => [| a_ne_m]. apply/eqP. move => a_eq_m. rewrite -a_eq_m mem_undup in hm. rewrite hm //= in a_notin_l.
          rewrite a_ne_m addr0 //=. 
        rewrite eq_in_map in transform_map. rewrite {}transform_map IH //=. rewrite size_lt_cons //=.
Qed.

Lemma mass_cons_eq_acc_mass_add_mass {A : eqType} {μ : EnumQ A} (a : A) : mass μ (undup (unzip2 μ)) = acc_mass a μ + mass ([seq i <- μ | snd i != a]) (undup (unzip2 [seq i <- μ | snd i != a])).
Proof.
  rewrite /acc_mass /mass (sumq_filter (undup (unzip2  μ)) (fun (i : A) => i == a)).
  congr GRing.add.
  - rewrite /acc_mass /unzip1 /supp /unzip2 filter_undup. elim: μ => [//=|a0 μ IHμ].
    rewrite map_cons filter_cons filter_cons. remember (a0.2 == a) as snd_a. destruct snd_a.
    + rewrite sumq_cons -{}IHμ. remember [seq i.2  | i <- μ] as μ2. replace (undup (a0.2 :: [seq i <- μ2  | i == a])) with [:: a].
      + rewrite map_cons sumq_cons sumq_nil addr0 filter_cons -Heqsnd_a sumq_cons undup_filter_item. congr GRing.add.
        remember (a \in μ2) as H. destruct H. rewrite map_cons sumq_cons sumq_nil addr0 //=. rewrite sumq_nil.
        enough (H : [seq i <- μ  | i.2 == a] = [seq i <- μ  | false]). rewrite H filter_pred0 sumq_nil //=. apply eq_in_filter.
        move=> [px x] i //=. rewrite Heqμ2 in HeqH.
        have: true = (x \in [seq i.2 | i <- μ]). rewrite (map_f snd i) //.
        move=> Hxin. apply/negP. move=>/eqP Hxa. rewrite Hxa in Hxin. rewrite -HeqH //= in Hxin.
      + rewrite undup_cons. remember (a0.2  \in [seq i <- μ2  | i == a]) as H. destruct H.
        - rewrite undup_filter_item. enough (a \in μ2). rewrite H //=.
          rewrite Heqμ2. rewrite Heqμ2 in HeqH. rewrite filter_map /preim //= in HeqH. symmetry in Heqsnd_a. rewrite (eqP Heqsnd_a) in HeqH. symmetry in HeqH.
          clear - HeqH. exact: (mem_subseq (map_subseq snd (filter_subseq (SimplPred (fun x => x.2 == a)) μ)) HeqH).
        - enough (H2: [seq i <- μ2  | i == a] = [seq i <- μ2 | false]). rewrite H2 filter_pred0. enough (H3 : a = a0.2). rewrite H3 //=.
          clear - Heqsnd_a. symmetry in Heqsnd_a. rewrite (eqP Heqsnd_a) //=.
        - apply eq_in_filter. intros x i. symmetry in Heqsnd_a. rewrite (eqP Heqsnd_a) in HeqH. apply/negP. move => x_eq_a.
          rewrite -(eqP x_eq_a) in HeqH. clear - i HeqH. enough (H : x  \in [seq i <- μ2  | i == x]). rewrite H //= in HeqH. clear HeqH.
          rewrite mem_filter eq_refl i //=.
    + rewrite undup_filter_item. remember (a \in [seq i.2  | i <- μ]) as a_in_μ. destruct a_in_μ.
      - rewrite sumq_cons sumq_nil addr0 filter_cons -Heqsnd_a //=.
      - rewrite /map sumq_nil. symmetry. enough (H : [seq i.1  | i <- μ  & i.2 == a] = [::]). rewrite /map in H. rewrite H sumq_nil //=.
        enough (H : [seq i <- μ | i.2 == a] = [::]). rewrite H /map //=. clear IHμ. induction μ. auto.
        rewrite filter_cons. rewrite map_cons in_cons in Heqa_in_μ. symmetry in Heqa_in_μ. rewrite Bool.orb_false_iff in Heqa_in_μ.
        destruct Heqa_in_μ. symmetry in H0. rewrite (IHμ H0) eq_sym H //=.
  - rewrite /supp /unzip2. congr sumq.
    have prem_f: (fun i : nnQ * A => (snd i) != a) = preim snd (fun i : A => i != a). rewrite //=.
    rewrite prem_f -filter_map filter_undup -eq_in_map. move => b hb. rewrite -prem_f. rewrite mem_undup mem_filter in hb.
    rewrite /acc_mass. congr sumq. congr unzip1. rewrite -filter_predI. apply eq_in_filter. intros c hc. rewrite /predI //=.
    remember (c.2 == b) as cb. destruct cb. rewrite -Heqcb //=. move: (andP hb) => [b_ne_a _].
    symmetry in Heqcb. symmetry. apply/negP. move=> c_eq_a. rewrite (eqP Heqcb) in c_eq_a. rewrite c_eq_a //= in b_ne_a.
    rewrite -Heqcb //=.
Qed.

Lemma sum_cons_eq_acc_mass_add_mass {A : eqType} {μ : EnumQ A} (a : A) : sumq (unzip1 μ) = acc_mass a μ + sumq (unzip1 ([seq i <- μ | snd i != a])).
Proof.
  elim: μ => [//|h l IH].
  - simpl. rewrite acc_mass_nil addr0 //=.
  - rewrite acc_mass_cons filter_cons /unzip1 map_cons sumq_cons.
    case: (h.2 == a).
    - rewrite //= IH addrA (addrC (acc_mass a l) h.1) //=.
    - rewrite //= addr0 addrA IH addrA (addrC (acc_mass a l) h.1) //=.
Qed.

Lemma mass_supp_eq_sumq_fst {A : eqType} (μ : EnumQ A) : mass μ (supp μ) = sumq (unzip1 μ).
Proof.
  rewrite mass_supp_eq_mass_undup.
  move: μ. apply seq_strong_induction.
  move => [|a l] iH. cbn. reflexivity.
  rewrite (mass_cons_eq_acc_mass_add_mass (snd a)) (sum_cons_eq_acc_mass_add_mass (snd a)).
  congr GRing.add.
  replace [seq i <- a :: l  | i.2 != a.2] with [seq i <- l  | i.2 != a.2].
  eapply (iH [seq i <- l  | i.2 != a.2]).
  rewrite size_filter.
  have le_count := count_size (λ i : ℚ≥0 * A, i.2 != a.2) l. auto.
  unfold filter. rewrite (eq_refl (snd a)). auto.
Qed.

Lemma le_acc_mass_mass_supp {A : eqType} {x : A} {μ : EnumQ A} : acc_mass x μ <= mass μ (supp μ).
Proof.
  have uniq : uniq (supp μ) := supp_uniq μ.
  induction μ as [| a l ih']. cbn. auto.
  have ih := ih' (supp_uniq l).
  rewrite mass_supp_eq_sumq_fst /acc_mass /unzip1 filter_cons.
  remember (snd a == x) as snd_a_x. destruct snd_a_x.
  - rewrite map_cons map_cons sumq_cons sumq_cons. apply le_nnQ_of_le_Q, ssrnum.Num.Theory.lerD. auto.
    rewrite mass_supp_eq_sumq_fst in ih'. apply ih', supp_uniq.
  - rewrite map_cons sumq_cons (le_trans ih) //=.
    rewrite mass_supp_eq_sumq_fst /unzip1. apply le_nnQ_of_le_Q.
    rewrite ssrnum.Num.Theory.lerDr. exact (le_nnQ0 a.1).
Qed.

End Supp.



Section successor.
Context {X : eqType}.

Definition EnumQSucc {Y} (μ : EnumQ X) (k : X → Y) : EnumQ Y :=
  map (λ '(p, x), (p, k x)) μ.

(* Definition EnumQSubSucc {μ : EnumQ X} (k : X → Y) *)

End successor.



#[global] Program Instance EnumQ_DiscreteInterface
    : DiscreteInterface EnumQ :=
  {|disc_rep := EnumQ_Discrete
  ; disc_eq := @EqEnumQ
  ; disc_RT := @enumQRT
  ; disc_mass := @acc_mass
  ; disc_supp := @supp
  |}.
Next Obligation.
  split. intros. unfold enumQRT. intros x ? <-.
  rewrite H. reflexivity.
  intros. intro a. apply H. reflexivity.
Qed.
Next Obligation.
  intros m1 m2 Hm.
  unfold enumQRT in Hm.
  apply Hm. reflexivity.
Qed.

End EnumQ.
