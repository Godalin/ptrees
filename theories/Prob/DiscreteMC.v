Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8.
Require Import Setoid.
Require Import Program.
Require Import Morphisms.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq ssrfun.
From mathcomp Require Import order ssralg ssrint rat.

From PTree.Prob Require Import RatSubTypes.

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





(** The [Enum] Representation *)
Module Enum.
Import NonnegQNotations.
Import GRing.Theory.
Import Order.Theory.

Definition Enum (A : Type) := seq (ℚ≥0 * A).

Declare Scope enum_scope.
Bind Scope enum_scope with Enum.
Delimit Scope enum_scope with enum.
#[local] Open Scope enum_scope.

Fixpoint scale_Enum {A} (r : ℚ≥0) (e : Enum A) : Enum A :=
  match e with
  | [::] => [::]
  | (s, x) :: e' => (r * s, x) :: scale_Enum r e'
  end.

Lemma scale_app : ∀ A r (u v : Enum A),
  scale_Enum r (u ++ v) = scale_Enum r u ++ scale_Enum r v.
Proof. move=> A r u v. move: r. elim: u => [//|[t a] us] IH r //=.
  congr cons. rewrite IH //.
Qed.

Lemma scale_scale : ∀ {A} r s (u : Enum A),
  scale_Enum r (scale_Enum s u) = scale_Enum (r * s) u.
Proof. move=> A r s u. elim: u => [//|[t a] us] IH //=.
rewrite {}IH. congr cons. congr pair. rewrite mulrA //.
Qed.

Definition ret_Enum {A} (x : A) : Enum A := [:: (1, x)].

Definition bind_Enum {A B} (xs : Enum A) (f : A → Enum B) : Enum B :=
  foldr (λ '(s, x) ys, scale_Enum s (f x) ++ ys) [::] xs.

#[global] Instance Enum_Discrete : Discrete Enum :=
  {|disc_ret := @ret_Enum
  ; disc_bind := @bind_Enum
  ; disc_flip := λ _, [:: (1, true); (1, false)]
  ; disc_score := λ r, [:: (r, tt)]
  |}.


Definition scale_bind : ∀ {A B} r (u : Enum A) (f : A → Enum B),
  scale_Enum r (bind_Enum u f) = bind_Enum u (λ x, scale_Enum r (f x)).
Proof. move=> A B r u f. elim: u => [//|[s a] us] IH //=.
rewrite !scale_app {}IH. congr app. rewrite !scale_scale.
congr scale_Enum. rewrite mulrC //.
Qed.



(** We need the decidable equality for the base type [A] of
    the enumeration. *)

Definition sumq (l : seq ℚ≥0) : ℚ≥0
  := foldr (λ x acc, x + acc) 0 l.

Lemma sumq_cons {x : ℚ≥0} {l : seq ℚ≥0} : sumq (x :: l) = x + sumq l.
Proof. unfold sumq, foldr. reflexivity. Qed.

Lemma sumq_app {l1 l2 : seq ℚ≥0} : sumq (l1 ++ l2) = sumq l1 + sumq l2.
Proof. rewrite /sumq. elim: l1 => [//=| x s iH //=]. rewrite add0r //=.
rewrite iH //= addrA. reflexivity. Qed.

Lemma sumq_nil : sumq [::] = 0.
Proof. cbn. reflexivity. Qed.

Definition acc_mass {A : eqType} (x : A) (μ : Enum A) : ℚ≥0
  := sumq (unzip1 [seq i <- μ | snd i == x]).

Definition mass {X : eqType} (μ : Enum X) (s : seq X) : ℚ≥0
  := sumq [seq acc_mass x μ | x <- s].

Lemma acc_mass_nil {A : eqType} {x : A} : acc_mass x ([::] : Enum A) = 0.
Proof. cbn. reflexivity. Qed.

Lemma mass_nil {A : eqType} (μ : Enum A) : mass μ [::] = 0.
Proof. cbn. reflexivity. Qed.

Definition enumk {Y} {X : eqType} (μ : Enum X) (k : X → Y) (x : X) : ℚ≥0 * Y
  := (acc_mass x μ, k x).

Lemma acc_nil : ∀ (A : eqType) (x : A), acc_mass x [::] = 0.
Proof. move=> //=. Qed.

Lemma acc_app {A : eqType} {x : A} {μ1 μ2 : Enum A}
  : acc_mass x (μ1 ++ μ2) = acc_mass x μ1 + acc_mass x μ2.
Proof. rewrite /acc_mass filter_cat /unzip1 map_cat sumq_app //=. Qed.

Definition EqEnum {A : eqType} (μ1 μ2 : Enum A) : Prop :=
  ∀ x : A, acc_mass x μ1 = acc_mass x μ2.

Infix "==Enum" := EqEnum (at level 70).

Lemma enum_eq_eq {A : eqType} : ∀ {μ1 μ2 : Enum A},
  μ1 = μ2 → EqEnum μ1 μ2.
Proof. intros. unfold EqEnum. intros.
  rewrite H. reflexivity.
Qed.

Lemma enum_eq_refl : ∀ {A : eqType} {μ : Enum A},
  μ ==Enum μ.
Proof. intros. unfold EqEnum. intros. reflexivity. Qed.

Lemma enum_eq_sym {A : eqType} : ∀ {μ ν : Enum A},
  μ ==Enum ν → ν ==Enum μ.
Proof. intros. unfold EqEnum. intros. symmetry. apply H. Qed.

Lemma enum_eq_trans {A : eqType} : ∀ {x y z : Enum A},
  x ==Enum y → y ==Enum z → x ==Enum z.
Proof. intros. unfold EqEnum. intros. etransitivity; eauto. Qed.



#[global] Instance enum_eq_equiv {A : eqType}
  : @Equivalence (Enum A) EqEnum.
Proof. split. unfold Reflexive. intros. apply enum_eq_refl.
  unfold Symmetric. intros. now apply enum_eq_sym.
  unfold Transitive. intros. now eapply enum_eq_trans.
Qed.

Add Parametric Morphism {A : eqType} : (@app (ℚ≥0 * A))
  with signature EqEnum ==> EqEnum ==> EqEnum
  as app_proper.
Proof. intros. intros a. repeat rewrite acc_app.
  rewrite H. rewrite H0. reflexivity.
Qed.



Lemma app_comm {A : eqType} (u v : Enum A) : u ++ v ==Enum v ++ u.
Proof. unfold EqEnum. intros. induction u.
  simpl. now rewrite cats0. destruct a.
  repeat rewrite acc_app. rewrite addrC //.
Qed.

Lemma enum_nil_bind : ∀ A B (f : A → Enum B),
  bind_Enum [:: ] f = [:: ].
Proof. intros. simpl. reflexivity. Qed.

Lemma enum_cons_bind : ∀ A B x r (u : Enum A) (f : A → Enum B),
  bind_Enum ((r, x) :: u) f = scale_Enum r (f x) ++ bind_Enum u f.
Proof. intros. simpl. reflexivity. Qed.

Lemma enum_bind_nil : ∀ A B (u : Enum A),
  bind_Enum u (λ _, [::] : Enum B) = [::].
Proof.
  intros. simpl. induction u.
  now simpl. destruct a. rewrite enum_cons_bind.
  now simpl.
Qed.

Lemma enum_bind_app : ∀ A {B : eqType} (u : Enum A) (f g : A → Enum B),
  bind_Enum u (λ x, (f x) ++ (g x))
    ==Enum
  bind_Enum u (λ x, f x) ++ bind_Enum u (λ x, g x).
Proof. intros. induction u. now simpl.
  destruct a. repeat rewrite enum_cons_bind.
  rewrite scale_app. rewrite IHu. repeat rewrite <- catA.
  rewrite (catA (bind_Enum u (λ x : A, f x))).
  rewrite (app_comm (bind_Enum u (λ x : A, f x)) (scale_Enum n (g a))).
  repeat rewrite <- catA. reflexivity.
Qed.

Lemma enum_comm_nil : ∀ A B C (v : Enum B) (f : A → B → Enum C),
  bind_Enum [::] (λ x, bind_Enum v (λ y, f x y)) =
  bind_Enum v (λ y, bind_Enum [::] (λ x, f x y)).
Proof.
  intros A B C v f.
  rewrite enum_bind_nil. simpl. reflexivity.
Qed.

Lemma enum_comm_cons : ∀
  {A : eqType} {B : eqType} {C : eqType} r a
  (u : Enum A) (v : Enum B) (f : A → B → Enum C),
    bind_Enum ((r, a) :: u) (λ x, bind_Enum v (λ y, f x y))
      ==Enum
    bind_Enum v (λ y, bind_Enum ((r, a) :: u) (λ x, f x y)).
Proof.
  intros. rewrite enum_cons_bind. simpl.
  induction v.
  - simpl. rewrite enum_bind_nil. now apply enum_eq_eq.
  - destruct a0. simpl. repeat rewrite scale_app.
    repeat rewrite enum_bind_app.
    repeat rewrite <- catA.
    rewrite (catA (scale_Enum r (bind_Enum v (λ y : B, f a y)))).
    rewrite (app_comm (scale_Enum r (bind_Enum v (λ y : B, f a y)))).
    rewrite <- catA.
    rewrite IHv. repeat rewrite scale_scale.
    rewrite scale_bind. rewrite enum_bind_app.
    apply enum_eq_eq. congr app. congr scale_Enum.
    rewrite mulrC //.
Qed.

Theorem enum_Fubini_Tonelli : ∀
  {A : eqType} {B : eqType} {C : eqType}
  (u : Enum A) (v : Enum B) (f : A → B → Enum C),
    bind_Enum u (λ x, bind_Enum v (λ y, f x y))
      ==Enum
    bind_Enum v (λ y, bind_Enum u (λ x, f x y)).
Proof. destruct u.
  - intros. apply enum_eq_eq. apply enum_comm_nil.
  - intros. destruct p. now eapply enum_comm_cons.
Qed.

(** * the relation transformer for [Enum] *)

Definition enumRT {R1 : eqType} {R2 : eqType}
    (RR : R1 → R2 → Prop) : Enum R1 → Enum R2 → Prop
  := λ μx μy, ∀ x y, RR x y → acc_mass x μx = acc_mass y μy.

Infix "==EnumRT" := (enumRT _) (at level 70).

#[global] Program Instance Enum_DiscreteInterface
    : DiscreteInterface Enum :=
  {|disc_rep := Enum_Discrete
  ; disc_eq := @EqEnum
  ; disc_RT := @enumRT
  ; disc_mass := @acc_mass
  |}.
Next Obligation.
  split. intros. unfold enumRT. intros x ? <-.
  rewrite H. reflexivity.
  intros. intro a. apply H. reflexivity.
Qed.
Next Obligation.
  intros m1 m2 Hm.
  unfold enumRT in Hm.
  apply Hm. reflexivity.
Qed.



(** Convenient Distribution Constructors *)
Section Dists.

Definition dirac {A} (x : A) : Enum A :=
  ret_Enum x.

#[program] Definition one_div_two := [nn 1/2].
#[program] Definition one_div_three := [nn 1/3].

Definition unif2 {A} (x y : A) : Enum A :=
  [:: (one_div_two, x); (one_div_two, y)].

Definition unif3 {A} (x y z : A) : Enum A :=
  [:: (one_div_three, x); (one_div_three, y); (one_div_three, z)].

End Dists.



Section int.

Definition integral {A : eqType} (f : A → ℚ≥0) (μ : Enum A)
  := foldr (λ '(p, x) s, (f x) * p + s) 0.

End int.



(* Properties about Support Set *)

Section Supp.

Lemma eta {A : eqType} (μ : Enum A)
  : μ = [seq (p, x) | '(p, x) <- μ].
Proof. elim: μ => [//|[p x] μ IH]. rewrite map_cons.
congr cons. exact: IH.
Qed.

Definition supp {A : eqType} (μ : Enum A)
  := undup (unzip2 μ).

Lemma supp_uniq {A : eqType} (μ : Enum A) : uniq (supp μ).
Proof. apply: undup_uniq. Qed.

Lemma supp_spec {A: eqType} (μ : Enum A)
  : (supp μ =i unzip2 μ).
Proof. apply: mem_undup. Qed.

Lemma supp_nil {A : eqType} : supp ([::] : Enum A) = [::].
Proof. cbn. reflexivity. Qed.

Lemma sumq_filter {A} {C : A -> nnQ} (l : seq A) (P : A -> bool) : sumq (map C l) = sumq [seq C i  | i <- l  & P i] + sumq [seq C i  | i <- l  & ~~ P i].
Proof.
  induction l. rewrite //= addr0 //=.
  rewrite map_cons /filter. destruct (P a).
  - rewrite //= IHl addrA //=.
  - rewrite //= IHl addrA addrA (addrC (C a) (sumq [seq C i  | i <- l  & P i])) //=.
Qed.

Lemma filter_cons {A} {l: seq A} {a : A} {P: A -> bool}: filter P (a :: l) = if P a then a :: filter P l else filter P l.
Proof. reflexivity. Qed.

Lemma undup_filter_item {A: eqType} {l: seq A} {a : A} : undup [seq i <- l | i == a] = if a \in l then [:: a] else [::].
Proof. Admitted.

Lemma acc_mass_cons {A : eqType} {μ : Enum A} {a : A} {h : nnQ * A} : acc_mass a (h :: μ) = acc_mass a μ + if h.2 == a then h.1 else 0.
Proof.
  rewrite /acc_mass /filter.
  have fold_filter : filter (fun x => snd x == a) = filter (fun x => snd x == a). reflexivity. unfold filter at 1 in fold_filter.
  rewrite fold_filter.
  remember (h.2 == a) as snd_h_a. destruct snd_h_a.
  - rewrite /unzip1 map_cons sumq_cons addrC //=.
  - rewrite addr0 //=.
Qed.

Lemma mass_cons_eq_acc_mass_add_mass {A : eqType} {μ : Enum A} (a : A) : mass μ (supp μ) = acc_mass a μ + mass ([seq i <- μ | snd i != a]) (supp [seq i <- μ | snd i != a]).
Proof.
  rewrite /acc_mass /mass (sumq_filter (supp μ) (fun (i : A) => i == a)).
  congr GRing.add.
  - rewrite /acc_mass /unzip1 /supp /unzip2 filter_undup. induction μ. cbn. reflexivity.
    rewrite map_cons filter_cons filter_cons. remember (a0.2 == a) as snd_a. destruct snd_a.
    + rewrite sumq_cons -{}IHμ. remember [seq i.2  | i <- μ] as μ2. replace (undup (a0.2 :: [seq i <- μ2  | i == a])) with [:: a].
      + rewrite map_cons sumq_cons sumq_nil addr0 filter_cons -Heqsnd_a sumq_cons undup_filter_item. congr GRing.add.
        remember (a \in μ2) as H. destruct H. rewrite map_cons sumq_cons sumq_nil addr0 //=. rewrite sumq_nil.
        enough (H : [seq i <- μ  | i.2 == a] = [seq i <- μ  | false]). rewrite H filter_pred0 sumq_nil //=. apply eq_in_filter.
        intros x i. rewrite Heqμ2 in HeqH. clear - Heqsnd_a HeqH. admit.
      + unfold undup. remember (a0.2  \in [seq i <- μ2  | i == a]) as H. destruct H.
        - have fold_undup : undup = undup. reflexivity. unfold undup at 1 in fold_undup. rewrite {}fold_undup undup_filter_item. enough (a \in μ2). rewrite H //=.
          rewrite Heqμ2. rewrite Heqμ2 in HeqH. rewrite filter_map /preim //= in HeqH. clear - HeqH Heqsnd_a. admit.
        - enough (H2: [seq i <- μ2  | i == a] = [seq i <- μ2 | false]). rewrite H2 filter_pred0. enough (H3 : a = a0.2). rewrite H3 //=.
          clear - Heqsnd_a. admit.
        - apply eq_in_filter. intros x i. admit.
    + rewrite undup_filter_item. remember (a \in [seq i.2  | i <- μ]) as a_in_μ. destruct a_in_μ.
      - rewrite sumq_cons sumq_nil addr0 filter_cons -Heqsnd_a //=.
      - rewrite /map sumq_nil. symmetry. enough (H : [seq i.1  | i <- μ  & i.2 == a] = [::]). rewrite /map in H. rewrite H sumq_nil //=.
        enough (H : [seq i <- μ | i.2 == a] = [::]). rewrite H /map //=. clear IHμ. induction μ. auto.
        rewrite filter_cons. rewrite map_cons in_cons in Heqa_in_μ. symmetry in Heqa_in_μ. rewrite Bool.orb_false_iff in Heqa_in_μ.
        destruct Heqa_in_μ. symmetry in H0. rewrite (IHμ H0) eq_sym H. reflexivity.
  - rewrite /supp /unzip2. congr sumq.
    have prem_f: (fun i : nnQ * A => (snd i) != a) = preim snd (fun i : A => i != a). rewrite //=.
    rewrite prem_f -filter_map filter_undup -eq_in_map. move => b hb. rewrite -prem_f. rewrite mem_undup mem_filter in hb.
    rewrite /acc_mass. congr sumq. congr unzip1. rewrite -filter_predI. apply eq_in_filter. intros c hc. rewrite /predI //=.
    remember (c.2 == b) as cb. destruct cb. rewrite -Heqcb //=.
    rewrite <- (Bool.reflect_iff _ _ (@andP (b != a) (b  \in [seq i.2  | i <- μ])) ) in hb. destruct hb.
    clear - Heqcb H. admit.
    rewrite -Heqcb //=.
Admitted.

Lemma sum_cons_eq_acc_mass_add_mass {A : eqType} {μ : Enum A} (a : A) : sumq (unzip1 μ) = acc_mass a μ + sumq (unzip1 ([seq i <- μ | snd i != a])).
Proof.
  elim: μ => [//|h l IH].
  - simpl. rewrite acc_mass_nil addr0 //=.
  - rewrite acc_mass_cons /filter /unzip1 map_cons sumq_cons.
    have fold_filter : filter (fun x => snd x != a) = filter (fun x => snd x != a). reflexivity. unfold filter at 1 in fold_filter.
    rewrite {}fold_filter.
    remember (h.2 == a) as snd_h_a. destruct snd_h_a.
    - rewrite //= IH addrA (addrC (acc_mass a l) h.1) //=.
    - rewrite //= addr0 addrA IH addrA (addrC (acc_mass a l) h.1) //=.
Qed.

Lemma seq_strong_induction {A: Type} {P : seq A -> Prop} (Pn : ∀ L, (∀ l, size l < size L -> P l) -> P L ): ∀ l, P l.
Proof.
  enough (H0: ∀ (n: nat) l, lt (size l) n -> P l).
  - move=> l. eapply (H0 (plus 1 (size l))). auto.
  - elim => [l fal| n IHn l sizel_lt_n_add_1].
    + cbn in fal. apply except. exact (PeanoNat.Nat.nle_succ_0 _ fal).
    + eapply (Pn l). move => l' size_l'_lt_l. eapply (IHn l').
      rewrite /Order.lt /Order.NatOrder.Datatypes_nat__canonical__Order_POrder //= /is_true -(Bool.reflect_iff _ _ ssrnat.ltP) in size_l'_lt_l.
      rewrite /lt -PeanoNat.Nat.succ_le_mono in sizel_lt_n_add_1. exact (PeanoNat.Nat.le_trans _ _ _ size_l'_lt_l sizel_lt_n_add_1).
Qed.

Lemma mass_supp_eq_sumq_fst {A : eqType} (μ : Enum A) : mass μ (supp μ) = sumq (unzip1 μ).
Proof.
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

Lemma acc_mass_0_of_notin_supp {A : eqType} (x : A) (μ : Enum A) : x \notin (supp μ) → acc_mass x μ = 0.
Proof.
  intros h.
  rewrite /acc_mass. rewrite /supp mem_undup /unzip2 in h.
  replace ([seq i <- μ  | snd i == x]) with ([::] : Enum A). auto.
  elim: μ h => [//= | h t ih x_notin].
  rewrite map_cons in_cons in x_notin.
  rewrite <- (Bool.reflect_iff _ _ (@norP (x == snd h) (x  \in [seq snd i  | i <- t])) ) in x_notin.
  move: x_notin => [x_ne_h x_notin].
  rewrite eq_sym /is_true Bool.negb_true_iff in x_ne_h.
  rewrite /filter x_ne_h.
  exact (ih x_notin).
Qed.

Lemma le_acc_mass_mass_supp {A : eqType} {x : A} {μ : Enum A} : acc_mass x μ <= mass μ (supp μ).
Proof.
  have uniq : uniq (supp μ) := supp_uniq μ.
  induction μ as [| a l ih']. cbn. auto.
  have ih := ih' (supp_uniq l).
  rewrite mass_supp_eq_sumq_fst /acc_mass /unzip1 /filter.
  remember (snd a == x) as snd_a_x. destruct snd_a_x.
  - have fold_filter : filter (fun a => snd a == x) = filter (fun a => snd a == x). reflexivity. unfold filter at 1 in fold_filter.
    rewrite map_cons map_cons sumq_cons sumq_cons {}fold_filter. apply le_nnQ_of_le_Q, ssrnum.Num.Theory.lerD. auto.
    rewrite mass_supp_eq_sumq_fst in ih'. apply ih', supp_uniq.
  - rewrite map_cons sumq_cons (le_trans ih) //=.
    rewrite mass_supp_eq_sumq_fst /unzip1. apply le_nnQ_of_le_Q.
    rewrite ssrnum.Num.Theory.lerDr. exact (le_nnQ0 a.1).
Qed.

End Supp.



Section successor.
Context {X : eqType}.

Definition EnumSucc {Y} (μ : Enum X) (k : X → Y) : Enum Y :=
  map (λ '(p, x), (p, k x)) μ.

(* Definition EnumSubSucc {μ : Enum X} (k : X → Y) *)

End successor.


End Enum.
