Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype
  tuple bigop ssralg ssrnum order rat.
From PTree.Prob Require Import RatSubTypes DiscreteMC EnumMap MeasureIterationEnum
  TwoLevelMeasure TwoLevelMeasureEnum TwoLevelMeasureSubEnum FiniteEnumTransport
  FrontierLiftEnum IndexedCoupling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum EnumMap GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** Positions, not values, form the finite carrier.  In particular this
    representation needs neither an inhabitant nor decidable equality on A,
    and retains duplicate entries and zero weights. *)
Definition enum_position {A} (mu : Enum A) := 'I_(size mu).
Definition enum_position_entry {A} (mu : Enum A) (i : enum_position mu) :=
  tnth (in_tuple mu) i.
Arguments enum_position_entry {A} mu i.
Definition enum_position_weight {A} (mu : Enum A) i := (enum_position_entry mu i).1.
Definition enum_position_value {A} (mu : Enum A) i := (enum_position_entry mu i).2.
Arguments enum_position_weight {A} mu i.
Arguments enum_position_value {A} mu i.
Definition enum_positions {A} (mu : Enum A) : Enum (enum_position mu) :=
  finite_weighted_enum (enum_position_weight mu) id.

Lemma enum_positions_decode {A} (mu : Enum A) :
  emap (enum_position_value mu) (enum_positions mu) = mu.
Proof.
  rewrite /enum_positions finite_weighted_enum_map /finite_weighted_enum.
  transitivity (map (tnth (in_tuple mu)) (enum 'I_(size mu))).
  - apply eq_map=> i. unfold enum_position_weight, enum_position_value, enum_position_entry.
    by case: (tnth (in_tuple mu) i).
  - exact: map_tnth_enum.
Qed.

Lemma enum_positions_subprob {A} (mu : SubEnum A) :
  enum_subprob (enum_positions (subenum_raw mu)).
Proof.
  unfold enum_subprob, enum_mass.
  rewrite -(enum_expect_one_emap (enum_position_value (subenum_raw mu)))
    enum_positions_decode. exact (subenum_bound mu).
Qed.

Definition subenum_positions {A} (mu : SubEnum A) : SubEnum (enum_position (subenum_raw mu)) :=
  {| subenum_raw := enum_positions (subenum_raw mu);
     subenum_bound := enum_positions_subprob mu |}.

Lemma enum_lift_decode {A B} (mu : Enum A) (decode : A -> B) :
  @sem_lift Enum Enum_SemanticMeasure A B (fun x y => decode x = y) mu (emap decode mu).
Proof.
  change (IndexedCoupling.indexed_coupling (fun x y => decode x = y)
    (enum_prune mu) (enum_prune (emap decode mu))).
  rewrite enum_prune_emap.
  rewrite -{1}(emap_id (enum_prune mu)).
  apply IndexedCoupling.indexed_coupling_emap with (S := eq).
  - intros x y ->. reflexivity.
  - apply IndexedCoupling.indexed_coupling_refl. intro x. reflexivity.
Qed.

Lemma subenum_positions_decode {A} (mu : SubEnum A) :
  sem_lift (fun i x => enum_position_value (subenum_raw mu) i = x)
    (subenum_positions mu) mu.
Proof.
  change (@sem_lift Enum Enum_SemanticMeasure _ _
    (fun i x => enum_position_value (subenum_raw mu) i = x)
    (enum_positions (subenum_raw mu)) (subenum_raw mu)).
  have H := enum_lift_decode (enum_positions (subenum_raw mu))
    (enum_position_value (subenum_raw mu)).
  rewrite enum_positions_decode in H. exact H.
Qed.

Lemma weighted_seq_expect {I A} (weights : I -> nnQ) (decode : I -> A) indices f :
  enum_expect f [seq (weights i, decode i) | i <- indices] =
  \sum_(i <- indices) Qval (weights i) * f (decode i).
Proof. by elim: indices=> [|i indices IH]; rewrite ?big_nil ?big_cons /= ?IH. Qed.

Lemma finite_weighted_enum_expect {I : finType} {A}
    (weights : I -> nnQ) (decode : I -> A) f :
  enum_expect f (finite_weighted_enum weights decode) =
  \sum_i Qval (weights i) * f (decode i).
Proof. by rewrite /finite_weighted_enum weighted_seq_expect big_enum. Qed.

(** The atom-sum form needed by finite transportation is independent of
    the list representation, including repeated atoms. *)
Lemma finite_enum_expect {X : finType} (mu : Enum X) f :
  enum_expect f mu = \sum_x Qval (acc_mass x mu) * f x.
Proof.
  elim: mu=> [|[p a] mu IH].
  - rewrite /= big1 // => x _. exact: mul0r.
  - rewrite /= IH. transitivity
      (\sum_x ((if a == x then Qval p else 0) * f x + Qval (acc_mass x mu) * f x)).
    + rewrite big_split. apply congr1 with (f := fun z => z + \sum_x Qval (acc_mass x mu) * f x).
      transitivity (\sum_x (if a == x then Qval p * f x else 0)).
      * by rewrite -big_mkcond (big_pred1 a).
      * apply eq_bigr=> x _. by case: (a == x); rewrite ?mul0r.
    + apply eq_bigr=> x _. rewrite acc_mass_cons. cbn [fst snd].
      case: (a == x).
      * change (Qval p * f x + Qval (acc_mass x mu) * f x =
          (Qval (acc_mass x mu) + Qval p) * f x).
        by rewrite mulrDl addrC.
      * change (0 * f x + Qval (acc_mass x mu) * f x =
          (Qval (acc_mass x mu) + 0) * f x).
        by rewrite mul0r add0r addr0.
Qed.
