(** Rational finite nonnegative weightings. Ordinary rat coefficients carry
    no scalar certificate: nonnegativity belongs to the shared container.
    Algebraic data equalities compare raw lists, not proof fields. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List Morphisms Setoid.
From Coq.Arith Require Import Wf_nat.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq ssrnat
  fintype bigop ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import
  FiniteEnum FiniteListAlgebra FiniteAtoms FiniteSupport FinitePruning.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module EnumQ.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Definition EnumQ (A : Type) := FiniteEnum rat_rat__canonical__Num_NumDomain A.
Definition enumQ_raw {A} (mu : EnumQ A) := finite_enum_raw mu.
Lemma enumQ_nonnegative {A} (mu : EnumQ A) : finite_nonnegative (enumQ_raw mu).
Proof. exact: finite_enum_nonnegative. Qed.
Arguments enumQ_nonnegative {A} mu p x _.

Lemma enumQ_size_induction {A} (P : EnumQ A -> Prop) :
  (forall mu, (forall nu, (size (enumQ_raw nu) < size (enumQ_raw mu))%coq_nat -> P nu) -> P mu) ->
  forall mu, P mu.
Proof.
  exact (well_founded_induction (well_founded_ltof _ (fun mu => size (enumQ_raw mu))) P).
Qed.

Definition enumQ_of_list {A} (mu : list (rat*A)) (Hnn : finite_nonnegative mu) : EnumQ A :=
  finite_enum_of_list Hnn.
Definition enumQ_zero {A} : EnumQ A := finite_enum_zero _.
Definition ret_EnumQ {A} (x : A) : EnumQ A := finite_enum_ret _ x.
Definition bind_EnumQ {A B} (mu : EnumQ A) (k : A -> EnumQ B) : EnumQ B :=
  finite_enum_bind mu k.
Definition scale_EnumQ {A} p (Hp : 0 <= p) (mu : EnumQ A) : EnumQ A :=
  finite_enum_scale Hp mu.
Definition enumQ_map {A B} (f : A -> B) (mu : EnumQ A) : EnumQ B :=
  finite_enum_map f mu.

Definition enumQ_cons {A} (p : rat) (Hp : 0 <= p) (x : A) (mu : EnumQ A) : EnumQ A.
Proof.
  refine (enumQ_of_list (mu := (p,x)::enumQ_raw mu) _).
  move=> q y [He|Hin]; first by inversion He; subst.
  exact (enumQ_nonnegative mu q y Hin).
Defined.
Definition enumQ_app {A} (mu nu : EnumQ A) : EnumQ A.
Proof.
  refine (enumQ_of_list (mu := enumQ_raw mu ++ enumQ_raw nu) _).
  move=> p x /List.in_app_iff [H|H].
  - exact (enumQ_nonnegative mu p x H).
  - exact (enumQ_nonnegative nu p x H).
Defined.
Definition enumQ_filter {A} (P : rat*A -> bool) (mu : EnumQ A) : EnumQ A.
Proof.
  refine (enumQ_of_list (mu := List.filter P (enumQ_raw mu)) _).
  move=> p x /List.filter_In [H _]; exact (enumQ_nonnegative mu p x H).
Defined.

Definition enumQ_expect {A} (f : A -> rat) (mu : EnumQ A) :=
  finite_enum_expect mu f.
Definition sumq (ps : list rat) : rat := foldr (fun p q => p+q) 0 ps.
Definition acc_mass {A : eqType} (x : A) (mu : EnumQ A) : rat :=
  finite_atom x (enumQ_raw mu).
Definition mass {A : eqType} (mu : EnumQ A) (xs : list A) : rat :=
  sumq (List.map (fun x => acc_mass x mu) xs).
Definition EqEnumQ {A : eqType} (mu nu : EnumQ A) : Prop :=
  forall x, acc_mass x mu = acc_mass x nu.
Infix "==EnumQ" := EqEnumQ (at level 70).

Lemma enumQ_eq_eq {A : eqType} {mu nu : EnumQ A} :
  enumQ_raw mu = enumQ_raw nu -> mu ==EnumQ nu.
Proof. move=> H x; by rewrite /acc_mass H. Qed.
Lemma enumQ_eq_refl {A : eqType} (mu : EnumQ A) : mu ==EnumQ mu.
Proof. by []. Qed.
Lemma enumQ_eq_sym {A : eqType} (mu nu : EnumQ A) :
  mu ==EnumQ nu -> nu ==EnumQ mu.
Proof. move=> H x; symmetry; exact (H x). Qed.
Lemma enumQ_eq_trans {A : eqType} (mu nu rho : EnumQ A) :
  mu ==EnumQ nu -> nu ==EnumQ rho -> mu ==EnumQ rho.
Proof. move=> H K x; by rewrite H K. Qed.
#[global] Instance enumQ_eq_equiv {A : eqType} : Equivalence (@EqEnumQ A).
Proof.
  split.
  - exact: enumQ_eq_refl.
  - exact: enumQ_eq_sym.
  - exact: enumQ_eq_trans.
Qed.

Lemma sumq_nil : sumq [::] = 0.
Proof. reflexivity. Qed.
Lemma sumq_cons p ps : sumq (p::ps) = p + sumq ps.
Proof. reflexivity. Qed.
Lemma sumq_app ps qs : sumq (ps++qs) = sumq ps + sumq qs.
Proof. by elim: ps=> [|p ps IH] /=; rewrite ?add0r ?IH ?addrA. Qed.
Lemma acc_mass_nil {A : eqType} (x : A) : acc_mass x (@enumQ_zero A) = 0.
Proof. reflexivity. Qed.
Lemma acc_nil {A : eqType} (x : A) : acc_mass x (@enumQ_zero A) = 0.
Proof. reflexivity. Qed.
Lemma acc_app {A : eqType} x (mu nu : EnumQ A) :
  acc_mass x (enumQ_app mu nu) = acc_mass x mu + acc_mass x nu.
Proof. exact: finite_atom_app. Qed.
Lemma acc_mass_cons {A : eqType} x p (Hp : 0 <= p) y (mu : EnumQ A) :
  acc_mass x (enumQ_cons Hp y mu) = acc_mass x mu + if y == x then p else 0.
Proof. by rewrite /acc_mass /= finite_atom_cons addrC. Qed.
Lemma acc_mass_nonnegative {A : eqType} x (mu : EnumQ A) : 0 <= acc_mass x mu.
Proof. exact (finite_atom_nonnegative x (enumQ_nonnegative mu)). Qed.

Lemma enumQ_expect_ret {A} (f : A -> rat) x : enumQ_expect f (ret_EnumQ x) = f x.
Proof. exact: finite_enum_expect_ret. Qed.
Lemma enumQ_expect_nil {A} (f : A -> rat) : enumQ_expect f (@enumQ_zero A) = 0.
Proof. reflexivity. Qed.
Lemma enumQ_expect_cons {A} (f : A -> rat) p (Hp : 0 <= p) x mu :
  enumQ_expect f (enumQ_cons Hp x mu) = p*f x + enumQ_expect f mu.
Proof. reflexivity. Qed.
Lemma enumQ_expect_app {A} (f : A -> rat) (mu nu : EnumQ A) :
  enumQ_expect f (enumQ_app mu nu) = enumQ_expect f mu + enumQ_expect f nu.
Proof. exact: finite_expect_app. Qed.
Lemma enumQ_expect_scale {A} (f : A -> rat) p (Hp : 0 <= p) mu :
  enumQ_expect f (scale_EnumQ Hp mu) = p * enumQ_expect f mu.
Proof. exact: finite_enum_expect_scale. Qed.
Lemma enumQ_expect_bind {A B} (f : B -> rat) (mu : EnumQ A) k :
  enumQ_expect f (bind_EnumQ mu k) = enumQ_expect (fun x => enumQ_expect f (k x)) mu.
Proof. exact: finite_enum_expect_bind. Qed.
Lemma enumQ_expect_map {A B} (f : B -> rat) (h : A -> B) mu :
  enumQ_expect f (enumQ_map h mu) = enumQ_expect (fun x => f (h x)) mu.
Proof. exact: finite_enum_expect_map. Qed.

Lemma enumQ_nil_bind {A B} (k : A -> EnumQ B) :
  enumQ_raw (bind_EnumQ enumQ_zero k) = enumQ_raw enumQ_zero.
Proof. reflexivity. Qed.
Lemma enumQ_cons_bind {A B} p (Hp : 0 <= p) x mu (k : A -> EnumQ B) :
  enumQ_raw (bind_EnumQ (enumQ_cons Hp x mu) k) =
  enumQ_raw (enumQ_app (scale_EnumQ Hp (k x)) (bind_EnumQ mu k)).
Proof. reflexivity. Qed.
Lemma scale_app {A} p (Hp : 0 <= p) (mu nu : EnumQ A) :
  enumQ_raw (scale_EnumQ Hp (enumQ_app mu nu)) =
  enumQ_raw (enumQ_app (scale_EnumQ Hp mu) (scale_EnumQ Hp nu)).
Proof. exact: List.map_app. Qed.
Lemma scale_scale {A} p q (Hp : 0 <= p) (Hq : 0 <= q) (mu : EnumQ A) :
  enumQ_raw (scale_EnumQ Hp (scale_EnumQ Hq mu)) =
  enumQ_raw (scale_EnumQ (mulr_ge0 Hp Hq) mu).
Proof.
  change (finite_weight_map p (finite_weight_map q (enumQ_raw mu)) =
    finite_weight_map (p*q) (enumQ_raw mu)).
  rewrite -!finite_scale_with_weight_map.
  apply finite_scale_with_comp=> a b c; exact: mulrA.
Qed.
Lemma scale_bind {A B} p (Hp : 0 <= p) (mu : EnumQ A) (k : A -> EnumQ B) :
  enumQ_raw (scale_EnumQ Hp (bind_EnumQ mu k)) =
  enumQ_raw (bind_EnumQ mu (fun x => scale_EnumQ Hp (k x))).
Proof.
  change (finite_weight_map p (finite_bind (enumQ_raw mu) (fun x => enumQ_raw (k x))) =
    finite_bind (enumQ_raw mu) (fun x => finite_weight_map p (enumQ_raw (k x)))).
  rewrite -!finite_bind_with_numeric -!finite_scale_with_weight_map.
  rewrite finite_scale_with_bind; [|exact: mulrA|exact: mulrC].
  apply finite_bind_with_ext=> x; exact: finite_scale_with_weight_map.
Qed.

Definition dirac {A} (x : A) : EnumQ A := ret_EnumQ x.
Definition one_div_two : rat := 1/2.
Definition one_div_three : rat := 1/3.
Definition unif2 {A} (x y : A) : EnumQ A.
Proof.
  refine (enumQ_of_list (mu := [:: (one_div_two,x); (one_div_two,y)]) _).
  move=> p z [H|[H|[]]]; inversion H; subst; by rewrite /one_div_two.
Defined.
Definition unif3 {A} (x y z : A) : EnumQ A.
Proof.
  refine (enumQ_of_list (mu := [:: (one_div_three,x); (one_div_three,y); (one_div_three,z)]) _).
  move=> p a [H|[H|[H|[]]]]; inversion H; subst; by rewrite /one_div_three.
Defined.

Lemma enumQ_expect_unif2 {A} (f : A -> rat) x y :
  enumQ_expect f (unif2 x y) = one_div_two * f x + (one_div_two * f y + 0).
Proof. reflexivity. Qed.

Definition supp {A : eqType} (mu : EnumQ A) : list A :=
  undup [seq px.2 | px <- enumQ_raw mu & px.1 != 0].
Lemma supp_uniq {A : eqType} (mu : EnumQ A) : uniq (supp mu).
Proof. exact: undup_uniq. Qed.
Lemma enumQ_atom_zero {A : eqType} (mu : EnumQ A) x :
  acc_mass x mu = 0 <-> forall p, List.In (p,x) (enumQ_raw mu) -> p = 0.
Proof. exact (finite_atom_zero_iff x (enumQ_nonnegative mu)). Qed.
Lemma enumQ_atom_positive {A : eqType} (mu : EnumQ A) x :
  0 < acc_mass x mu <-> exists p, List.In (p,x) (enumQ_raw mu) /\ p <> 0.
Proof. exact (finite_atom_positive_iff x (enumQ_nonnegative mu)). Qed.
Definition EnumQSucc {A B} (mu : EnumQ A) (f : A -> B) : EnumQ B := enumQ_map f mu.

(** Induction on data does not identify the certificates in two records.
    Clients explicitly discharge invariance under raw-list equality. *)
Lemma enumQ_ind_raw {A} (P : EnumQ A -> Prop) :
  P enumQ_zero ->
  (forall p (Hp : 0 <= p) x mu, P mu -> P (enumQ_cons Hp x mu)) ->
  (forall mu nu, enumQ_raw mu = enumQ_raw nu -> P mu -> P nu) ->
  forall mu, P mu.
Proof.
  move=> Hz Hstep Heq [raw Hnn]; elim: raw Hnn=> [|[p x] tl IH] Hnn.
  - apply (Heq enumQ_zero); [reflexivity|exact Hz].
  - have Hp := Hnn p x (or_introl (Logic.eq_refl _)).
    have Htl : finite_nonnegative tl.
    { move=> q y Hy; exact (Hnn q y (or_intror Hy)). }
    apply (Heq (enumQ_cons Hp x (enumQ_of_list Htl))).
    + reflexivity.
    + apply Hstep; exact (IH Htl).
Qed.

Lemma enumQ_raw_mem {A : eqType} p x (mu : EnumQ A) :
  (p,x) \in enumQ_raw mu <-> List.In (p,x) (enumQ_raw mu).
Proof.
  elim: (enumQ_raw mu)=> [|px tl IH]; first by split.
  rewrite in_cons; split.
  - move/orP=> [/eqP H|H]; first by left; symmetry.
    right; exact (proj1 IH H).
  - move=> [H|H]; apply/orP; first by left; apply/eqP; symmetry.
    right; exact (proj2 IH H).
Qed.

Lemma in_supp_iff_acc_mass_ne_0 {A : eqType} x (mu : EnumQ A) :
  x \in supp mu <-> acc_mass x mu != 0.
Proof.
  rewrite /supp mem_undup; split.
  - move/mapP=> [[p y] Hfilter /= Heq].
    move: Hfilter; rewrite mem_filter=> /andP [Hp Hmem].
    subst y; apply/eqP=> Hz.
    have Hzero := proj1 (enumQ_atom_zero mu x) Hz p
      (proj1 (enumQ_raw_mem p x mu) Hmem).
    by rewrite Hzero eqxx in Hp.
  - move=> Hnz; have Hpos : 0 < acc_mass x mu.
    { rewrite lt_neqAle eq_sym Hnz /=; exact: acc_mass_nonnegative. }
    have [p [Hin Hp]] := proj1 (enumQ_atom_positive mu x) Hpos.
    apply/mapP; exists (p,x); last reflexivity.
    rewrite mem_filter; apply/andP; split.
    + exact/eqP.
    + exact (proj2 (enumQ_raw_mem p x mu) Hin).
Qed.
End EnumQ.
