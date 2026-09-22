(** Finite real joint couplings. Composition is an explicit finite product
    divided by the shared atom mass; zero fibers contribute zero. This layer
    uses neither an external probability model nor a gluing axiom. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals boolp.
From PTree.Prob.Interface Require Import Measure AE Coupling.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Section FiniteCoupling.
Variable R : realType.

Lemma real_enum_expect_ae_ext {A} (mu : list (R * A)) f g :
  (forall p x, List.In (p,x) mu -> p <> 0 -> f x = g x) ->
  real_enum_expect f mu = real_enum_expect g mu.
Proof.
  induction mu as [|[p x] tl IH]; intros H; cbn [real_enum_expect]; first reflexivity.
  have He : real_enum_expect f tl = real_enum_expect g tl.
  { apply IH; intros q y Hy Hq; exact (H q y (or_intror Hy) Hq). }
  rewrite He; destruct (eqVneq p 0) as [->|Hp]; first by rewrite !mul0r.
  have Hnz : p <> 0 by move=> Hz; move/eqP: Hp; exact.
  by rewrite (H p x (or_introl (Logic.eq_refl _)) Hnz).
Qed.

Lemma real_enum_expect_entry_le {A} (mu : list (R * A)) f p x :
  real_enum_nonnegative mu -> (forall y, 0 <= f y) ->
  List.In (p,x) mu -> p * f x <= real_enum_expect f mu.
Proof.
  induction mu as [|[q y] tl IH]; intros Hnn Hf Hin; first contradiction.
  have Htl : real_enum_nonnegative tl := fun r z Hz => Hnn r z (or_intror Hz).
  cbn [real_enum_expect]; destruct Hin as [He|Hin].
  - inversion He; subst; rewrite lerDl; exact: real_enum_expect_nonnegative.
  - apply: le_trans (IH Htl Hf Hin) _.
    rewrite lerDr; apply mulr_ge0; [exact (Hnn q y (or_introl (Logic.eq_refl _)))|exact (Hf y)].
Qed.

Definition real_indicator (P : Prop) : R := if asbool P then 1 else 0.
Lemma real_indicator_ge0 P : 0 <= real_indicator P.
Proof. rewrite /real_indicator; case: (asbool P); [exact: ler01|exact: lexx]. Qed.
Lemma real_indicator_true P : P -> real_indicator P = 1.
Proof. intro H; rewrite /real_indicator; have -> : asbool P = true by apply/asboolP. reflexivity. Qed.
Lemma real_indicator_false P : ~ P -> real_indicator P = 0.
Proof. intro H; rewrite /real_indicator; have -> : asbool P = false by apply/asboolPn. reflexivity. Qed.

Lemma subenumR_ae_zero_test {A} (mu : SubEnumR R A) (P : A -> Prop) :
  subenumR_ae mu P <-> subenumR_expect mu (fun x => real_indicator (~ P x)) = 0.
Proof.
  split.
  - intro H; rewrite -(real_enum_expect_zero (subenumR_raw mu)).
    apply real_enum_expect_ae_ext; intros p x Hin Hnz.
    apply real_indicator_false; intro Hnot; exact (Hnot (H p x Hin Hnz)).
  - intros He p x Hin Hnz; case: (pselect (P x))=> [//|Hnot]; exfalso.
    have Hb := real_enum_expect_entry_le (@subenumR_nonnegative R A mu)
      (fun y => real_indicator_ge0 (~ P y)) Hin.
    rewrite (real_indicator_true Hnot) mulr1 in Hb.
    change (is_true (p <= subenumR_expect mu (fun y => real_indicator (~ P y)))) in Hb.
    rewrite He in Hb; apply Hnz; apply/eqP; rewrite eq_le.
    apply/andP; split; [exact Hb|exact (@subenumR_nonnegative R A mu p x Hin)].
Qed.

Lemma subenumR_ae_proper {A} (mu nu : SubEnumR R A) P :
  subenumR_eq mu nu -> subenumR_ae mu P -> subenumR_ae nu P.
Proof.
  intros He H; apply subenumR_ae_zero_test.
  rewrite -(He (fun x => real_indicator (~ P x))).
  apply subenumR_ae_zero_test; exact H.
Qed.

Definition subenumR_map {A B} (f : A -> B) (mu : SubEnumR R A) :=
  subenumR_bind mu (fun x => subenumR_ret R (f x)).
Lemma subenumR_expect_map {A B} (f : A -> B) (mu : SubEnumR R A) g :
  subenumR_expect (subenumR_map f mu) g = subenumR_expect mu (fun x => g (f x)).
Proof.
  rewrite subenumR_expect_bind; apply real_enum_expect_ext=> x.
  by rewrite /subenumR_expect /= mul1r addr0.
Qed.
Lemma subenumR_ae_map {A B} (f : A -> B) (mu : SubEnumR R A) P :
  subenumR_ae (subenumR_map f mu) P <-> subenumR_ae mu (fun x => P (f x)).
Proof.
  rewrite !subenumR_ae_zero_test subenumR_expect_map; reflexivity.
Qed.

Definition real_enum_product {A B C} (mu : list (R*A)) (nu : list (R*B))
    (w : A -> B -> R) (h : A -> B -> C) : list (R*C) :=
  List.flat_map (fun px => List.map (fun qy =>
    (fst px * (fst qy * w (snd px) (snd qy)), h (snd px) (snd qy))) nu) mu.

Lemma real_enum_expect_product {A B C} (mu : list (R*A)) (nu : list (R*B)) w h (f : C -> R) :
  real_enum_expect f (real_enum_product mu nu w h) =
  real_enum_expect (fun x => real_enum_expect (fun y => w x y * f (h x y)) nu) mu.
Proof.
  induction mu as [|[p x] tl IH]; first reflexivity.
  cbn [real_enum_product List.flat_map]; rewrite real_enum_expect_app IH.
  cbn [real_enum_expect fst snd]; congr (_ + _).
  clear IH tl; induction nu as [|[q y] rest IHn]; cbn; first by rewrite mulr0.
  by rewrite IHn mulrDr !mulrA.
Qed.

Lemma real_enum_expect_swap {A B} (mu : list (R*A)) (nu : list (R*B)) f :
  real_enum_expect (fun x => real_enum_expect (f x) nu) mu =
  real_enum_expect (fun y => real_enum_expect (fun x => f x y) mu) nu.
Proof.
  induction mu as [|[p x] tl IH]; cbn [real_enum_expect].
  - symmetry; apply real_enum_expect_zero.
  - rewrite real_enum_expect_add real_enum_expect_scale IH; reflexivity.
Qed.

Definition subenumR_atom {A} (mu : SubEnumR R A) (x : A) :=
  subenumR_expect mu (fun y => real_indicator (y = x)).
Lemma subenumR_atom_ge0 {A} (mu : SubEnumR R A) x : 0 <= subenumR_atom mu x.
Proof. apply real_enum_expect_nonnegative; [exact (@subenumR_nonnegative R A mu)|intro y; apply real_indicator_ge0]. Qed.

Lemma subenumR_project_atom_positive {A B} (mu : SubEnumR R A) (f : A -> B) p x :
  List.In (p,x) (subenumR_raw mu) -> p <> 0 ->
  0 < subenumR_expect mu (fun y => real_indicator (f y = f x)).
Proof.
  intros Hin Hnz.
  have Hentry := real_enum_expect_entry_le (@subenumR_nonnegative R A mu)
    (fun y => real_indicator_ge0 (f y = f x)) Hin.
  rewrite (real_indicator_true (Logic.eq_refl (f x))) mulr1 in Hentry.
  apply: lt_le_trans _ Hentry.
  rewrite lt_def; apply/andP; split.
  - apply/eqP; exact Hnz.
  - exact (@subenumR_nonnegative R A mu p x Hin).
Qed.

Lemma real_indicator_eq_sym {A} (x y : A) : real_indicator (x = y) = real_indicator (y = x).
Proof.
  case: (pselect (x = y))=> [->|H].
  - reflexivity.
  - rewrite !real_indicator_false; [reflexivity|intro He; apply H; symmetry; exact He|exact H].
Qed.

Section Gluing.
Context {A B C : Type}.
Variables (j : SubEnumR R (A*B)) (k : SubEnumR R (B*C)).
Hypothesis middle : forall f,
  subenumR_expect j (fun xy => f (snd xy)) = subenumR_expect k (fun yz => f (fst yz)).

Let atom (y : B) := subenumR_expect k (fun yz => real_indicator (y = fst yz)).
Let weight (xy : A*B) (yz : B*C) :=
  if asbool (snd xy = fst yz) then (atom (snd xy))^-1 else 0.
Let raw := real_enum_product (subenumR_raw j) (subenumR_raw k) weight (fun xy yz => (fst xy,snd yz)).

Lemma subenumR_glue_atom_left p xy :
  List.In (p,xy) (subenumR_raw j) -> p <> 0 -> 0 < atom (snd xy).
Proof.
  intros Hin Hnz.
  have H := subenumR_project_atom_positive snd Hin Hnz.
  have He : subenumR_expect j (fun xy' => real_indicator (snd xy' = snd xy)) = atom (snd xy).
  { rewrite (middle (fun y => real_indicator (y = snd xy))).
    apply real_enum_expect_ext=> yz; exact: real_indicator_eq_sym. }
  by rewrite -He.
Qed.
Lemma subenumR_glue_atom_right q yz :
  List.In (q,yz) (subenumR_raw k) -> q <> 0 -> 0 < atom (fst yz).
Proof.
  intros Hin Hnz; have H := subenumR_project_atom_positive fst Hin Hnz.
  have He : subenumR_expect k (fun yz' => real_indicator (fst yz' = fst yz)) = atom (fst yz).
  { apply real_enum_expect_ext=> yz'; exact: real_indicator_eq_sym. }
  by rewrite -He.
Qed.

Lemma subenumR_glue_row xy f :
  real_enum_expect (fun yz => weight xy yz * f (fst xy)) (subenumR_raw k) =
  ((atom (snd xy))^-1 * f (fst xy)) * atom (snd xy).
Proof.
  rewrite /atom /subenumR_expect -real_enum_expect_scale.
  apply real_enum_expect_ext=> yz; rewrite /weight /atom /real_indicator.
  case: (asbool (snd xy = fst yz)); by rewrite ?mulr1 ?mulr0 ?mul0r.
Qed.

Lemma subenumR_glue_column yz g :
  real_enum_expect (fun xy => weight xy yz * g (snd yz)) (subenumR_raw j) =
  ((atom (fst yz))^-1 * g (snd yz)) * atom (fst yz).
Proof.
  transitivity (subenumR_expect j (fun xy =>
    ((atom (fst yz))^-1 * g (snd yz)) * real_indicator (snd xy = fst yz))).
  - apply real_enum_expect_ext=> xy; rewrite /weight /real_indicator.
    case H: (asbool (snd xy = fst yz)).
    + have He : snd xy = fst yz by apply/asboolP.
      by rewrite He mulr1.
    + by rewrite mul0r mulr0.
  - rewrite /subenumR_expect real_enum_expect_scale.
    change (((atom (fst yz))^-1 * g (snd yz)) *
      subenumR_expect j (fun xy => real_indicator (snd xy = fst yz)) =
      ((atom (fst yz))^-1 * g (snd yz)) * atom (fst yz)).
    rewrite (middle (fun y => real_indicator (y = fst yz))).
    congr (_ * _); apply real_enum_expect_ext=> yz'.
    exact: real_indicator_eq_sym.
Qed.

Lemma subenumR_glue_raw_left f :
  real_enum_expect (fun xz => f (fst xz)) raw = subenumR_expect j (fun xy => f (fst xy)).
Proof.
  rewrite /raw real_enum_expect_product.
  apply real_enum_expect_ae_ext=> p xy Hin Hnz.
  cbn [fst snd].
  transitivity (((atom (snd xy))^-1 * f (fst xy)) * atom (snd xy)).
  - exact (subenumR_glue_row xy f).
  rewrite mulrAC mulVf ?mul1r //.
  apply/eqP=> Hz; have H := subenumR_glue_atom_left Hin Hnz; by rewrite Hz ltxx in H.
Qed.
Lemma subenumR_glue_raw_right g :
  real_enum_expect (fun xz => g (snd xz)) raw = subenumR_expect k (fun yz => g (snd yz)).
Proof.
  rewrite /raw real_enum_expect_product real_enum_expect_swap.
  apply real_enum_expect_ae_ext=> q yz Hin Hnz.
  cbn [fst snd].
  transitivity (((atom (fst yz))^-1 * g (snd yz)) * atom (fst yz)).
  - exact (subenumR_glue_column yz g).
  rewrite mulrAC mulVf ?mul1r //.
  apply/eqP=> Hz; have H := subenumR_glue_atom_right Hin Hnz; by rewrite Hz ltxx in H.
Qed.

Definition subenumR_glue : SubEnumR R (A*C).
Proof.
  refine (@Build_SubEnumR R (A*C) raw _ _).
  - intros r xz Hin; apply List.in_flat_map in Hin.
    destruct Hin as [[p xy] [Hp Hin]]; apply List.in_map_iff in Hin.
    destruct Hin as [[q yz] [He Hq]]; cbn in He; inversion He; subst.
    apply mulr_ge0; [exact (@subenumR_nonnegative R (A*B) j p xy Hp)|].
    apply mulr_ge0; [exact (@subenumR_nonnegative R (B*C) k q yz Hq)|].
    rewrite /weight; case: (asbool _); last exact: lexx.
    rewrite invr_ge0; apply real_enum_expect_nonnegative.
    + exact (@subenumR_nonnegative R (B*C) k).
    + intro z; apply real_indicator_ge0.
  - have He : real_enum_expect (fun _ : A*C => 1) raw = subenumR_expect j (fun _ => 1).
    { exact (subenumR_glue_raw_left (fun _ => 1)). }
    rewrite He; exact (@subenumR_mass_bound R (A*B) j).
Defined.

Lemma subenumR_glue_support (S : A -> B -> Prop) (T : B -> C -> Prop) :
  subenumR_ae j (fun xy => S (fst xy) (snd xy)) ->
  subenumR_ae k (fun yz => T (fst yz) (snd yz)) ->
  subenumR_ae subenumR_glue (fun xz => exists y, S (fst xz) y /\ T y (snd xz)).
Proof.
  intros Hj Hk r xz Hin Hnz; apply List.in_flat_map in Hin.
  destruct Hin as [[p [x y]] [Hp Hin]]; apply List.in_map_iff in Hin.
  destruct Hin as [[q [y' z]] [He Hq]]; cbn in He; inversion He; subst; clear He.
  have Hpn : p <> 0 by intro H; apply Hnz; rewrite H mul0r.
  have Hqn : q <> 0 by intro H; apply Hnz; rewrite H mul0r mulr0.
  have Hyy : y = y'.
  { case H: (asbool (y = y')); first by apply/asboolP.
    exfalso; apply Hnz; rewrite /weight /= H !mulr0; reflexivity. }
  subst y'; exists y; split; [exact (Hj p (x,y) Hp Hpn)|exact (Hk q (y,z) Hq Hqn)].
Qed.
End Gluing.

Theorem subenumR_lift_comp {A B C} (S : A -> B -> Prop) (T : B -> C -> Prop)
    (mu : SubEnumR R A) (nu : SubEnumR R B) (xi : SubEnumR R C) :
  subenumR_lift S mu nu -> subenumR_lift T nu xi ->
  subenumR_lift (fun x z => exists y, S x y /\ T y z) mu xi.
Proof.
  intros [j [Hjl [Hjr Hj]]] [k [Hkl [Hkr Hk]]].
  have Hmid : forall f, subenumR_expect j (fun xy => f (snd xy)) =
    subenumR_expect k (fun yz => f (fst yz)) by intro f; rewrite Hjr Hkl.
  exists (subenumR_glue Hmid); split.
  - intro f; transitivity (subenumR_expect j (fun xy => f (fst xy))).
    + exact (subenumR_glue_raw_left Hmid f).
    + exact (Hjl f).
  - split.
    + intro g; transitivity (subenumR_expect k (fun yz => g (snd yz))).
      * exact (subenumR_glue_raw_right Hmid g).
      * exact (Hkr g).
    + exact (subenumR_glue_support Hj Hk).
Qed.

Lemma subenumR_lift_diagonal {A} (mu : SubEnumR R A) (S : A -> A -> Prop) :
  subenumR_ae mu (fun x => S x x) -> subenumR_lift S mu mu.
Proof.
  intro H; exists (subenumR_map (fun x => (x,x)) mu); split.
  - intro f; exact (subenumR_expect_map (fun x => (x,x)) mu (fun xy => f (fst xy))).
  - split.
    + intro g; exact (subenumR_expect_map (fun x => (x,x)) mu (fun xy => g (snd xy))).
    + apply subenumR_ae_map; exact H.
Qed.
Lemma subenumR_lift_ret {A B} (S : A -> B -> Prop) x y :
  S x y -> subenumR_lift S (subenumR_ret R x) (subenumR_ret R y).
Proof.
  intro H; exists (subenumR_ret R (x,y)); split; first by intro f.
  split; first by intro g.
  apply subenumR_ae_ret_iff; exact H.
Qed.
Lemma subenumR_lift_map {A B} (f : A -> B) (mu : SubEnumR R A) :
  subenumR_lift (fun x y => f x = y) mu (subenumR_map f mu).
Proof.
  exists (subenumR_map (fun x => (x,f x)) mu); split.
  - intro g; exact (subenumR_expect_map (fun x => (x,f x)) mu (fun xy => g (fst xy))).
  - split.
    + intro g; rewrite !subenumR_expect_map; reflexivity.
    + apply subenumR_ae_map; intros p x Hin Hnz; reflexivity.
Qed.
Lemma subenumR_lift_sym {A B} (S : A -> B -> Prop) (mu : SubEnumR R A) (nu : SubEnumR R B) :
  subenumR_lift S mu nu -> subenumR_lift (fun y x => S x y) nu mu.
Proof.
  intros [j [Hl [Hr Hj]]]; exists (subenumR_map (fun xy => (snd xy,fst xy)) j).
  split.
  - intro g; rewrite subenumR_expect_map; exact (Hr g).
  - split.
    + intro f; rewrite subenumR_expect_map; exact (Hl f).
    + apply subenumR_ae_map; exact Hj.
Qed.

Lemma subenumR_joint_ae {A B} (j : SubEnumR R (A*B)) (mu : SubEnumR R A) P :
  (forall f, subenumR_expect j (fun xy => f (fst xy)) = subenumR_expect mu f) ->
  subenumR_ae mu P -> subenumR_ae j (fun xy => P (fst xy)).
Proof.
  intros He Hp; apply subenumR_ae_zero_test.
  rewrite (He (fun x => real_indicator (~ P x))); apply subenumR_ae_zero_test; exact Hp.
Qed.

Theorem subenumR_lift_bind {A B C D} (S : A -> B -> Prop) (T : C -> D -> Prop)
    (mu : SubEnumR R A) (nu : SubEnumR R B) (k : A -> SubEnumR R C) (h : B -> SubEnumR R D) :
  subenumR_lift S mu nu ->
  (forall x y, S x y -> subenumR_lift T (k x) (h y)) ->
  subenumR_lift T (subenumR_bind mu k) (subenumR_bind nu h).
Proof.
  intros [j [Hl [Hr Hj]]] Hkh.
  pose good (xy : A*B) (z : SubEnumR R (C*D)) :=
    (forall f, subenumR_expect z (fun cd => f (fst cd)) = subenumR_expect (k (fst xy)) f) /\
    (forall g, subenumR_expect z (fun cd => g (snd cd)) = subenumR_expect (h (snd xy)) g) /\
    subenumR_ae z (fun cd => T (fst cd) (snd cd)).
  have Hex : forall xy, exists z, S (fst xy) (snd xy) -> good xy z.
  { intros [x y]; case: (pselect (S x y))=> H.
    - destruct (Hkh x y H) as [z Hz]; exists z; intros _; exact Hz.
    - exists (subenumR_zero R); intro Hxy; contradiction. }
  pose joint xy := proj1_sig (cid (Hex xy)).
  have Hjoint xy : S (fst xy) (snd xy) -> good xy (joint xy) := proj2_sig (cid (Hex xy)).
  exists (subenumR_bind j joint); split.
  - intro f; rewrite !subenumR_expect_bind -(Hl (fun x => subenumR_expect (k x) f)).
    apply real_enum_expect_ae_ext=> p xy Hin Hnz.
    exact (proj1 (Hjoint xy (Hj p xy Hin Hnz)) f).
  - split.
    + intro g; rewrite !subenumR_expect_bind -(Hr (fun y => subenumR_expect (h y) g)).
      apply real_enum_expect_ae_ext=> p xy Hin Hnz.
      exact (proj1 (proj2 (Hjoint xy (Hj p xy Hin Hnz))) g).
    + apply subenumR_ae_bind_iff; intros p xy Hin Hnz.
      exact (proj2 (proj2 (Hjoint xy (Hj p xy Hin Hnz)))).
Qed.

#[global] Instance SubEnumR_SemanticMeasureCoreLaws :
    @SemanticMeasureCoreLaws (SubEnumR R) (SubEnumR_SemanticMeasure R).
Proof.
  constructor; cbn.
  - intros A mu f; reflexivity.
  - intros A mu nu H f; symmetry; exact (H f).
  - intros A mu nu xi H1 H2 f; transitivity (subenumR_expect nu f); [exact (H1 f)|exact (H2 f)].
  - intros A mu p x Hin Hnz; exact I.
  - intros A mu P Q H Hmu p x Hin Hnz; exact (H x (Hmu p x Hin Hnz)).
  - intros A mu P Q HP HQ p x Hin Hnz; split; [exact (HP p x Hin Hnz)|exact (HQ p x Hin Hnz)].
  - intros A B S T mu nu H [j [Hl [Hr Hj]]]; exists j; repeat split; try assumption.
    intros p [x y] Hin Hnz; exact (H x y (Hj p (x,y) Hin Hnz)).
  - intros A S mu HS; apply subenumR_lift_diagonal; intros p x Hin Hnz; exact (HS x).
  - exact @subenumR_lift_ret.
  - intros A B S mu mu' nu He [j [Hl [Hr Hj]]]; exists j; split.
    + intro f; rewrite Hl; exact (He f).
    + split; assumption.
  - intros A B S mu nu nu' He [j [Hl [Hr Hj]]]; exists j; split; first exact Hl.
    split; last exact Hj; intro g; rewrite Hr; exact (He g).
  - exact @subenumR_lift_sym.
  - exact @subenumR_lift_comp.
Qed.

#[global] Instance SubEnumR_SemanticMeasureBindLaws :
    @SemanticMeasureBindLaws (SubEnumR R) (SubEnumR_SemanticMeasure R).
Proof.
  constructor.
  - exact (@subenumR_bind_ret_l R).
  - exact (@subenumR_bind_assoc R).
  - intros A B mu k h H f; rewrite !subenumR_expect_bind.
    apply real_enum_expect_ae_ext=> p x Hin Hnz; exact (H p x Hin Hnz f).
  - exact @subenumR_lift_bind.
Qed.

#[global] Instance SubEnumR_SemanticMeasureAELiftLaws :
    @SemanticMeasureAELiftLaws (SubEnumR R) (SubEnumR_SemanticMeasure R).
Proof.
  constructor; intros A mu P H; apply subenumR_lift_diagonal.
  intros p x Hin Hnz; split; [reflexivity|exact (H p x Hin Hnz)].
Qed.

#[global] Instance SubEnumR_SemanticMeasureCouplingAELaws :
    @SemanticMeasureCouplingAELaws (SubEnumR R) (SubEnumR_SemanticMeasure R).
Proof.
  constructor; cbn.
  - intros A B S mu nu P [j [Hl [Hr Hj]]] HP.
    have HjP := subenumR_joint_ae Hl HP.
    apply (subenumR_ae_proper (mu := subenumR_map snd j)).
    + intro g; rewrite subenumR_expect_map; exact (Hr g).
    + apply subenumR_ae_map; intros p [x y] Hin Hnz.
      exists x; split; [exact (Hj p (x,y) Hin Hnz)|exact (HjP p (x,y) Hin Hnz)].
  - intros A B S mu nu P Q [j [Hl [Hr Hj]]] HP HQ.
    have HjP := subenumR_joint_ae Hl HP.
    have HjQ : subenumR_ae j (fun xy => Q (snd xy)).
    { apply subenumR_ae_zero_test; rewrite (Hr (fun y => real_indicator (~ Q y))).
      apply subenumR_ae_zero_test; exact HQ. }
    exists j; split; first exact Hl; split; first exact Hr.
    intros p xy Hin Hnz; split; first exact (Hj p xy Hin Hnz).
    split; [exact (HjP p xy Hin Hnz)|exact (HjQ p xy Hin Hnz)].
Qed.

Lemma subenumR_lift_eq_iff {A} (mu nu : SubEnumR R A) :
  subenumR_lift eq mu nu <-> subenumR_eq mu nu.
Proof.
  split.
  - intros [j [Hl [Hr Hj]]] f; rewrite -(Hl f) -(Hr f).
    apply real_enum_expect_ae_ext=> p [x y] Hin Hnz.
    by rewrite (Hj p (x,y) Hin Hnz).
  - intro H; exists (subenumR_map (fun x => (x,x)) mu); split.
    + intro f; exact (subenumR_expect_map (fun x => (x,x)) mu (fun xy => f (fst xy))).
    + split.
      * intro g; rewrite subenumR_expect_map; exact (H g).
      * apply subenumR_ae_map; intros p x Hin Hnz; reflexivity.
Qed.

End FiniteCoupling.
