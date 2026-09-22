(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order rat reals.
From mathcomp.classical Require Import classical_sets.
From mathcomp.analysis Require Import ereal.
Require Import PTree.Prob.Backend.Common.FiniteEnum PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Iteration PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Internal scalar model for the raw weighted EnumQ backend.  Unlike the
    SubEnumQ model, neither total mass nor intermediate upper expectations
    have a uniform finite bound.  Supremum is therefore taken in extended
    reals.  Arbitrary formal Lub nodes still need not be additive measures.
    This file alone does NOT prove preservation by quotient coupling. *)
Section ExtendedUpper.
Variable R : realType.

Fixpoint enumQ_extended_raw {A} (f : A -> \bar R) (mu : list (rat*A)) : \bar R :=
  match mu with
  | nil => 0
  | (p,x)::tail => (ratr p)%:E * f x + enumQ_extended_raw f tail
  end.
Definition enumQ_extended_expect {A} (f : A -> \bar R) (mu : EnumQ A) :=
  enumQ_extended_raw f (enumQ_raw mu).

Lemma enumQ_extended_expect_cons {A} (f : A -> \bar R) p (Hp : (0 <= p)%R) x mu :
  enumQ_extended_expect f (enumQ_cons Hp x mu) =
  (ratr p)%:E * f x + enumQ_extended_expect f mu.
Proof. reflexivity. Qed.

Lemma enumQ_extended_expect_nonnegative {A} (f : A -> \bar R) mu :
  (forall x, 0 <= f x) -> 0 <= enumQ_extended_expect f mu.
Proof.
  move=> Hf; apply (enumQ_ind_raw (P := fun mu => 0 <= enumQ_extended_expect f mu)).
  - exact: lexx.
  - move=> p Hp x tail IH; change (0 <= (ratr p)%:E * f x + enumQ_extended_expect f tail).
    apply: adde_ge0 IH; apply: mule_ge0 (Hf x).
    by rewrite lee_fin ler0q.
  - move=> a b He IH; by rewrite /enumQ_extended_expect -He.
Qed.
Lemma enumQ_extended_expect_mono {A} (f g : A -> \bar R) mu :
  (forall x, f x <= g x) -> enumQ_extended_expect f mu <= enumQ_extended_expect g mu.
Proof.
  move=> Hfg; apply (enumQ_ind_raw (P := fun mu =>
    enumQ_extended_expect f mu <= enumQ_extended_expect g mu)).
  - exact: lexx.
  - move=> p Hp x tail IH; change
      ((ratr p)%:E*f x+enumQ_extended_expect f tail <=
       (ratr p)%:E*g x+enumQ_extended_expect g tail).
    apply: leeD IH; apply: lee_wpmul2l (Hfg x).
    by rewrite lee_fin ler0q.
  - move=> a b He IH; by rewrite /enumQ_extended_expect -He.
Qed.
Lemma enumQ_extended_expect_zero {A} (mu : EnumQ A) :
  enumQ_extended_expect (fun _ => 0) mu = 0.
Proof.
  rewrite /enumQ_extended_expect; elim: (enumQ_raw mu)=> [|[p x] tail IH] //=.
  by rewrite mule0 IH adde0.
Qed.
Lemma enumQ_extended_raw_app {A} (f : A -> \bar R) mu nu :
  enumQ_extended_raw f (mu++nu) = enumQ_extended_raw f mu + enumQ_extended_raw f nu.
Proof. by elim: mu=> [|[p x] tail IH] /=; rewrite ?add0e ?IH ?addeA. Qed.
Lemma enumQ_extended_expect_app {A} (f : A -> \bar R) mu nu :
  enumQ_extended_expect f (enumQ_app mu nu) =
  enumQ_extended_expect f mu + enumQ_extended_expect f nu.
Proof. exact: enumQ_extended_raw_app. Qed.

Lemma enumQ_extended_expect_scale {A} (f : A -> \bar R) p (Hp : (0 <= p)%R) mu :
  (forall x, 0 <= f x) ->
  enumQ_extended_expect f (scale_EnumQ Hp mu) = (ratr p)%:E * enumQ_extended_expect f mu.
Proof.
  move=> Hf; apply (enumQ_ind_raw (P := fun mu =>
    enumQ_extended_expect f (scale_EnumQ Hp mu) =
    (ratr p)%:E * enumQ_extended_expect f mu)).
  - by rewrite /enumQ_extended_expect /= mule0.
  - move=> q Hq x tail IH; change
      ((ratr (p*q))%:E*f x+enumQ_extended_expect f (scale_EnumQ Hp tail) =
       (ratr p)%:E*((ratr q)%:E*f x+enumQ_extended_expect f tail)).
    rewrite IH ge0_muleDr; last 2 first.
    + apply mule_ge0; [|exact: Hf]; by rewrite lee_fin ler0q.
    + exact: enumQ_extended_expect_nonnegative.
    by rewrite rmorphM EFinM muleA.
  - move=> a b He IH; move: IH.
    change (enumQ_extended_raw f (finite_weight_map p (enumQ_raw a)) =
      (ratr p)%:E*enumQ_extended_raw f (enumQ_raw a) ->
      enumQ_extended_raw f (finite_weight_map p (enumQ_raw b)) =
      (ratr p)%:E*enumQ_extended_raw f (enumQ_raw b)).
    by rewrite He.
Qed.
Lemma enumQ_extended_expect_bind {A B} (f : B -> \bar R)
    (mu : EnumQ A) (k : A -> EnumQ B) :
  (forall x, 0 <= f x) ->
  enumQ_extended_expect f (bind_EnumQ mu k) =
    enumQ_extended_expect (fun x => enumQ_extended_expect f (k x)) mu.
Proof.
  move=> Hf; apply (enumQ_ind_raw (P := fun mu =>
    enumQ_extended_expect f (bind_EnumQ mu k) =
    enumQ_extended_expect (fun x => enumQ_extended_expect f (k x)) mu)).
  - reflexivity.
  - move=> p Hp x tail IH.
    change (enumQ_extended_expect f (enumQ_app (scale_EnumQ Hp (k x)) (bind_EnumQ tail k)) =
      (ratr p)%:E*enumQ_extended_expect f (k x)+
      enumQ_extended_expect (fun x => enumQ_extended_expect f (k x)) tail).
    by rewrite enumQ_extended_expect_app enumQ_extended_expect_scale // IH.
  - move=> a b He IH; move: IH.
    change (enumQ_extended_raw f (finite_bind (enumQ_raw a) (fun x => enumQ_raw (k x))) =
      enumQ_extended_raw (fun x => enumQ_extended_expect f (k x)) (enumQ_raw a) ->
      enumQ_extended_raw f (finite_bind (enumQ_raw b) (fun x => enumQ_raw (k x))) =
      enumQ_extended_raw (fun x => enumQ_extended_expect f (k x)) (enumQ_raw b)).
    by rewrite He.
Qed.
Lemma enumQ_extended_expect_rat {A} (f : A -> rat) mu :
  enumQ_extended_expect (fun x => (ratr (f x))%:E) mu = (ratr (enumQ_expect f mu))%:E.
Proof.
  change (enumQ_extended_raw (fun x => (ratr (f x))%:E) (enumQ_raw mu) =
    (ratr (finite_expect f (enumQ_raw mu)))%:E).
  elim: (enumQ_raw mu)=> [|[p x] tail IH] /=; first by rewrite rmorph0.
  by rewrite IH rmorphD rmorphM EFinD EFinM.
Qed.

Lemma enumQ_extended_expect_one {A} (mu : EnumQ A) :
  enumQ_extended_expect (fun _ => 1) mu = (ratr (enumQ_expect (fun _ => 1) mu))%:E.
Proof.
  rewrite (_ : (fun _ : A => (1 : \bar R)) = (fun _ => (ratr (1 : rat))%:E));
    last by apply functional_extensionality=> x; rewrite rmorph1.
  exact: enumQ_extended_expect_rat.
Qed.

Definition extended_upper (c : nat -> \bar R) := ereal_sup (range c).

Lemma extended_upper_le c b :
  (forall n, c n <= b) -> extended_upper c <= b.
Proof. move=> Hb. apply ub_ereal_sup=> x [n _ <-]. exact: Hb. Qed.

Lemma extended_upper_ge c n : c n <= extended_upper c.
Proof. apply ereal_sup_ubound. by exists n. Qed.

Lemma extended_upper_constant x : extended_upper (fun _ => x) = x.
Proof.
  apply/eqP. rewrite eq_le. apply/andP; split.
  - apply extended_upper_le=> n. exact: lexx.
  - exact: (extended_upper_ge (fun _ => x) 0%nat).
Qed.

Lemma extended_upper_mono c d :
  (forall n, c n <= d n) -> extended_upper c <= extended_upper d.
Proof.
  move=> H. apply extended_upper_le=> n.
  exact: le_trans (H n) (extended_upper_ge d n).
Qed.

Lemma extended_upper_swap (grid : nat -> nat -> \bar R) :
  extended_upper (fun i => extended_upper (grid i)) =
  extended_upper (fun j => extended_upper (fun i => grid i j)).
Proof.
  apply/eqP. rewrite eq_le. apply/andP; split;
    apply extended_upper_le=> i; apply extended_upper_le=> j.
  - eapply le_trans; [apply (extended_upper_ge (fun k => grid k j) i)|].
    exact: extended_upper_ge.
  - eapply le_trans; [apply (extended_upper_ge (grid j) i)|].
    exact: extended_upper_ge.
Qed.

Fixpoint free_omega_extended_upper {A} (mu : FreeOmega EnumQ A)
    (f : A -> \bar R) : \bar R :=
  match mu with
  | FORet x => f x
  | FOZero => 0
  | @FOSample _ _ X node k =>
      enumQ_extended_expect (fun x => free_omega_extended_upper (k x) f) node
  | FOLub c => extended_upper (fun n => free_omega_extended_upper (c n) f)
  end.

Lemma free_omega_extended_upper_nonnegative {A} (mu : FreeOmega EnumQ A)
    (f : A -> \bar R) :
  (forall x, 0 <= f x) -> 0 <= free_omega_extended_upper mu f.
Proof.
  move=> Hf. induction mu as [x| |X node k IH|c IH]; cbn [free_omega_extended_upper].
  - exact: Hf.
  - exact: lexx.
  - exact: enumQ_extended_expect_nonnegative.
  - exact: le_trans (IH 0%nat) (extended_upper_ge _ 0%nat).
Qed.

Lemma free_omega_extended_upper_mono {A} (mu : FreeOmega EnumQ A)
    (f g : A -> \bar R) :
  (forall x, f x <= g x) ->
  free_omega_extended_upper mu f <= free_omega_extended_upper mu g.
Proof.
  move=> Hfg. induction mu as [x| |X node k IH|c IH]; cbn [free_omega_extended_upper].
  - exact: Hfg.
  - exact: lexx.
  - exact: enumQ_extended_expect_mono.
  - exact: extended_upper_mono.
Qed.

Lemma free_omega_extended_upper_bind {A B} (mu : FreeOmega EnumQ A)
    (k : A -> FreeOmega EnumQ B) (f : B -> \bar R) :
  free_omega_extended_upper (free_omega_bind mu k) f =
  free_omega_extended_upper mu (fun x => free_omega_extended_upper (k x) f).
Proof.
  induction mu as [x| |X node h IH|c IH]; cbn [free_omega_bind free_omega_extended_upper].
  - reflexivity.
  - reflexivity.
  - f_equal. apply functional_extensionality. exact IH.
  - f_equal. apply functional_extensionality. exact IH.
Qed.
End ExtendedUpper.
