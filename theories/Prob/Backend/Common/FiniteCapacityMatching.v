(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice ssrnat seq fintype finset bigop.
Require Import PTree.Prob.Backend.Common.FiniteMatching.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Integer capacities are expanded into distinguishable copies.  The
    source labels themselves need not have distinct neighborhoods. *)
Definition capacity_copies {X : finType} (p : X -> nat) := {x : X & 'I_(p x)}.

Section CapacityCounting.
Context {X : finType} (p : X -> nat).
Local Notation CX := (capacity_copies p).

Lemma capacity_fiber_card (S : {set X}) :
  #|[set i : CX | tag i \in S]| = \sum_(x in S) p x.
Proof.
  rewrite -sum1dep_card.
  transitivity (\sum_(i : CX | (tag i \in S) && true) 1).
  { apply eq_bigl=> i. by rewrite andbT. }
  rewrite -(@sig_big_dep nat 0 _ X (fun x => @Finite.Pack 'I_(p x) (Finite.on 'I_(p x)))
    (fun x => x \in S) (fun x (j : 'I_(p x)) => true)
    (fun x (j : 'I_(p x)) => 1)).
  apply eq_bigr=> x Hx.
  by rewrite sum1_card card_ord.
Qed.

Lemma capacity_copies_card : #|{: CX}| = \sum_x p x.
Proof.
  have H := capacity_fiber_card setT.
  have HE : [set i : CX | tag i \in [set: X]] = setT.
  { by apply/setP=> i; rewrite !inE. }
  rewrite HE cardsT in H. rewrite H. apply eq_bigl=> x. by rewrite inE.
Qed.

Lemma capacity_subset_card (S : {set CX}) :
  #|S| <= \sum_(x in tag @: S) p x.
Proof.
  rewrite -capacity_fiber_card. apply subset_leq_card.
  apply/subsetP=> i Hi. rewrite inE. apply/imsetP. by exists i.
Qed.
End CapacityCounting.

Section CapacityMatching.
Context {X Y : finType} (p : X -> nat) (q : Y -> nat) (edge : X -> Y -> bool).
Local Notation CX := (capacity_copies p).
Local Notation CY := (capacity_copies q).
Let expanded (i : CX) (j : CY) := edge (tag i) (tag j).

Definition capacity_hall : Prop := forall S : {set X},
  \sum_(x in S) p x <= \sum_(y in matching_neighbors edge setT S) q y.

Lemma expanded_neighbors (S : {set CX}) :
  matching_neighbors expanded setT S =
  [set j : CY | tag j \in matching_neighbors edge setT (tag @: S)].
Proof.
  apply/setP=> j. rewrite inE. apply/idP/idP.
  - move/matching_neighborsP=> [_ [i [Hi Hij]]].
    apply/matching_neighborsP. split; [by rewrite inE|].
    exists (tag i). split=> //; apply/imsetP; by exists i.
  - move/matching_neighborsP=> [_ [x [/imsetP [i Hi Hix] Hxj]]].
    apply/matching_neighborsP. split; [by rewrite inE|].
    exists i. split=> //. by rewrite /expanded -Hix.
Qed.

Theorem capacity_hall_matching : capacity_hall ->
  exists f : CX -> option CY, finite_matching expanded setT setT f.
Proof.
  intro Hall. apply (@finite_hall_matching
    (@Finite.Pack CX (Finite.on CX)) (@Finite.Pack CY (Finite.on CY))
    expanded setT setT). intros S HS.
  rewrite expanded_neighbors capacity_fiber_card.
  exact (leq_trans (capacity_subset_card S) (Hall (tag @: S))).
Qed.

(** With equal total capacity every target copy is used exactly once.
    This is the equality-of-marginals step needed for a coupling. *)
Theorem capacity_hall_perfect_matching :
  capacity_hall -> \sum_x p x = \sum_y q y ->
  exists f : CX -> option CY,
    finite_matching expanded setT setT f /\
    forall j : CY, exists i : CX, f i = Some j.
Proof.
  intros Hall Htotal. destruct (capacity_hall_matching Hall) as [f [Hf Hinj]].
  have Hfi : injective f.
  { intros i j Hij. apply (Hinj i j); [by rewrite inE|by rewrite inE|exact Hij]. }
  have Hsome : injective (@Some CY) by intros i j; injection 1.
  have Hsubset : f @: [set: CX] \subset Some @: [set: CY].
  { apply/subsetP=> z /imsetP [i _ ->].
    have Hi : i \in [set: CX] by rewrite inE.
    destruct (Hf i Hi) as [j [Hij _]]. rewrite Hij.
    apply/imsetP. exists j=> //; by rewrite inE. }
  have Hcard : #|f @: [set: CX]| = #|Some @: [set: CY]|.
  { by rewrite (card_imset [set: CX] Hfi) (card_imset [set: CY] Hsome)
      !cardsT !capacity_copies_card Htotal. }
  have Himage : f @: [set: CX] = Some @: [set: CY].
  { apply/eqP. by rewrite eqEcard Hsubset -Hcard leqnn. }
  exists f. split; [by split|]. intro j.
  have Hin : Some j \in f @: [set: CX].
  { rewrite Himage. apply/imsetP. exists j=> //; by rewrite inE. }
  move/imsetP: Hin=> [i _ Hi]. exists i. symmetry. exact Hi.
Qed.

Theorem capacity_hall_bijection :
  capacity_hall -> \sum_x p x = \sum_y q y ->
  exists g : CX -> CY, bijective g /\ forall i, expanded i (g i).
Proof.
  intros Hall Htotal. destruct (capacity_hall_matching Hall) as [f [Hf Hi]].
  have Hvalid : forall i : CX, i \in [set: CX] by intro i; rewrite inE.
  have Hex : forall i : CX, exists j : CY, (f i == Some j) && expanded i j.
  { intro i. destruct (Hf i (Hvalid i)) as [j [Hij [_ He]]].
    exists j. by rewrite Hij eqxx He. }
  pose (g := fun i => xchoose (Hex i)).
  have Hspec : forall i, f i = Some (g i) /\ expanded i (g i).
  { intro i. have /andP [/eqP Hsome He] := xchooseP (Hex i). by split. }
  have Hgi : injective g.
  { intros i j Hij. apply (Hi i j (Hvalid i) (Hvalid j)).
    by rewrite (proj1 (Hspec i)) (proj1 (Hspec j)) Hij. }
  exists g. split.
  - apply (@inj_card_bij (@Finite.Pack CX (Finite.on CX))
      (@Finite.Pack CY (Finite.on CY)) g Hgi).
    by rewrite !capacity_copies_card Htotal.
  - intro i. exact (proj2 (Hspec i)).
Qed.
End CapacityMatching.

Section CountingPartitions.
Context {A B : finType}.

Lemma finite_card_partition (f : A -> B) (S : {set A}) :
  #|S| = \sum_y #|[set x in S | f x == y]|.
Proof.
  rewrite -sum1_card (partition_big f predT); [|by intros].
  apply eq_bigr=> y _. exact: sum1dep_card.
Qed.

Lemma finite_bijection_preimage_card (f : A -> B) (S : {set B}) :
  bijective f -> #|[set x | f x \in S]| = #|S|.
Proof.
  intro Hbij.
  transitivity #|[preim f of S]|; first by apply eq_card=> x; rewrite !inE.
  rewrite (card_preim (bij_inj Hbij)). apply eq_card=> y.
  have Hcodom : y \in codom f.
  { destruct Hbij as [g Hgf Hfg]. apply/codomP. exists (g y). symmetry. apply Hfg. }
  by rewrite !inE Hcodom.
Qed.
End CountingPartitions.

Section IntegerTransport.
Context {X Y : finType} (p : X -> nat) (q : Y -> nat) (edge : X -> Y -> bool).
Local Notation CX := (capacity_copies p).
Local Notation CY := (capacity_copies q).

(** Counts of matched copies give a finite nonnegative integer matrix
    with EXACT row and column sums and no weight outside the relation. *)
Theorem finite_capacity_transport :
  capacity_hall p q edge -> \sum_x p x = \sum_y q y ->
  exists w : X -> Y -> nat,
    (forall x, \sum_y w x y = p x) /\
    (forall y, \sum_x w x y = q y) /\
    (forall x y, 0 < w x y -> edge x y).
Proof.
  intros Hall Htotal.
  destruct (capacity_hall_bijection Hall Htotal) as [g [Hbij Hedges]].
  pose (w := fun x y => #|[set i : CX | (tag i == x) && (tag (g i) == y)]|).
  have Hfiber : forall (Z : finType) (r : Z -> nat) z,
      #|[set i : capacity_copies r | tag i == z]| = r z.
  { intros Z r z.
    have H := capacity_fiber_card r [set z].
    have HE : [set i : capacity_copies r | tag i \in [set z]] =
        [set i : capacity_copies r | tag i == z].
    { by apply/setP=> i; rewrite !inE. }
    rewrite HE big_set1 in H. exact H. }
  exists w. split.
  - intro x. rewrite -(Hfiber X p x) (finite_card_partition (fun i : CX => tag (g i))).
    apply eq_bigr=> y _. rewrite /w. apply eq_card=> i.
    by rewrite !inE.
  - split.
    + intro y.
      have Hcard : #|[set i : CX | tag (g i) == y]| = q y.
      { rewrite -(Hfiber Y q y).
        have HE : [set i : CX | tag (g i) == y] =
            [set i : CX | g i \in [set j : CY | tag j == y]].
        { by apply/setP=> i; rewrite !inE. }
        rewrite HE. exact (finite_bijection_preimage_card _ Hbij). }
      rewrite -Hcard (finite_card_partition (fun i : CX => tag i)).
      apply eq_bigr=> x _. rewrite /w. apply eq_card=> i.
      by rewrite !inE andbC.
    + intros x y Hpos. move: Hpos; rewrite /w card_gt0=> /set0Pn [i Hi].
      move: Hi; rewrite inE=> /andP [/eqP Hx /eqP Hy].
      have He := Hedges i. by rewrite Hx Hy in He.
Qed.
End IntegerTransport.
