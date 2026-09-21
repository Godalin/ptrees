(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype finset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Finite combinatorial infrastructure for constructing rational
    couplings.  The matching is an actual partial function, not an
    assumed transport or measure capability. *)
Section FiniteMatching.
Context {A B : finType} (edge : A -> B -> bool).

Definition matching_neighbors (V : {set B}) (S : {set A}) : {set B} :=
  [set y in V | [exists x in S, edge x y]].

Definition finite_matching (L : {set A}) (V : {set B}) (f : A -> option B) : Prop :=
  (forall x, x \in L -> exists y, f x = Some y /\ y \in V /\ edge x y) /\
  {in L &, injective f}.

Definition finite_hall (L : {set A}) (V : {set B}) : Prop :=
  forall S : {set A}, S \subset L -> #|S| <= #|matching_neighbors V S|.

Lemma matching_neighborsP (V : {set B}) (S : {set A}) (y : B) :
  reflect (y \in V /\ exists x, x \in S /\ edge x y) (y \in matching_neighbors V S).
Proof.
  rewrite /matching_neighbors inE. apply: (iffP andP).
  - move=> [Hy /existsP [x /andP [Hx Hxy]]]. split=> //. by exists x.
  - intros [Hy [x [Hx Hxy]]]. split=> //. apply/existsP. exists x. by apply/andP.
Qed.

Lemma matching_neighbors_subset V S : matching_neighbors V S \subset V.
Proof. apply/subsetP=> y /matching_neighborsP [Hy _]. exact Hy. Qed.

Lemma matching_neighbors_mono V (S T : {set A}) :
  S \subset T -> matching_neighbors V S \subset matching_neighbors V T.
Proof.
  move=> /subsetP HST. apply/subsetP=> y /matching_neighborsP [Hy [x [Hx Hxy]]].
  apply/matching_neighborsP. split=> //. exists x. split=> //; exact (HST x Hx).
Qed.

Lemma matching_neighbors0 V : matching_neighbors V set0 = set0.
Proof.
  apply/setP=> y. apply/idP/idP.
  - move/matching_neighborsP=> [_ [x [Hx _]]]. by rewrite inE in Hx.
  - by rewrite inE.
Qed.

Lemma matching_neighbors_union V S T :
  matching_neighbors V (S :|: T) = matching_neighbors V S :|: matching_neighbors V T.
Proof.
  apply/setP=> y. apply/idP/idP.
  - move/matching_neighborsP=> [Hy [x [Hx Hxy]]]. move: Hx; rewrite inE=> /orP [Hx|Hx];
      apply/setUP; [left|right]; apply/matching_neighborsP; split=> //; by exists x.
  - move/setUP=> [H|H]; move/matching_neighborsP: H=> [Hy [x [Hx Hxy]]];
      apply/matching_neighborsP; split=> //; exists x; split=> //;
      rewrite inE; apply/orP; [by left|by right].
Qed.

Lemma matching_neighbors_diff V W S :
  matching_neighbors (V :\: W) S = matching_neighbors V S :\: W.
Proof.
  apply/setP=> y. rewrite /matching_neighbors !inE.
  by case: (y \in W); case: (y \in V); case: [exists x in S, edge x y].
Qed.

Lemma matching_neighbors_restrict V (S T : {set A}) :
  T \subset S -> matching_neighbors (matching_neighbors V S) T = matching_neighbors V T.
Proof.
  intro HTS. apply/setP=> y. apply/idP/idP.
  - move/matching_neighborsP=> [/matching_neighborsP [Hy _] Hxy].
    by apply/matching_neighborsP.
  - move/matching_neighborsP=> [Hy Hxy]. apply/matching_neighborsP. split=> //.
    apply (subsetP (matching_neighbors_mono V HTS)). by apply/matching_neighborsP.
Qed.

Lemma finite_matching_empty V : finite_matching set0 V (fun _ => None).
Proof. split; [intros x; by rewrite inE|intros x y; by rewrite inE]. Qed.

Lemma finite_matching_singleton x y : edge x y ->
  finite_matching [set x] [set y] (fun _ => Some y).
Proof.
  intro Hxy. split.
  - intros z. rewrite inE=> /eqP ->. exists y. split=> //; split=> //; by rewrite inE.
  - intros a b. rewrite !inE=> /eqP -> /eqP -> _. reflexivity.
Qed.

Lemma finite_matching_union L1 L2 V1 V2 f1 f2 :
  finite_matching L1 V1 f1 -> finite_matching L2 V2 f2 ->
  [disjoint V1 & V2] ->
  finite_matching (L1 :|: L2) (V1 :|: V2)
    (fun x => if x \in L1 then f1 x else f2 x).
Proof.
  move=> [Hf1 Hi1] [Hf2 Hi2] Hd. split.
  - intros x Hx. case E: (x \in L1).
    + destruct (Hf1 x E) as [y [Hxy [Hy He]]]. exists y. split=> //.
      split=> //; apply/setUP; by left.
    + have Hx2 : x \in L2 by move: Hx; rewrite inE E /=.
      destruct (Hf2 x Hx2) as [y [Hxy [Hy He]]]. exists y. split=> //.
      split=> //; apply/setUP; by right.
  - intros x y Hx Hy.
    case Ex: (x \in L1); case Ey: (y \in L1).
    + exact (Hi1 x y Ex Ey).
    + have Hy2 : y \in L2 by move: Hy; rewrite inE Ey /=.
      destruct (Hf1 x Ex) as [u [Hu [Hu1 _]]].
      destruct (Hf2 y Hy2) as [v [Hv [Hv2 _]]].
      rewrite Hu Hv=> [[Euv]]. subst v. exfalso.
      have Hnot := disjointFr Hd Hu1. by rewrite Hv2 in Hnot.
    + have Hx2 : x \in L2 by move: Hx; rewrite inE Ex /=.
      destruct (Hf2 x Hx2) as [u [Hu [Hu2 _]]].
      destruct (Hf1 y Ey) as [v [Hv [Hv1 _]]].
      rewrite Hu Hv=> [[Euv]]. subst v. exfalso.
      have Hnot := disjointFr Hd Hv1. by rewrite Hu2 in Hnot.
    + have Hx2 : x \in L2 by move: Hx; rewrite inE Ex /=.
      have Hy2 : y \in L2 by move: Hy; rewrite inE Ey /=.
      exact (Hi2 x y Hx2 Hy2).
Qed.

Lemma finite_hall_tight_left L V (S : {set A}) :
  finite_hall L V -> S \subset L -> finite_hall S (matching_neighbors V S).
Proof.
  intros Hall HSL T HTS. rewrite (matching_neighbors_restrict V HTS).
  apply Hall. exact (subset_trans HTS HSL).
Qed.

Lemma finite_hall_tight_right L V (S : {set A}) :
  finite_hall L V -> S \subset L -> #|matching_neighbors V S| = #|S| ->
  finite_hall (L :\: S) (V :\: matching_neighbors V S).
Proof.
  intros Hall HSL Htight T HT.
  have HST : S :&: T = set0.
  { apply/setP=> x. apply/idP/idP; [|by rewrite inE].
    rewrite inE=> /andP [HxS HxT].
    have /setDP [_ Hnot] := subsetP HT x HxT. by rewrite HxS in Hnot. }
  have HSLT : S :|: T \subset L.
  { apply/subsetP=> x /setUP [Hx|Hx]; [exact (subsetP HSL x Hx)|].
    exact (subsetP (subset_trans HT (subsetDl L S)) x Hx). }
  have Hineq := Hall (S :|: T) HSLT.
  rewrite matching_neighbors_union cardsU HST cards0 subn0 in Hineq.
  have Hcard := cardsUI (matching_neighbors V S) (matching_neighbors V T).
  have Hdiff := cardsID (matching_neighbors V S) (matching_neighbors V T).
  rewrite setIC in Hdiff.
  rewrite matching_neighbors_diff. apply/leP. move/leP: Hineq=> Hineq.
  rewrite Htight in Hcard. rewrite -!plusE in Hcard Hdiff Hineq. lia.
Qed.

(** Hall's finite matching theorem, with explicit construction data.
    Induction splits at a tight subset; if no proper nonempty subset is
    tight, any edge can be removed while preserving the Hall inequalities. *)
Theorem finite_hall_matching L V :
  finite_hall L V -> exists f, finite_matching L V f.
Proof.
  have bounded : forall n (L : {set A}) (V : {set B}), #|L| < n ->
      finite_hall L V -> exists f, finite_matching L V f.
  { elim=> [|n IH] L0 V0 Hsize Hall; [by rewrite ltn0 in Hsize|].
    case EL: (L0 == set0).
    { move/eqP: EL=> ->. exists (fun _ => None). apply finite_matching_empty. }
    case Etight: [exists S : {set A},
      [&& S \proper L0, S != set0 & #|matching_neighbors V0 S| == #|S|]].
    - move/existsP: Etight=> [S /and3P [Hproper Hnonzero /eqP Htight]].
      have Hproper' := Hproper. move: Hproper'; rewrite properEcard=> /andP [HSL Hcard].
      (* Use the cardinal characterization explicitly, rather than
         identifying a syntactic subset with a strictly smaller domain. *)
      have Hsmall : #|S| < n.
      { move: Hproper. rewrite properEcard=> /andP [_ Hless].
        exact (leq_trans Hless (ltnSE Hsize)). }
      have Hrestsmall : #|L0 :\: S| < n.
      { rewrite (cardsDS HSL). have Hpos : 0 < #|S| by rewrite card_gt0.
        move/ltP: Hpos=> Hpos. move/ltP: Hsize=> Hsize.
        have Hbound := subset_leq_card HSL. move/leP: Hbound=> Hbound.
        apply/ltP. rewrite -minusE. lia. }
      destruct (IH S (matching_neighbors V0 S) Hsmall
        (finite_hall_tight_left Hall HSL)) as [f Hf].
      destruct (IH (L0 :\: S) (V0 :\: matching_neighbors V0 S) Hrestsmall
        (finite_hall_tight_right Hall HSL Htight)) as [g Hg].
      have Hd : [disjoint matching_neighbors V0 S & V0 :\: matching_neighbors V0 S].
      { rewrite disjoints_subset. apply/subsetP=> y Hy. rewrite inE.
        apply/negP=> /setDP [_ Hnot]. by rewrite Hy in Hnot. }
      have Hjoined := finite_matching_union Hf Hg Hd.
      have Hleft : S :|: (L0 :\: S) = L0.
      { rewrite -{1}(setIidPl HSL) setIC. exact: setID. }
      have Hright : matching_neighbors V0 S :|: (V0 :\: matching_neighbors V0 S) = V0.
      { rewrite -{1}(setIidPl (matching_neighbors_subset V0 S)) setIC. exact: setID. }
      rewrite Hleft Hright in Hjoined.
      exists (fun x => if x \in S then f x else g x). exact Hjoined.
    - have Hnonempty : L0 != set0 by rewrite EL.
      move/set0Pn: Hnonempty=> [a Ha].
      have Hsingle : [set a] \subset L0 by rewrite sub1set.
      have Hneighbor := Hall [set a] Hsingle.
      rewrite cards1 card_gt0 in Hneighbor.
      move/set0Pn: Hneighbor=> [b /matching_neighborsP [Hb [x [Hx Hab]]]].
      move: Hx; rewrite inE=> /eqP Hxa. subst x.
      have Hrest : finite_hall (L0 :\ a) (V0 :\ b).
      { intros T HT. case ET: (T == set0).
        { move/eqP: ET=> ->. by rewrite cards0. }
        have HTL := subset_trans HT (subsetDl L0 [set a]).
        have HaT : a \notin T by move: HT; rewrite subsetD1=> /andP [].
        have HTproper : T \proper L0.
        { rewrite properEneq HTL andbT. apply/eqP=> E. subst T. by rewrite Ha in HaT. }
        have Hstrict : #|T| < #|matching_neighbors V0 T|.
        { have Hle := Hall T HTL.
          rewrite ltn_neqAle Hle andbT. apply/eqP=> Heq.
          have Hexists : [exists S : {set A},
              [&& S \proper L0, S != set0 & #|matching_neighbors V0 S| == #|S|]].
          { apply/existsP. exists T. apply/and3P. split=> //.
            - by rewrite ET.
            - by rewrite Heq. }
          by rewrite Etight in Hexists. }
        rewrite matching_neighbors_diff.
        have Hcount := cardsD1 b (matching_neighbors V0 T).
        move/ltP: Hstrict=> Hstrict. apply/leP.
        case: (b \in matching_neighbors V0 T) Hcount=> Hcount;
          rewrite -plusE in Hcount; cbn in Hcount; lia. }
      have Hsmall : #|L0 :\ a| < n.
      { have Hlt : #|L0 :\ a| < #|L0|.
        { move: (properD1 Ha). by rewrite properEcard=> /andP []. }
        exact (leq_trans Hlt (ltnSE Hsize)). }
      destruct (IH (L0 :\ a) (V0 :\ b) Hsmall Hrest) as [g Hg].
      have Hd : [disjoint [set b] & V0 :\ b] by rewrite disjoints1 setD11.
      have Hjoined := finite_matching_union (finite_matching_singleton Hab) Hg Hd.
      rewrite (setD1K Ha) (setD1K Hb) in Hjoined.
      exists (fun x => if x \in [set a] then Some b else g x). exact Hjoined. }
  intro Hall. exact (bounded #|L|.+1 L V (ltnSn _) Hall).
Qed.
End FiniteMatching.
