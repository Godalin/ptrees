Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Morphisms.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrfun ssralg ssrnum order rat.

From PTree.Prob Require Import RatSubTypes DiscreteMC EnumBindFacts EnumMap RelLift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Coupling.
Import Enum EnumMap.
Import RatSubTypes.NonnegQNotations.
Import GRing.Theory.
#[local] Open Scope subrat_scope.
#[local] Open Scope ring_scope.

Definition nnq_div (p q : nnQ) : nnQ :=
  mknnQ (Qval p / Qval q)
    (Num.Theory.divr_ge0 (le_nnQ0 p) (le_nnQ0 q)).

Lemma nnq_divE p q :
  Qval (nnq_div p q) = Qval p / Qval q.
Proof. reflexivity. Qed.

Lemma nnq_div0r p :
  nnq_div p 0 = 0.
Proof.
  apply val_inj.
  by rewrite /nnq_div /= invr0 mulr0.
Qed.

Lemma nnq_div_mul_cancel p q :
  q != 0 -> nnq_div p q * q = p.
Proof.
  move=> Hq.
  apply val_inj.
  rewrite /nnq_div /=.
  apply divfK.
  exact Hq.
Qed.

Lemma nnq_mul_div_cancel p q :
  q != 0 -> q * nnq_div p q = p.
Proof.
  move=> Hq.
  rewrite mulrC.
  exact: nnq_div_mul_cancel Hq.
Qed.

Lemma nnq_div_mul_right_cancel p q :
  q != 0 -> nnq_div (p * q) q = p.
Proof.
  move=> Hq.
  apply val_inj.
  rewrite /nnq_div /=.
  apply mulfK.
  exact Hq.
Qed.

Lemma nnq_div_zero_l q :
  nnq_div 0 q = 0.
Proof.
  apply val_inj.
  by rewrite /nnq_div /= mul0r.
Qed.

Record coupling {A B : eqType}
    (R : A -> B -> Prop) (mu : Enum A) (nu : Enum B) : Prop := {
  joint : Enum (A * B);
  coupling_left : emap fst joint ==Enum mu;
  coupling_right : emap snd joint ==Enum nu;
  coupling_related :
    forall a b,
      acc_mass (a, b) joint != RatSubTypes.nnQ_0 ->
      R a b
}.

Lemma coupling_mono {A B : eqType} (R S : A -> B -> Prop)
    (mu : Enum A) (nu : Enum B) :
  (forall a b, R a b -> S a b) ->
  coupling R mu nu ->
  coupling S mu nu.
Proof.
  move=> HRS [j HL HR Hrel].
  exists j => // a b Hab.
  exact: HRS (Hrel a b Hab).
Qed.

Lemma coupling_proper_l {A B : eqType} (R : A -> B -> Prop)
    (mu mu' : Enum A) (nu : Enum B) :
  mu ==Enum mu' -> coupling R mu nu -> coupling R mu' nu.
Proof.
  move=> Hmm [j HL HR Hrel].
  exists j => //.
  exact: enum_eq_trans HL Hmm.
Qed.

Lemma coupling_proper_r {A B : eqType} (R : A -> B -> Prop)
    (mu : Enum A) (nu nu' : Enum B) :
  nu ==Enum nu' -> coupling R mu nu -> coupling R mu nu'.
Proof.
  move=> Hnn [j HL HR Hrel].
  exists j => //.
  exact: enum_eq_trans HR Hnn.
Qed.

Lemma emap_nonzero_preimage {A B : eqType} (f : A -> B)
    (mu : Enum A) (b : B) :
  acc_mass b (emap f mu) != RatSubTypes.nnQ_0 ->
  exists a, acc_mass a mu != RatSubTypes.nnQ_0 /\ f a = b.
Proof.
  move=> Hb.
  have Hsupp : b \in supp (emap f mu).
    by apply/(in_supp_iff_acc_mass_ne_0 b (emap f mu)).
  rewrite /supp mem_undup /emap in Hsupp.
  move/mapP: Hsupp => [[p y] Hpy Hfy].
  move: Hpy; rewrite mem_filter => /andP [Hp Hpy].
  move/mapP: Hpy => [[q a] Hqa Heq].
  cbn in Heq. inversion Heq; subst q y.
  exists a; split.
  - apply/(in_supp_iff_acc_mass_ne_0 a mu).
    rewrite /supp mem_undup.
    apply/mapP.
    exists (p, a) => //.
    by rewrite mem_filter Hp Hqa.
  - by move: Hfy => /= [].
Qed.

Lemma emap_fst_diag {A : eqType} (mu : Enum A) :
  emap fst (emap (fun a => (a, a)) mu) = mu.
Proof. by elim: mu => [//|[p a] mu IH] //=; rewrite IH. Qed.

Lemma emap_snd_diag {A : eqType} (mu : Enum A) :
  emap snd (emap (fun a => (a, a)) mu) = mu.
Proof. by elim: mu => [//|[p a] mu IH] //=; rewrite IH. Qed.

Lemma coupling_refl {A : eqType} (mu : Enum A) :
  coupling eq mu mu.
Proof.
  exists (emap (fun a => (a, a)) mu).
  - apply enum_eq_eq. exact: emap_fst_diag mu.
  - apply enum_eq_eq. exact: emap_snd_diag mu.
  - move=> a b Hab.
    move: (@emap_nonzero_preimage A _
             (fun x : A => (x, x)) mu (a, b) Hab)
      => [x [_ Hx]].
    by inversion Hx.
Qed.

Lemma coupling_of_enum_eq {A : eqType} (mu nu : Enum A) :
  mu ==Enum nu -> coupling eq mu nu.
Proof.
  move=> H.
  apply (coupling_proper_r H).
  exact: coupling_refl mu.
Qed.

Definition swap {A B} (p : A * B) : B * A := (snd p, fst p).

Lemma emap_fst_swap {A B : eqType} (mu : Enum (A * B)) :
  emap fst (emap swap mu) = emap snd mu.
Proof. by elim: mu => [//|[p [a b]] mu IH] //=; rewrite IH. Qed.

Lemma emap_snd_swap {A B : eqType} (mu : Enum (A * B)) :
  emap snd (emap swap mu) = emap fst mu.
Proof. by elim: mu => [//|[p [a b]] mu IH] //=; rewrite IH. Qed.

Lemma coupling_sym {A B : eqType} (R : A -> B -> Prop)
    (mu : Enum A) (nu : Enum B) :
  coupling R mu nu ->
  coupling (fun b a => R a b) nu mu.
Proof.
  move=> [j HL HR Hrel].
  exists (emap swap j).
  - rewrite emap_fst_swap. exact HR.
  - rewrite emap_snd_swap. exact HL.
  - move=> b a Hba.
    move: (@emap_nonzero_preimage _ _
             swap j (b, a) Hba)
      => [[a' b'] [Hab Heq]].
    cbn in Heq.
    inversion Heq; subst.
    exact: Hrel Hab.
Qed.

Lemma coupling_emap {A B C D : eqType}
    (R : A -> B -> Prop) (S : C -> D -> Prop)
    (f : A -> C) (g : B -> D) (mu : Enum A) (nu : Enum B) :
  (forall a b, R a b -> S (f a) (g b)) ->
  coupling R mu nu -> coupling S (emap f mu) (emap g nu).
Proof.
  move=> HRS [j HL HR Hrel].
  have Hleft_map :
      emap fst (emap (fun xy => (f (fst xy), g (snd xy))) j) =
      emap f (emap fst j).
  { clear HL HR Hrel.
    by elim: j=> [|[p [a b]] j IH] //=; rewrite IH. }
  have Hright_map :
      emap snd (emap (fun xy => (f (fst xy), g (snd xy))) j) =
      emap g (emap snd j).
  { clear HL HR Hrel Hleft_map.
    by elim: j=> [|[p [a b]] j IH] //=; rewrite IH. }
  exists (emap (fun xy => (f (fst xy), g (snd xy))) j).
  - eapply enum_eq_trans.
    + exact: enum_eq_eq Hleft_map.
    + apply (emap_proper f). exact HL.
  - eapply enum_eq_trans.
    + exact: enum_eq_eq Hright_map.
    + apply (emap_proper g). exact HR.
  - move=> c d Hcd.
    move: (@emap_nonzero_preimage (A * B)%type (C * D)%type
      (fun xy : A * B => (f (fst xy), g (snd xy))) j (c, d) Hcd)
      => [[a b] [Hab Heq]].
    cbn in Heq. inversion Heq; subst c d.
    exact: HRS (Hrel a b Hab).
Qed.

Lemma coupling_scale {A B : eqType} (R : A -> B -> Prop)
    p (mu : Enum A) (nu : Enum B) :
  coupling R mu nu -> coupling R (scale_Enum p mu) (scale_Enum p nu).
Proof.
  move=> [j HL HR Hrel]. exists (scale_Enum p j).
  - rewrite emap_scale. exact: scale_Enum_proper HL.
  - rewrite emap_scale. exact: scale_Enum_proper HR.
  - move=> a b Hab.
    apply Hrel. apply: contra Hab=> /eqP Hz.
    rewrite acc_mass_scale Hz. apply/eqP. apply val_inj.
    cbn. exact: mulr0 (Qval p).
Qed.

Lemma coupling_zero_scale {A B : eqType} (R : A -> B -> Prop)
    (mu : Enum A) (nu : Enum B) :
  coupling R (scale_Enum 0 mu) (scale_Enum 0 nu).
Proof.
  exists [::].
  - move=> a. rewrite acc_mass_nil acc_mass_scale.
    apply val_inj. by rewrite /= mul0r.
  - move=> b. rewrite acc_mass_nil acc_mass_scale.
    apply val_inj. by rewrite /= mul0r.
  - move=> a b Hbad. by rewrite acc_mass_nil in Hbad.
Qed.

Lemma entry_nonzero_acc_mass {A : eqType}
    (p : nnQ) (x : A) (mu : Enum A) :
  (p, x) \in mu -> p != 0 -> acc_mass x mu != 0.
Proof.
  move=> Hmem Hp.
  apply/(in_supp_iff_acc_mass_ne_0 x mu).
  rewrite /supp mem_undup.
  apply/mapP.
  exists (p, x) => //.
  by rewrite mem_filter Hp Hmem.
Qed.

Lemma coupling_app {A B : eqType} (R : A -> B -> Prop)
    (mu1 mu2 : Enum A) (nu1 nu2 : Enum B) :
  coupling R mu1 nu1 -> coupling R mu2 nu2 ->
  coupling R (mu1 ++ mu2) (nu1 ++ nu2).
Proof.
  move=> [j1 HL1 HR1 Hrel1] [j2 HL2 HR2 Hrel2].
  exists (j1 ++ j2).
  - rewrite emap_app. exact: app_Enum_proper HL1 HL2.
  - rewrite emap_app. exact: app_Enum_proper HR1 HR2.
  - move=> a b Hab. rewrite acc_app in Hab.
    case H1: (acc_mass (a, b) j1 == 0).
    + apply Hrel2. apply: contra Hab=> /eqP H2.
      move/eqP: H1=> H1. rewrite H1 H2.
      apply/eqP. apply val_inj. cbn. exact: addr0 0.
    + apply Hrel1. apply/eqP=> Hz.
      have Heq0 : (acc_mass (a, b) j1 == 0) = true.
      { apply/eqP. apply val_inj. exact (f_equal Qval Hz). }
      rewrite Heq0 in H1. discriminate.
Qed.

(** Finite relational Kleisli extension.  This proof is constructive: the
    outer joint is traversed entry by entry and each continuation joint is
    scaled by that entry's weight. *)
Lemma coupling_bind {A B C D : eqType} (R : C -> D -> Prop)
    (outer : Enum (A * B))
    (k : A -> Enum C) (h : B -> Enum D) :
  (forall a b, coupling R (k a) (h b)) ->
  coupling R
    (bind_Enum (emap fst outer) k)
    (bind_Enum (emap snd outer) h).
Proof.
  move=> Hk. elim: outer=> [|[p [a b]] outer IH] /=.
  - exists [::]; first exact: enum_eq_refl.
    + exact: enum_eq_refl.
    + move=> c d Hbad. by rewrite acc_mass_nil in Hbad.
  - apply coupling_app.
    + exact: coupling_scale (Hk a b).
    + exact IH.
Qed.

(** Relational Kleisli extension over one explicit outer joint. *)
Lemma coupling_bind_joint_on {A B C D : eqType}
    (S : A -> B -> Prop) (R : C -> D -> Prop)
    (outer : Enum (A * B))
    (k : A -> Enum C) (h : B -> Enum D) :
  (forall a b, acc_mass (a, b) outer != 0 -> S a b) ->
  (forall a b, S a b -> coupling R (k a) (h b)) ->
  coupling R
    (bind_Enum (emap fst outer) k)
    (bind_Enum (emap snd outer) h).
Proof.
  move=> Houter Hk. induction outer as [|[p [a b]] outer IH]; cbn.
  - exists [::]; first exact: enum_eq_refl.
    + exact: enum_eq_refl.
    + move=> c d Hbad. by rewrite acc_mass_nil in Hbad.
  - apply coupling_app.
    + case Hp: (p == 0).
      * move/eqP: Hp=> Hp. subst p. exact: coupling_zero_scale.
      * apply coupling_scale. apply Hk. apply Houter.
        apply entry_nonzero_acc_mass with p.
        -- by rewrite in_cons eq_refl.
        -- by rewrite /negb Hp.
    + apply IH.
      move=> x y Hxy. apply Houter.
      rewrite acc_mass_cons.
      exact: ne0_of_ne0_add Hxy.
Qed.

Definition glue_row {A B C : eqType}
    (nu : Enum B) (jbc : Enum (B * C))
    (ab : nnQ * (A * B)) : Enum (A * C) :=
  [seq (nnq_div (fst ab * fst bc) (acc_mass (snd (snd ab)) nu),
         (fst (snd ab), snd (snd bc)))
    | bc <- jbc & fst (snd bc) == snd (snd ab)].

Definition glue {A B C : eqType}
    (nu : Enum B) (jab : Enum (A * B)) (jbc : Enum (B * C)) :
    Enum (A * C) :=
  flatten [seq glue_row nu jbc ab | ab <- jab].

Lemma nnq_div_add_l p q m :
  nnq_div (p + q) m = nnq_div p m + nnq_div q m.
Proof.
  apply val_inj.
  by rewrite /nnq_div /= mulrDl.
Qed.

Lemma nnq_div_mul_add_l p q r m :
  nnq_div (p * (q + r)) m =
  nnq_div (p * q) m + nnq_div (p * r) m.
Proof. by rewrite mulrDr nnq_div_add_l. Qed.

Lemma sumq_nnq_div_mul {p m} (l : seq nnQ) :
  sumq [seq nnq_div (p * q) m | q <- l] =
  nnq_div (p * sumq l) m.
Proof.
  elim: l => [|q l IH] /=.
  - by rewrite mulr0 nnq_div_zero_l.
  - rewrite IH.
    exact: (esym (nnq_div_mul_add_l p q (sumq l) m)).
Qed.

Lemma glue_row_sum {A B C : eqType}
    (nu : Enum B) (jbc : Enum (B * C))
    (ab : nnQ * (A * B)) :
  sumq (unzip1 (glue_row nu jbc ab)) =
  nnq_div
    (fst ab * acc_mass (snd (snd ab)) (emap fst jbc))
    (acc_mass (snd (snd ab)) nu).
Proof.
  elim: jbc => [|[q [b c]] j IH].
  - rewrite /glue_row /= acc_mass_nil mulr0 nnq_div_zero_l.
    reflexivity.
  - rewrite /glue_row /=.
    case E: (b == snd (snd ab)).
    + rewrite /= IH.
      rewrite /emap /= acc_mass_cons.
      have E' : (b == snd (snd ab)) = true := E.
      rewrite E' /=.
      rewrite mulrDr nnq_div_add_l.
      exact: addrC _ _.
    + rewrite /= IH.
      rewrite /emap /= acc_mass_cons E addr0.
      reflexivity.
Qed.

Lemma acc_mass_glue_row_left {A B C : eqType}
    (nu : Enum B) (jbc : Enum (B * C))
    (ab : nnQ * (A * B)) (a : A) :
  acc_mass a (emap fst (glue_row nu jbc ab)) =
  if fst (snd ab) == a
  then nnq_div
    (fst ab * acc_mass (snd (snd ab)) (emap fst jbc))
    (acc_mass (snd (snd ab)) nu)
  else 0.
Proof.
  elim: jbc => [|[q [b c]] j IH].
  - rewrite /glue_row /emap /= acc_mass_nil.
    case: (fst (snd ab) == a) => //=.
    by rewrite acc_mass_nil mulr0 nnq_div_zero_l.
  - rewrite /glue_row /=.
    case Eb: (b == snd (snd ab)).
    + rewrite /= /emap /= acc_mass_cons IH.
      rewrite /=.
      case Ea: (fst (snd ab) == a).
      * rewrite acc_mass_cons Eb.
        rewrite mulrDr nnq_div_add_l.
        reflexivity.
      * by rewrite addr0.
    + rewrite /=.
      rewrite acc_mass_cons Eb addr0.
      change
        (acc_mass a (emap fst (glue_row nu j ab)) =
         (if fst (snd ab) == a
          then nnq_div
            (fst ab * acc_mass (snd (snd ab)) (emap fst j))
            (acc_mass (snd (snd ab)) nu)
          else 0)).
      exact IH.
Qed.

Lemma acc_mass_flatten {X : eqType} (x : X) (ls : seq (Enum X)) :
  acc_mass x (flatten ls) = sumq [seq acc_mass x l | l <- ls].
Proof.
  elim: ls => [//|l ls IH] /=.
  by rewrite acc_app IH.
Qed.

Lemma coupling_middle_mass {A B : eqType}
    (j : Enum (A * B)) (nu : Enum B) :
  emap snd j ==Enum nu ->
  forall b, acc_mass b (emap snd j) = acc_mass b nu.
Proof. exact. Qed.

Lemma emap_flatten {A B} (f : A -> B) (ls : seq (Enum A)) :
  emap f (flatten ls) = flatten [seq emap f l | l <- ls].
Proof.
  by rewrite /emap map_flatten.
Qed.

Lemma joint_nonzero_marginals {A B : eqType}
    (j : Enum (A * B)) a b :
  acc_mass (a, b) j != 0 ->
  acc_mass a (emap fst j) != 0 /\ acc_mass b (emap snd j) != 0.
Proof.
  move=> Hab.
  have Hmem : (a, b) \in supp j.
  { exact: (in_supp_iff_acc_mass_ne_0 (a, b) j).2 Hab. }
  rewrite /supp mem_undup in Hmem.
  move/mapP: Hmem=> [[p [a' b']] Hentry Heq].
  move: Heq=> /= [] -> ->.
  rewrite mem_filter in Hentry. move/andP: Hentry=> [Hp Hj].
  split.
  - apply entry_nonzero_acc_mass with p.
    + rewrite /emap. apply/mapP. exists (p, (a', b'))=> //.
    + exact Hp.
  - apply entry_nonzero_acc_mass with p.
    + rewrite /emap. apply/mapP. exists (p, (a', b'))=> //.
    + exact Hp.
Qed.

Lemma sumq_if_filter {A} (P : pred A) (F : A -> nnQ) (l : seq A) :
  sumq [seq if P x then F x else 0 | x <- l] =
  sumq [seq F x | x <- l & P x].
Proof.
  elim: l => [//|x l IH] /=.
  case: (P x).
  - by rewrite /= IH.
  - rewrite /= IH.
    by rewrite add0r.
Qed.

Lemma glue_left_marginal {A B C : eqType}
    (nu : Enum B) (jab : Enum (A * B)) (jbc : Enum (B * C)) :
  emap snd jab ==Enum nu ->
  emap fst jbc ==Enum nu ->
  emap fst (glue nu jab jbc) ==Enum emap fst jab.
Proof.
  move=> Hab Hbc a.
  rewrite /glue emap_flatten acc_mass_flatten -!map_comp.
  rewrite acc_mass_emap.
  transitivity
    (sumq [seq
      if fst (snd ab) == a then fst ab else 0
      | ab <- jab]).
  - congr sumq.
    apply/eq_in_map => ab Habmem.
    change
      (acc_mass a (emap fst (glue_row nu jbc ab)) =
       (if fst (snd ab) == a then fst ab else 0)).
    rewrite acc_mass_glue_row_left.
    case Ea: (fst (snd ab) == a) => //=.
    have Hmiddle :
      acc_mass (snd (snd ab)) (emap fst jbc) =
      acc_mass (snd (snd ab)) nu := Hbc _.
    rewrite Hmiddle.
    case Ep: (fst ab == 0).
    + move/eqP: Ep => Ep.
      by rewrite Ep mul0r nnq_div_zero_l.
    + have Habmap : (fst ab, snd (snd ab)) \in emap snd jab.
        rewrite /emap.
        apply/mapP.
        exists ab.
        - exact Habmem.
        - reflexivity.
      have Ep' : fst ab != 0.
        by rewrite /negb Ep.
      have Hden : acc_mass (snd (snd ab)) nu != 0.
        rewrite -Hab.
        exact: (@entry_nonzero_acc_mass B
          (fst ab) (snd (snd ab)) (emap snd jab) Habmap Ep').
      rewrite nnq_div_mul_right_cancel //.
  - exact: sumq_if_filter (fun ab => fst (snd ab) == a) fst jab.
Qed.

Lemma sumq_map_zero {A} (xs : seq A) :
  sumq [seq 0 | _ <- xs] = 0.
Proof. by elim: xs => [//|x xs IH] /=; rewrite IH add0r. Qed.

Lemma sumq_map_add {A} (F G : A -> nnQ) (xs : seq A) :
  sumq [seq F x + G x | x <- xs] =
  sumq [seq F x | x <- xs] + sumq [seq G x | x <- xs].
Proof.
  elim: xs => [|x xs IH] /=.
  - by rewrite add0r.
  - rewrite IH.
    exact: addrACA.
Qed.

Lemma sumq_exchange {A B} (F : A -> B -> nnQ)
    (xs : seq A) (ys : seq B) :
  sumq [seq sumq [seq F x y | y <- ys] | x <- xs] =
  sumq [seq sumq [seq F x y | x <- xs] | y <- ys].
Proof.
  elim: xs => [|x xs IH] /=.
  - by rewrite sumq_map_zero.
  - rewrite IH -sumq_map_add.
    congr sumq.
Qed.

Lemma acc_mass_glue_row_right {A B C : eqType}
    (nu : Enum B) (jbc : Enum (B * C))
    (ab : nnQ * (A * B)) (c : C) :
  acc_mass c (emap snd (glue_row nu jbc ab)) =
  sumq [seq
    if (fst (snd bc) == snd (snd ab)) && (snd (snd bc) == c)
    then nnq_div (fst ab * fst bc) (acc_mass (snd (snd ab)) nu)
    else 0
    | bc <- jbc].
Proof.
  rewrite acc_mass_emap /glue_row.
  elim: jbc => [//|[q [b d]] j IH] /=.
  case Eb: (b == snd (snd ab)).
  - rewrite /=.
    case Ed: (d == c) => /=.
    + by rewrite IH.
    + by rewrite add0r IH.
  - by rewrite /= IH add0r.
Qed.

Lemma glue_column_sum {A B : eqType}
    (nu : Enum B) (jab : Enum (A * B)) (q : nnQ) (b : B) :
  sumq [seq nnq_div (q * fst ab) (acc_mass b nu)
         | ab <- jab & snd (snd ab) == b] =
  nnq_div (q * acc_mass b (emap snd jab)) (acc_mass b nu).
Proof.
  elim: jab => [|[p [a b']] jab IH] /=.
  - by rewrite acc_mass_nil mulr0 nnq_div_zero_l.
  - rewrite acc_mass_cons.
    case Eb: (b' == b).
    + rewrite /= IH mulrDr nnq_div_add_l.
      exact: addrC.
    + rewrite /= IH addr0.
      reflexivity.
Qed.

Lemma glue_right_marginal {A B C : eqType}
    (nu : Enum B) (jab : Enum (A * B)) (jbc : Enum (B * C)) :
  emap snd jab ==Enum nu ->
  emap fst jbc ==Enum nu ->
  emap snd (glue nu jab jbc) ==Enum emap snd jbc.
Proof.
  move=> Hab Hbc c.
  rewrite /glue emap_flatten acc_mass_flatten -!map_comp.
  transitivity
    (sumq [seq sumq [seq
      if (fst (snd bc) == snd (snd ab)) && (snd (snd bc) == c)
      then nnq_div (fst ab * fst bc) (acc_mass (snd (snd ab)) nu)
      else 0 | bc <- jbc] | ab <- jab]).
  - congr sumq.
    apply/eq_in_map => ab Habmem.
    exact: acc_mass_glue_row_right.
  - rewrite sumq_exchange.
    transitivity
      (sumq [seq if snd (snd bc) == c then fst bc else 0
             | bc <- jbc]).
    + congr sumq.
      apply/eq_in_map => bc Hbcmem.
      case Ec: (snd (snd bc) == c).
      * rewrite /=.
        transitivity
          (sumq [seq nnq_div (fst bc * fst ab)
                    (acc_mass (fst (snd bc)) nu)
                 | ab <- jab & snd (snd ab) == fst (snd bc)]).
        -- have Hconvert :
             sumq [seq
               if fst (snd bc) == snd (snd ab)
               then nnq_div (fst ab * fst bc)
                    (acc_mass (snd (snd ab)) nu)
               else 0 | ab <- jab] =
             sumq [seq nnq_div (fst bc * fst ab)
                       (acc_mass (fst (snd bc)) nu)
                    | ab <- jab & snd (snd ab) == fst (snd bc)].
           { clear Hab Hbc Hbcmem.
             elim: jab => [//|ab jab IH] /=.
             case Eab: (fst (snd bc) == snd (snd ab)).
             - move/eqP: Eab => Eab.
               rewrite /= -Eab eq_refl /= mulrC IH.
               reflexivity.
             - have Eab' : (snd (snd ab) == fst (snd bc)) = false.
                 by rewrite eq_sym Eab.
               by rewrite Eab' /= IH add0r. }
           transitivity
             (sumq [seq
               if fst (snd bc) == snd (snd ab)
               then nnq_div (fst ab * fst bc)
                    (acc_mass (snd (snd ab)) nu)
               else 0 | ab <- jab]).
           ++ congr sumq.
              apply/eq_in_map => ab _.
              by rewrite andbT.
           ++ exact Hconvert.
        -- rewrite glue_column_sum.
           have Hmiddle :
             acc_mass (fst (snd bc)) (emap snd jab) =
             acc_mass (fst (snd bc)) nu := Hab _.
           rewrite Hmiddle.
           case Eq: (fst bc == 0).
           ++ move/eqP: Eq => ->.
              by rewrite mul0r nnq_div_zero_l.
           ++ have Hmap : (fst bc, fst (snd bc)) \in emap fst jbc.
                rewrite /emap.
                apply/mapP. exists bc => //.
              have Hden : acc_mass (fst (snd bc)) nu != 0.
                rewrite -Hbc.
                have Hq : fst bc != 0.
                  by rewrite /negb Eq.
                exact: (@entry_nonzero_acc_mass B
                  (fst bc) (fst (snd bc)) (emap fst jbc)
                  Hmap Hq).
              exact: nnq_div_mul_right_cancel Hden.
      * rewrite /=.
        have Hz :
          sumq [seq
            if (fst (snd bc) == snd (snd ab)) &&
               (snd (snd bc) == c)
            then nnq_div (fst ab * fst bc)
                 (acc_mass (snd (snd ab)) nu)
            else 0 | ab <- jab] = 0.
        { clear Hab Hbc Hbcmem.
          rewrite Ec.
          transitivity (sumq [seq 0 | _ <- jab]).
          - congr sumq.
            apply/eq_in_map => ab _.
            by rewrite andbF.
          - exact: sumq_map_zero. }
        rewrite -Ec.
        exact Hz.
    + rewrite acc_mass_emap.
      exact: sumq_if_filter (fun bc => snd (snd bc) == c) fst jbc.
Qed.

Lemma nnq_div_prod_nonzero p q m :
  nnq_div (p * q) m != 0 -> p != 0 /\ q != 0.
Proof.
  move=> H.
  split.
  - apply: contra H => /eqP ->.
    by rewrite mul0r nnq_div_zero_l eq_refl.
  - apply: contra H => /eqP ->.
    by rewrite mulr0 nnq_div_zero_l eq_refl.
Qed.

Lemma glue_entry_preimage {A B C : eqType}
    (nu : Enum B) (jab : Enum (A * B)) (jbc : Enum (B * C))
    (w : nnQ) (a : A) (c : C) :
  (w, (a, c)) \in glue nu jab jbc ->
  exists p b q,
    (p, (a, b)) \in jab /\
    (q, (b, c)) \in jbc /\
    w = nnq_div (p * q) (acc_mass b nu).
Proof.
  elim: jab => [|[p [a' b]] jab IH] /=.
  - by rewrite /glue.
  - rewrite /glue /= mem_cat.
    move/orP=> [Hrow|Hrest].
    + rewrite /glue_row in Hrow.
      move/mapP: Hrow => [[q [b' c']] Hbc Heq].
      rewrite mem_filter in Hbc.
      move/andP: Hbc => [/eqP Hbb Hbc].
      cbn in Hbb.
      subst b'.
      inversion Heq; subst w a' c'.
      exists p, b, q.
      split; first by rewrite in_cons eq_refl.
      split=> //.
    + move: (IH Hrest) => [p' [b' [q [Hp [Hq Hw]]]]].
      exists p', b', q.
      split; first by rewrite in_cons Hp orbT.
      split=> //.
Qed.

Lemma glue_related {A B C : eqType}
    (R : A -> B -> Prop) (S : B -> C -> Prop)
    (nu : Enum B) (jab : Enum (A * B)) (jbc : Enum (B * C)) :
  (forall a b, acc_mass (a, b) jab != 0 -> R a b) ->
  (forall b c, acc_mass (b, c) jbc != 0 -> S b c) ->
  forall a c, acc_mass (a, c) (glue nu jab jbc) != 0 ->
    exists b, R a b /\ S b c.
Proof.
  move=> HR HS a c Hac.
  have Hsupp : (a, c) \in supp (glue nu jab jbc).
    exact/(in_supp_iff_acc_mass_ne_0 (a, c) (glue nu jab jbc)).
  rewrite /supp mem_undup in Hsupp.
  move/mapP: Hsupp => [[w [a' c']] Hw Hpair].
  move: Hw; rewrite mem_filter => /andP [Hw0 Hw].
  cbn in Hpair. inversion Hpair; subst a' c'.
  move: (@glue_entry_preimage A B C nu jab jbc w a c Hw)
    => [p [b [q [Hp [Hq Heq]]]]].
  have Hw' : nnq_div (p * q) (acc_mass b nu) != 0.
    by rewrite -Heq.
  move: (nnq_div_prod_nonzero Hw') => [Hp0 Hq0].
  exists b; split.
  - apply HR. exact: entry_nonzero_acc_mass Hp Hp0.
  - apply HS. exact: entry_nonzero_acc_mass Hq Hq0.
Qed.

Lemma coupling_comp {A B C : eqType}
    (R : A -> B -> Prop) (S : B -> C -> Prop)
    (mu : Enum A) (nu : Enum B) (xi : Enum C) :
  coupling R mu nu ->
  coupling S nu xi ->
  coupling (fun a c => exists b, R a b /\ S b c) mu xi.
Proof.
  move=> [jab HabL HabR HabRel] [jbc HbcL HbcR HbcRel].
  exists (glue nu jab jbc).
  - eapply enum_eq_trans.
    + exact: glue_left_marginal HabR HbcL.
    + exact HabL.
  - eapply enum_eq_trans.
    + exact: glue_right_marginal HabR HbcL.
    + exact HbcR.
  - exact: glue_related HabRel HbcRel.
Qed.

#[global] Instance Enum_ProbRelLift : ProbRelLift (M := Enum) := {
  prob_lift := @coupling;
  prob_lift_mono := @coupling_mono;
  prob_lift_proper_l := @coupling_proper_l;
  prob_lift_proper_r := @coupling_proper_r;
  prob_lift_refl := @coupling_refl;
  prob_lift_of_eq := @coupling_of_enum_eq;
  prob_lift_sym := @coupling_sym
}.

#[global] Instance Enum_ComposableProbRelLift :
    @ComposableProbRelLift Enum Enum_DiscreteInterface
      Enum_ProbRelLift := {
  prob_lift_comp := @coupling_comp
}.

End Coupling.

Export Coupling.
