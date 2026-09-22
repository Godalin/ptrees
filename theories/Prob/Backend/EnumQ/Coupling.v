(** Finite rational joints over the shared nonnegative container.  Coupling
    still means exact atom marginals and support in the given relation. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List Morphisms.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrfun ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteAtoms FiniteSupport FiniteListAlgebra.
From PTree.Prob.Backend.EnumQ Require Import Representation Bind Map.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Coupling.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Record coupling {A B : eqType}
    (R : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B) : Prop := {
  joint : EnumQ (A * B);
  coupling_left : emap fst joint ==EnumQ mu;
  coupling_right : emap snd joint ==EnumQ nu;
  coupling_related : forall a b, acc_mass (a,b) joint != 0 -> R a b
}.

Lemma coupling_mono {A B : eqType} (R S : A -> B -> Prop)
    (mu : EnumQ A) (nu : EnumQ B) :
  (forall a b, R a b -> S a b) -> coupling R mu nu -> coupling S mu nu.
Proof. move=> H [j HL HR Hrel]; exists j=> // a b Hab; exact: H (Hrel a b Hab). Qed.
Lemma coupling_proper_l {A B : eqType} (R : A -> B -> Prop)
    (mu mu' : EnumQ A) (nu : EnumQ B) :
  mu ==EnumQ mu' -> coupling R mu nu -> coupling R mu' nu.
Proof. move=> H [j HL HR Hrel]; exists j=> //; exact: enumQ_eq_trans HL H. Qed.
Lemma coupling_proper_r {A B : eqType} (R : A -> B -> Prop)
    (mu : EnumQ A) (nu nu' : EnumQ B) :
  nu ==EnumQ nu' -> coupling R mu nu -> coupling R mu nu'.
Proof. move=> H [j HL HR Hrel]; exists j=> //; exact: enumQ_eq_trans HR H. Qed.

Lemma entry_nonzero_acc_mass {A : eqType} (p : rat) (x : A) (mu : EnumQ A) :
  (p,x) \in enumQ_raw mu -> p != 0 -> acc_mass x mu != 0.
Proof.
  move=> Hin Hp; apply/eqP=> Hz.
  have Hzero := proj1 (enumQ_atom_zero mu x) Hz p
    (proj1 (enumQ_raw_mem p x mu) Hin).
  by rewrite Hzero eqxx in Hp.
Qed.

Lemma emap_nonzero_preimage {A B : eqType} (f : A -> B)
    (mu : EnumQ A) (b : B) :
  acc_mass b (emap f mu) != 0 -> exists a, acc_mass a mu != 0 /\ f a = b.
Proof.
  move=> Hb.
  have Hsupp := proj2 (in_supp_iff_acc_mass_ne_0 b (emap f mu)) Hb.
  rewrite /supp mem_undup in Hsupp.
  move/mapP: Hsupp=> [[p y] Hpy /= Heq]; subst y.
  move: Hpy; rewrite mem_filter=> /andP [Hp Hpy].
  change (is_true ((p,b) \in [seq (px.1,f px.2) | px <- enumQ_raw mu])) in Hpy.
  move/mapP: Hpy=> [[q a] Hqa /= Heq].
  inversion Heq; subst q b.
  exists a; split; last reflexivity.
  exact: entry_nonzero_acc_mass Hqa Hp.
Qed.

Lemma emap_fst_diag {A : eqType} (mu : EnumQ A) :
  enumQ_raw (emap fst (emap (fun a => (a,a)) mu)) = enumQ_raw mu.
Proof. rewrite emap_comp; exact: emap_id. Qed.
Lemma emap_snd_diag {A : eqType} (mu : EnumQ A) :
  enumQ_raw (emap snd (emap (fun a => (a,a)) mu)) = enumQ_raw mu.
Proof. rewrite emap_comp; exact: emap_id. Qed.
Lemma coupling_refl {A : eqType} (mu : EnumQ A) : coupling eq mu mu.
Proof.
  exists (emap (fun a => (a,a)) mu).
  - apply enumQ_eq_eq; exact: emap_fst_diag.
  - apply enumQ_eq_eq; exact: emap_snd_diag.
  - move=> a b Hab.
    have [x [_ Hx]] := emap_nonzero_preimage Hab; by inversion Hx.
Qed.
Lemma coupling_of_enumQ_eq {A : eqType} (mu nu : EnumQ A) :
  mu ==EnumQ nu -> coupling eq mu nu.
Proof. move=> H; apply (coupling_proper_r H); exact: coupling_refl. Qed.

Definition swap {A B} (p : A * B) : B * A := (snd p,fst p).
Lemma emap_fst_swap {A B : eqType} (mu : EnumQ (A*B)) :
  enumQ_raw (emap fst (emap swap mu)) = enumQ_raw (emap snd mu).
Proof. rewrite emap_comp; reflexivity. Qed.
Lemma emap_snd_swap {A B : eqType} (mu : EnumQ (A*B)) :
  enumQ_raw (emap snd (emap swap mu)) = enumQ_raw (emap fst mu).
Proof. rewrite emap_comp; reflexivity. Qed.
Lemma coupling_sym {A B : eqType} (R : A -> B -> Prop)
    (mu : EnumQ A) (nu : EnumQ B) :
  coupling R mu nu -> coupling (fun b a => R a b) nu mu.
Proof.
  move=> [j HL HR Hrel]; exists (emap swap j).
  - eapply enumQ_eq_trans; last exact HR.
    apply enumQ_eq_eq; exact: emap_fst_swap.
  - eapply enumQ_eq_trans; last exact HL.
    apply enumQ_eq_eq; exact: emap_snd_swap.
  - move=> b a Hba.
    have [[a' b'] [Hab Heq]] := emap_nonzero_preimage Hba.
    inversion Heq; subst; exact: Hrel Hab.
Qed.
Lemma coupling_emap {A B C D : eqType}
    (R : A -> B -> Prop) (S : C -> D -> Prop)
    (f : A -> C) (g : B -> D) (mu : EnumQ A) (nu : EnumQ B) :
  (forall a b, R a b -> S (f a) (g b)) ->
  coupling R mu nu -> coupling S (emap f mu) (emap g nu).
Proof.
  move=> H [j HL HR Hrel].
  exists (emap (fun xy => (f xy.1,g xy.2)) j).
  - eapply enumQ_eq_trans; last exact (emap_proper f HL).
    apply enumQ_eq_eq; by rewrite !emap_comp.
  - eapply enumQ_eq_trans; last exact (emap_proper g HR).
    apply enumQ_eq_eq; by rewrite !emap_comp.
  - move=> c d Hcd.
    have [[a b] [Hab Heq]] := emap_nonzero_preimage Hcd.
    inversion Heq; subst; exact: H (Hrel a b Hab).
Qed.

Lemma coupling_scale {A B : eqType} (R : A -> B -> Prop)
    p (Hp : 0 <= p) (mu : EnumQ A) (nu : EnumQ B) :
  coupling R mu nu -> coupling R (scale_EnumQ Hp mu) (scale_EnumQ Hp nu).
Proof.
  move=> [j HL HR Hrel]; exists (scale_EnumQ Hp j).
  - eapply enumQ_eq_trans; last exact (scale_EnumQ_proper Hp HL).
    apply enumQ_eq_eq; exact: emap_scale.
  - eapply enumQ_eq_trans; last exact (scale_EnumQ_proper Hp HR).
    apply enumQ_eq_eq; exact: emap_scale.
  - move=> a b Hab; apply Hrel; apply: contra Hab=> /eqP Hz.
    by rewrite acc_mass_scale Hz mulr0 eqxx.
Qed.
Lemma coupling_zero {A B : eqType} (R : A -> B -> Prop) :
  coupling R enumQ_zero enumQ_zero.
Proof.
  exists enumQ_zero.
  - exact: enumQ_eq_refl.
  - exact: enumQ_eq_refl.
  - move=> a b; by rewrite acc_mass_nil eqxx.
Qed.
Lemma coupling_zero_scale {A B : eqType} (R : A -> B -> Prop)
    (mu : EnumQ A) (nu : EnumQ B) :
  coupling R (scale_EnumQ (lexx 0) mu) (scale_EnumQ (lexx 0) nu).
Proof.
  exists enumQ_zero.
  - move=> a; change (0 = acc_mass a (scale_EnumQ (lexx 0) mu)).
    by rewrite acc_mass_scale mul0r.
  - move=> b; change (0 = acc_mass b (scale_EnumQ (lexx 0) nu)).
    by rewrite acc_mass_scale mul0r.
  - move=> a b; by rewrite acc_mass_nil eqxx.
Qed.
Lemma coupling_app {A B : eqType} (R : A -> B -> Prop)
    (mu1 mu2 : EnumQ A) (nu1 nu2 : EnumQ B) :
  coupling R mu1 nu1 -> coupling R mu2 nu2 ->
  coupling R (enumQ_app mu1 mu2) (enumQ_app nu1 nu2).
Proof.
  move=> [j1 HL1 HR1 Hrel1] [j2 HL2 HR2 Hrel2]; exists (enumQ_app j1 j2).
  - eapply enumQ_eq_trans; last exact (app_EnumQ_proper HL1 HL2).
    apply enumQ_eq_eq; exact: emap_app.
  - eapply enumQ_eq_trans; last exact (app_EnumQ_proper HR1 HR2).
    apply enumQ_eq_eq; exact: emap_app.
  - move=> a b Hab; rewrite acc_app in Hab.
    case H1: (acc_mass (a,b) j1 == 0).
    + apply Hrel2; apply: contra Hab=> /eqP H2.
      by rewrite (eqP H1) H2 add0r eqxx.
    + apply Hrel1; by rewrite H1.
Qed.

Lemma coupling_raw {A B : eqType} (R : A -> B -> Prop)
    (mu mu' : EnumQ A) (nu nu' : EnumQ B) :
  enumQ_raw mu = enumQ_raw mu' -> enumQ_raw nu = enumQ_raw nu' ->
  coupling R mu nu -> coupling R mu' nu'.
Proof.
  move=> H K HC; apply (coupling_proper_r (enumQ_eq_eq K)).
  exact (coupling_proper_l (enumQ_eq_eq H) HC).
Qed.

Lemma enumQ_cons_atom_nonzero {A : eqType} p (Hp : 0 <= p) y
    (mu : EnumQ A) x :
  acc_mass x mu != 0 -> acc_mass x (enumQ_cons Hp y mu) != 0.
Proof.
  move=> H; rewrite acc_mass_cons paddr_eq0.
  - by rewrite (negbTE H).
  - exact: acc_mass_nonnegative.
  - by case: (y == x).
Qed.

(** Constructive finite Kleisli extension: choose one supplied joint per
    positive entry by list induction, not by an infinite choice principle. *)
Lemma coupling_bind_joint_on_nonzero {A B C D : eqType}
    (R : C -> D -> Prop) (outer : EnumQ (A*B))
    (k : A -> EnumQ C) (h : B -> EnumQ D) :
  (forall a b, acc_mass (a,b) outer != 0 -> coupling R (k a) (h b)) ->
  coupling R (bind_EnumQ (emap fst outer) k) (bind_EnumQ (emap snd outer) h).
Proof.
  apply (enumQ_ind_raw (P := fun outer =>
    (forall a b, acc_mass (a,b) outer != 0 -> coupling R (k a) (h b)) ->
    coupling R (bind_EnumQ (emap fst outer) k) (bind_EnumQ (emap snd outer) h))).
  - move=> _; apply (coupling_raw (mu := enumQ_zero) (nu := enumQ_zero));
      try reflexivity; exact: coupling_zero.
  - move=> p Hp [a b] tail IH H.
    apply (coupling_raw
      (mu := enumQ_app (scale_EnumQ Hp (k a)) (bind_EnumQ (emap fst tail) k))
      (nu := enumQ_app (scale_EnumQ Hp (h b)) (bind_EnumQ (emap snd tail) h)));
      try reflexivity.
    apply coupling_app.
    + case Hzero: (p == 0).
      * move/eqP: Hzero=> Hzero; subst p.
        apply (coupling_raw
          (mu := scale_EnumQ (lexx 0) (k a))
          (nu := scale_EnumQ (lexx 0) (h b))); try reflexivity.
        exact: coupling_zero_scale.
      * apply coupling_scale; apply H.
        apply entry_nonzero_acc_mass with p.
        -- by rewrite /enumQ_raw /= in_cons eqxx.
        -- by rewrite Hzero.
    + apply IH=> x y Hxy; apply H; exact: enumQ_cons_atom_nonzero Hxy.
  - move=> mu nu He IH H; apply (coupling_raw
      (mu := bind_EnumQ (emap fst mu) k) (nu := bind_EnumQ (emap snd mu) h)).
    + unfold enumQ_raw in He; by rewrite /enumQ_raw /bind_EnumQ /emap /enumQ_map /finite_enum_map
        /finite_enum_bind /= He.
    + unfold enumQ_raw in He; by rewrite /enumQ_raw /bind_EnumQ /emap /enumQ_map /finite_enum_map
        /finite_enum_bind /= He.
    + apply IH=> a b Hab; apply H.
      by rewrite /acc_mass -He.
Qed.

Lemma coupling_bind {A B C D : eqType} (R : C -> D -> Prop)
    (outer : EnumQ (A*B)) (k : A -> EnumQ C) (h : B -> EnumQ D) :
  (forall a b, coupling R (k a) (h b)) ->
  coupling R (bind_EnumQ (emap fst outer) k) (bind_EnumQ (emap snd outer) h).
Proof. move=> H; apply coupling_bind_joint_on_nonzero=> a b _; exact: H. Qed.

Lemma coupling_bind_joint_on {A B C D : eqType}
    (S : A -> B -> Prop) (R : C -> D -> Prop) (outer : EnumQ (A*B))
    (k : A -> EnumQ C) (h : B -> EnumQ D) :
  (forall a b, acc_mass (a,b) outer != 0 -> S a b) ->
  (forall a b, S a b -> coupling R (k a) (h b)) ->
  coupling R (bind_EnumQ (emap fst outer) k) (bind_EnumQ (emap snd outer) h).
Proof.
  move=> H K; apply coupling_bind_joint_on_nonzero=> a b Hab; exact: K (H a b Hab).
Qed.

Lemma equality_joint_marginals {A : eqType} (j : EnumQ (A*A)) :
  (forall x y, acc_mass (x,y) j != 0 -> x = y) -> emap fst j ==EnumQ emap snd j.
Proof.
  move=> H a.
  change (enumQ_expect (fun x => if x == a then 1 else 0) (enumQ_map fst j) =
    enumQ_expect (fun x => if x == a then 1 else 0) (enumQ_map snd j)).
  rewrite !enumQ_expect_map; change
    (finite_expect (fun xy => if xy.1 == a then 1 else 0) (enumQ_raw j) =
     finite_expect (fun xy => if xy.2 == a then 1 else 0) (enumQ_raw j)).
  apply finite_expect_ae_ext; first exact (enumQ_nonnegative j).
  move=> p [x y] Hin Hnz.
  have Hxy : x = y.
  { apply H; apply entry_nonzero_acc_mass with p.
    - exact (proj2 (enumQ_raw_mem p (x,y) j) Hin).
    - exact/eqP. }
  by rewrite Hxy.
Qed.
Lemma coupling_eq_enumQ_eq {A : eqType} (mu nu : EnumQ A) :
  coupling eq mu nu -> mu ==EnumQ nu.
Proof.
  move=> [j HL HR Hrel].
  eapply enumQ_eq_trans; first exact (enumQ_eq_sym HL).
  eapply enumQ_eq_trans; [exact: equality_joint_marginals Hrel|exact HR].
Qed.

(** The data-level row retains precisely the old filtered product: entries
    with a different middle value are omitted, not replaced by zero entries. *)
Definition glue_row {A B C : eqType} (nu : EnumQ B) (jbc : EnumQ (B*C))
    (ab : rat*(A*B)) : list (rat*(A*C)) :=
  [seq (ab.1 * bc.1 / acc_mass ab.2.2 nu, (ab.2.1,bc.2.2))
    | bc <- enumQ_raw jbc & bc.2.1 == ab.2.2].

Definition glue {A B C : eqType} (nu : EnumQ B)
    (jab : EnumQ (A*B)) (jbc : EnumQ (B*C)) : EnumQ (A*C).
Proof.
  refine (enumQ_of_list (mu := List.flat_map (glue_row nu jbc) (enumQ_raw jab)) _).
  move=> w ac /List.in_flat_map [[p [a b]] [Hab Hin]].
  move/List.in_map_iff: Hin=> [[q [b' c]] [He Hbc]].
  move/List.filter_In: Hbc=> [Hbc Hb].
  inversion He; subst w ac; apply divr_ge0.
  - apply mulr_ge0.
    + exact (enumQ_nonnegative jab p (a,b) Hab).
    + exact (enumQ_nonnegative jbc q (b',c) Hbc).
  - exact: acc_mass_nonnegative.
Defined.

Lemma glue_row_expect {A B C : eqType} (nu : EnumQ B)
    (jbc : EnumQ (B*C)) (ab : rat*(A*B)) f :
  finite_expect f (glue_row nu jbc ab) =
  ab.1 * enumQ_expect (fun bc =>
    if bc.1 == ab.2.2 then (acc_mass ab.2.2 nu)^-1 * f (ab.2.1,bc.2)
    else 0) jbc.
Proof.
  rewrite /glue_row /enumQ_expect /finite_enum_expect.
  change (finite_expect f [seq (ab.1 * bc.1 / acc_mass ab.2.2 nu, (ab.2.1,bc.2.2))
      | bc <- enumQ_raw jbc & bc.2.1 == ab.2.2] =
    ab.1 * finite_expect (fun bc => if bc.1 == ab.2.2
      then (acc_mass ab.2.2 nu)^-1 * f (ab.2.1,bc.2) else 0) (enumQ_raw jbc)).
  elim: (enumQ_raw jbc)=> [|[q [b c]] tl IH] /=; first by rewrite mulr0.
  case Hb: (b == ab.2.2)=> /=.
  - by rewrite IH mulrDr !mulrA.
  - by rewrite mulr0 add0r.
Qed.

Lemma glue_expect {A B C : eqType} (nu : EnumQ B)
    (jab : EnumQ (A*B)) (jbc : EnumQ (B*C)) f :
  enumQ_expect f (glue nu jab jbc) =
  enumQ_expect (fun ab => enumQ_expect (fun bc =>
    if bc.1 == ab.2 then (acc_mass ab.2 nu)^-1 * f (ab.1,bc.2)
    else 0) jbc) jab.
Proof.
  change (finite_expect f (List.flat_map (glue_row nu jbc) (enumQ_raw jab)) =
    finite_expect (fun ab => enumQ_expect (fun bc =>
      if bc.1 == ab.2 then (acc_mass ab.2 nu)^-1 * f (ab.1,bc.2) else 0) jbc)
      (enumQ_raw jab)).
  elim: (enumQ_raw jab)=> [|[p [a b]] tl IH] //=.
  by rewrite finite_expect_app glue_row_expect IH.
Qed.

Lemma glue_middle_nonzero_l {A B : eqType} (j : EnumQ (A*B)) (nu : EnumQ B) p a b :
  emap snd j ==EnumQ nu -> List.In (p,(a,b)) (enumQ_raw j) -> p <> 0 ->
  acc_mass b nu != 0.
Proof.
  move=> H Hin Hp; rewrite -H; apply entry_nonzero_acc_mass with p; last exact/eqP.
  apply (proj2 (enumQ_raw_mem p b (emap snd j))).
  apply List.in_map_iff; exists (p,(a,b)); by split.
Qed.
Lemma glue_middle_nonzero_r {B C : eqType} (j : EnumQ (B*C)) (nu : EnumQ B) q b c :
  emap fst j ==EnumQ nu -> List.In (q,(b,c)) (enumQ_raw j) -> q <> 0 ->
  acc_mass b nu != 0.
Proof.
  move=> H Hin Hp; rewrite -H; apply entry_nonzero_acc_mass with q; last exact/eqP.
  apply (proj2 (enumQ_raw_mem q b (emap fst j))).
  apply List.in_map_iff; exists (q,(b,c)); by split.
Qed.

Lemma glue_left_expect {A B C : eqType} (nu : EnumQ B)
    (jab : EnumQ (A*B)) (jbc : EnumQ (B*C)) f :
  emap snd jab ==EnumQ nu -> emap fst jbc ==EnumQ nu ->
  enumQ_expect (fun ac => f ac.1) (glue nu jab jbc) =
  enumQ_expect (fun ab => f ab.1) jab.
Proof.
  move=> Hab Hbc; rewrite glue_expect.
  apply finite_expect_ae_ext; first exact (enumQ_nonnegative jab).
  move=> p [a b] Hin Hp.
  transitivity (((acc_mass b nu)^-1 * f a) * acc_mass b (emap fst jbc)).
  - rewrite /acc_mass /finite_atom finite_expect_map -finite_expect_scale.
    apply finite_expect_ext=> [[b' c]] /=.
    by case: (b' == b); rewrite ?mulr1 ?mulr0.
  - rewrite Hbc mulrAC mulVf ?mul1r //.
    exact: glue_middle_nonzero_l Hab Hin Hp.
Qed.

Lemma glue_right_expect {A B C : eqType} (nu : EnumQ B)
    (jab : EnumQ (A*B)) (jbc : EnumQ (B*C)) g :
  emap snd jab ==EnumQ nu -> emap fst jbc ==EnumQ nu ->
  enumQ_expect (fun ac => g ac.2) (glue nu jab jbc) =
  enumQ_expect (fun bc => g bc.2) jbc.
Proof.
  move=> Hab Hbc; rewrite glue_expect.
  rewrite /enumQ_expect /finite_enum_expect finite_expect_swap.
  apply finite_expect_ae_ext; first exact (enumQ_nonnegative jbc).
  move=> q [b c] Hin Hq.
  transitivity (((acc_mass b nu)^-1 * g c) * acc_mass b (emap snd jab)).
  - rewrite /acc_mass /finite_atom finite_expect_map -finite_expect_scale.
    apply finite_expect_ext=> [[a b']] /=.
    case Hb: (b == b').
    + move/eqP: Hb=> Hb; subst b'; by rewrite eqxx mulr1.
    + by rewrite eq_sym Hb mulr0.
  - rewrite Hab mulrAC mulVf ?mul1r //.
    exact: glue_middle_nonzero_r Hbc Hin Hq.
Qed.

Lemma glue_left_marginal {A B C : eqType} (nu : EnumQ B)
    (jab : EnumQ (A*B)) (jbc : EnumQ (B*C)) :
  emap snd jab ==EnumQ nu -> emap fst jbc ==EnumQ nu ->
  emap fst (glue nu jab jbc) ==EnumQ emap fst jab.
Proof.
  move=> H K a; change
    (enumQ_expect (fun x => if x == a then 1 else 0) (enumQ_map fst (glue nu jab jbc)) =
     enumQ_expect (fun x => if x == a then 1 else 0) (enumQ_map fst jab)).
  rewrite !enumQ_expect_map; exact (glue_left_expect (fun x => if x == a then 1 else 0) H K).
Qed.
Lemma glue_right_marginal {A B C : eqType} (nu : EnumQ B)
    (jab : EnumQ (A*B)) (jbc : EnumQ (B*C)) :
  emap snd jab ==EnumQ nu -> emap fst jbc ==EnumQ nu ->
  emap snd (glue nu jab jbc) ==EnumQ emap snd jbc.
Proof.
  move=> H K c; change
    (enumQ_expect (fun x => if x == c then 1 else 0) (enumQ_map snd (glue nu jab jbc)) =
     enumQ_expect (fun x => if x == c then 1 else 0) (enumQ_map snd jbc)).
  rewrite !enumQ_expect_map; exact (glue_right_expect (fun x => if x == c then 1 else 0) H K).
Qed.

Lemma glue_entry_preimage {A B C : eqType} (nu : EnumQ B)
    (jab : EnumQ (A*B)) (jbc : EnumQ (B*C)) w a c :
  (w,(a,c)) \in enumQ_raw (glue nu jab jbc) ->
  exists p b q, (p,(a,b)) \in enumQ_raw jab /\
    (q,(b,c)) \in enumQ_raw jbc /\ w = p*q / acc_mass b nu.
Proof.
  move=> H; have Hin := proj1 (enumQ_raw_mem w (a,c) (glue nu jab jbc)) H.
  move/List.in_flat_map: Hin=> [[p [a' b]] [Hp Hin]].
  move/List.in_map_iff: Hin=> [[q [b' c']] [He Hin]].
  move/List.filter_In: Hin=> [Hq /eqP Hb]; cbn in Hb; subst b'.
  inversion He; subst w a' c'; exists p,b,q; split.
  - exact (proj2 (enumQ_raw_mem p (a,b) jab) Hp).
  - split; last reflexivity; exact (proj2 (enumQ_raw_mem q (b,c) jbc) Hq).
Qed.
Lemma glue_related {A B C : eqType} (R : A -> B -> Prop) (S : B -> C -> Prop)
    (nu : EnumQ B) (jab : EnumQ (A*B)) (jbc : EnumQ (B*C)) :
  (forall a b, acc_mass (a,b) jab != 0 -> R a b) ->
  (forall b c, acc_mass (b,c) jbc != 0 -> S b c) ->
  forall a c, acc_mass (a,c) (glue nu jab jbc) != 0 -> exists b, R a b /\ S b c.
Proof.
  move=> HR HS a c Hac.
  have Hpos : 0 < acc_mass (a,c) (glue nu jab jbc).
  { rewrite lt0r Hac /=; exact: acc_mass_nonnegative. }
  have [w [Hin Hw]] := proj1 (enumQ_atom_positive (glue nu jab jbc) (a,c)) Hpos.
  have [p [b [q [Hp [Hq He]]]]] := glue_entry_preimage
    (proj2 (enumQ_raw_mem w (a,c) (glue nu jab jbc)) Hin).
  have Hp0 : p != 0.
  { apply/eqP=> Hz; apply Hw; by rewrite He Hz mul0r mul0r. }
  have Hq0 : q != 0.
  { apply/eqP=> Hz; apply Hw; by rewrite He Hz mulr0 mul0r. }
  exists b; split.
  - apply HR; exact: entry_nonzero_acc_mass Hp Hp0.
  - apply HS; exact: entry_nonzero_acc_mass Hq Hq0.
Qed.
Lemma coupling_comp {A B C : eqType} (R : A -> B -> Prop) (S : B -> C -> Prop)
    (mu : EnumQ A) (nu : EnumQ B) (xi : EnumQ C) :
  coupling R mu nu -> coupling S nu xi ->
  coupling (fun a c => exists b, R a b /\ S b c) mu xi.
Proof.
  move=> [jab HL HM HR] [jbc HN HK HS]; exists (glue nu jab jbc).
  - eapply enumQ_eq_trans; [exact: glue_left_marginal HM HN|exact HL].
  - eapply enumQ_eq_trans; [exact: glue_right_marginal HM HN|exact HK].
  - exact: glue_related HR HS.
Qed.

Lemma joint_nonzero_marginals {A B : eqType} (j : EnumQ (A*B)) a b :
  acc_mass (a,b) j != 0 ->
  acc_mass a (emap fst j) != 0 /\ acc_mass b (emap snd j) != 0.
Proof.
  move=> H; have Hpos : 0 < acc_mass (a,b) j.
  { rewrite lt0r H /=; exact: acc_mass_nonnegative. }
  have [p [Hin Hp]] := proj1 (enumQ_atom_positive j (a,b)) Hpos.
  split; apply entry_nonzero_acc_mass with p; try exact/eqP.
  - apply (proj2 (enumQ_raw_mem p a (emap fst j))).
    apply List.in_map_iff; exists (p,(a,b)); by split.
  - apply (proj2 (enumQ_raw_mem p b (emap snd j))).
    apply List.in_map_iff; exists (p,(a,b)); by split.
Qed.

End Coupling.
Export Coupling.
