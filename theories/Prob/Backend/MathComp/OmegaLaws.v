(** Checked native countable limits. Returned events increase; cemetery mass
    is not part of the order. No PTree universe relaxation is used here. *)
Set Warnings "-notation-overridden,-ambiguous-paths,-redundant-canonical-projection".
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype
  bigop ssralg ssrnum order reals boolp classical_sets functions fsbigop.
From mathcomp Require Import topology normedtype sequences measure ereal numfun
  lebesgue_measure lebesgue_integral.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws OrderLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory HBNNSimple.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section NativeSup.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Context {A : Type} (chain : nat -> M A).
Hypothesis increasing : forall n, mathcomp_node_le (chain n) (chain n.+1).

Definition mathcomp_lub_value (U : set (mc_carrier A)) : \bar R :=
  ereal_sup [set mathcomp_kernel_root (chain n) (U `&` mc_returned) | n in setT].

Lemma mathcomp_lub_value_ge0 U : 0 <= mathcomp_lub_value U.
Proof.
  apply: ereal_sup_ge; exists (mathcomp_kernel_root (chain 0) (U `&` mc_returned));
    last exact: measure_ge0.
  by exists 0%N.
Qed.

Lemma mathcomp_lub_value0 : mathcomp_lub_value set0 = 0.
Proof.
  apply/eqP; rewrite eq_le mathcomp_lub_value_ge0 andbT.
  apply: ub_ereal_sup => _ [n _ <-]; by rewrite set0I measure0.
Qed.

Lemma mathcomp_lub_value_upper U n :
  mathcomp_kernel_root (chain n) (U `&` mc_returned) <= mathcomp_lub_value U.
Proof.
  apply: ereal_sup_ge; exists (mathcomp_kernel_root (chain n) (U `&` mc_returned));
    last exact: lexx.
  by exists n.
Qed.

Lemma mathcomp_returned_chain_increasing U :
  nondecreasing_seq (fun n => mathcomp_kernel_root (chain n) (U `&` mc_returned)).
Proof.
  apply/nondecreasing_seqP => n; apply: increasing; first by [].
  by move=> [_].
Qed.

Lemma mathcomp_lub_value_cvg U :
  (fun n => mathcomp_kernel_root (chain n) (U `&` mc_returned)) @ \oo -->
  mathcomp_lub_value U.
Proof. exact: ereal_nondecreasing_cvgn (mathcomp_returned_chain_increasing U). Qed.

Lemma mathcomp_lub_value_additive : additive2 mathcomp_lub_value.
Proof.
  move=> U V mU mV Hdis.
  have Hd : (U `&` mc_returned) `&` (V `&` mc_returned) = set0.
  { apply/seteqP; split; last by [].
    move=> x [[Ux _] [Vx _]].
    have Huv : (U `&` V) x by split.
    by rewrite Hdis in Huv. }
  have Hseq : (fun n => mathcomp_kernel_root (chain n) ((U `|` V) `&` mc_returned)) =
    (fun n => mathcomp_kernel_root (chain n) (U `&` mc_returned) +
              mathcomp_kernel_root (chain n) (V `&` mc_returned)).
  { apply/funext => n; by rewrite setIUl measureU. }
  have Hc := mathcomp_lub_value_cvg (U := U `|` V).
  rewrite Hseq in Hc.
  have Hsum := cvgeD (ge0_adde_def (mathcomp_lub_value_ge0 U)
    (mathcomp_lub_value_ge0 V)) (mathcomp_lub_value_cvg (U := U)) (mathcomp_lub_value_cvg (U := V)).
  exact: cvg_unique Hc (Hsum (@filter_filter _ _ eventually_filter)).
Qed.

HB.instance Definition mathcomp_lub_value_content :=
  @isContent.Build _ (mc_carrier A) R mathcomp_lub_value
    mathcomp_lub_value_ge0 ((additive2P mathcomp_lub_value0).2 mathcomp_lub_value_additive).

Lemma mathcomp_lub_value_subadditive : measurable_subset_sigma_subadditive mathcomp_lub_value.
Proof.
  move=> U F mF mU Hsub; apply: ub_ereal_sup => _ [n _ <-].
  apply: (le_trans (@measure_sigma_subadditive _ R (mc_carrier A)
    (mathcomp_kernel_root (chain n)) (U `&` mc_returned)
    (fun i => F i `&` mc_returned) _ _ _)).
  - by move=> i.
  - by [].
  - move=> x [Ux Hx]; have [i _ Fix] := Hsub x Ux; exists i; first exact I.
    by split.
  - apply: lee_nneseries; first by move=> i _ _; exact: measure_ge0.
    move=> i _; exact: mathcomp_lub_value_upper.
Qed.

HB.instance Definition mathcomp_lub_value_measure :=
  @Content_SigmaSubAdditive_isMeasure.Build _ R (mc_carrier A)
    mathcomp_lub_value mathcomp_lub_value_subadditive.

Lemma mathcomp_lub_value_le1 : mathcomp_lub_value setT <= 1.
Proof.
  apply: ub_ereal_sup => _ [n _ <-].
  apply: (le_trans _ (mathcomp_kernel_root_le1 (chain n))).
  apply: le_measure => //; by rewrite inE.
Qed.

HB.instance Definition mathcomp_lub_value_subprobability :=
  @Measure_isSubProbability.Build _ _ R mathcomp_lub_value mathcomp_lub_value_le1.

Definition mathcomp_native_lub : M A :=
  mathcomp_source_kernel [the subprobability (mc_carrier A) R of mathcomp_lub_value].

Lemma mathcomp_native_lub_spec : mathcomp_kernel_lub chain mathcomp_native_lub.
Proof.
  move=> U mU Hb.
  change (mathcomp_lub_value U =
    ereal_sup [set mathcomp_kernel_root (chain n) U | n in setT]).
  rewrite /mathcomp_lub_value.
  have -> : U `&` mc_returned = U.
  { apply/seteqP; split; first by move=> x [].
    move=> [|x] Hx; first by exfalso; apply: Hb.
    by split. }
  reflexivity.
Qed.
End NativeSup.

Section NativeContinuity.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).

Lemma mathcomp_native_sintegral_cvg {A} (chain : nat -> M A) out
    (h : {nnsfun mc_carrier A >-> R}) :
  (forall n, mathcomp_node_le (chain n) (chain n.+1)) ->
  mathcomp_kernel_lub chain out -> h MCBottom = 0%R ->
  (fun n => sintegral (mathcomp_kernel_root (chain n)) h) @ \oo -->
    sintegral (mathcomp_kernel_root out) h.
Proof.
  move=> Hi Hl Hz.
  under eq_fun do rewrite sintegralE fsbig_finite //=.
  rewrite sintegralE fsbig_finite //=.
  apply: cvg_nnesum => r _.
  - near=> n; apply: nnsfun_mulemu_ge0.
  - case: (eqVneq r 0%R) => [->|Hr].
      under eq_fun do rewrite mul0e.
      rewrite mul0e; exact: cvg_cst.
    apply: cvgeZl => //=.
    have Hb : ~ (h @^-1` [set r]) MCBottom.
    { move=> H; move: Hr; by rewrite -H Hz eqxx. }
    have Hm : measurable (h @^-1` [set r]) by [].
    rewrite (Hl _ Hm Hb).
    apply: ereal_nondecreasing_cvgn.
    apply/nondecreasing_seqP => n; exact: Hi.
  Unshelve. all: by end_near.
Qed.
Lemma mathcomp_native_integral_lub {A} (chain : nat -> M A) out
    (f : mc_carrier A -> \bar R) :
  (forall n, mathcomp_node_le (chain n) (chain n.+1)) ->
  mathcomp_kernel_lub chain out ->
  (forall x, 0 <= f x) -> f MCBottom = 0 ->
  \int[mathcomp_kernel_root out]_x f x =
    ereal_sup [set \int[mathcomp_kernel_root (chain n)]_x f x | n in setT].
Proof.
  move=> Hi Hl Hpos Hz; apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite ge0_integralE //=.
    apply: ub_ereal_sup => _ [h /= Hh] <-.
    have Hhz : h MCBottom = 0%R.
    { apply/eqP; rewrite eq_le; apply/andP; split; last exact: fun_ge0.
      have := Hh MCBottom; by rewrite /patch mem_set // Hz lee_fin. }
    apply: (cvge_le _ (mathcomp_native_sintegral_cvg Hi Hl Hhz)).
    near=> n; apply: ereal_sup_ge.
    exists (\int[mathcomp_kernel_root (chain n)]_x f x); first by exists n.
    rewrite ge0_integralE //=.
    apply: ereal_sup_ge; exists (sintegral (mathcomp_kernel_root (chain n)) h).
      by exists h.
    exact: lexx.
  - apply: ub_ereal_sup => _ [n _ <-].
    apply: mathcomp_native_integral_le => //.
    exact: mathcomp_native_lub_upper Hl.
  Unshelve. all: by end_near.
Qed.

Lemma mathcomp_native_bind_lub {A B} (chain : nat -> M A) out
    (k : A -> M B) :
  (forall n, mathcomp_node_le (chain n) (chain n.+1)) ->
  mathcomp_kernel_lub chain out ->
  mathcomp_kernel_lub (fun n => mathcomp_kernel_bind (chain n) k)
    (mathcomp_kernel_bind out k).
Proof.
  move=> Hi Hl U mU Hb; rewrite mathcomp_kernel_root_bind.
  have Hz : mathcomp_kernel_extend_measure k MCBottom U = 0.
  { change (dirac MCBottom U = (0 : \bar R)).
    rewrite /dirac indicE.
    have -> : (MCBottom \in U) = false by apply/asboolPn.
    reflexivity. }
  have Hp x : 0 <= mathcomp_kernel_extend_measure k x U by exact: measure_ge0.
  rewrite (mathcomp_native_integral_lub Hi Hl Hp Hz).
  congr (ereal_sup _); apply: eq_imagel => n.
Qed.


#[global] Instance MathCompNativeOmegaLaws :
  @SemanticOmegaLaws M (MathCompNodeSemanticMeasure R)
    (MathCompNodeSemanticOmega R).
Proof.
  constructor.
  - move=> A chain Hi; exists (mathcomp_native_lub Hi).
    exact: mathcomp_native_lub_spec.
  - exact: mathcomp_kernel_lub_unique.
  - move=> A c d mu nu He Hc Hd.
    apply: mathcomp_kernel_lub_unique Hd.
    exact: mathcomp_kernel_lub_proper He Hc.
  - exact: mathcomp_kernel_lub_proper.
  - exact @mathcomp_native_bind_lub.
Qed.
Lemma mathcomp_native_bind_lub_k {A B} (mu : M A)
    (chain : A -> nat -> M B) (out : A -> M B) :
  (forall x n, mathcomp_node_le (chain x n) (chain x n.+1)) ->
  (forall x, mathcomp_kernel_lub (chain x) (out x)) ->
  mathcomp_kernel_lub (fun n => mathcomp_kernel_bind mu (fun x => chain x n))
    (mathcomp_kernel_bind mu out).
Proof.
  move=> Hi Hl U mU Hb.
  pose f n x := mathcomp_kernel_extend_measure (fun a => chain a n) x U.
  have Hf n : measurable_fun setT (f n).
  { exact: measurable_mathcomp_kernel_extend. }
  have Hpos n x : setT x -> 0 <= f n x by move=> _; exact: measure_ge0.
  have Hinc x : setT x -> nondecreasing_seq (fun n => f n x).
  { move=> _; apply/nondecreasing_seqP => n.
    case: x => [|a]; first exact: lexx.
    exact: Hi. }
  have Hlim x : limn (fun n => f n x) = mathcomp_kernel_extend_measure out x U.
  { case: x => [|a]; first exact: lim_cst.
    apply: cvg_lim => //.
    change ((fun n => mathcomp_kernel_root (chain a n) U) @ \oo -->
      mathcomp_kernel_root (out a) U).
    rewrite (Hl a U mU Hb).
    exact: ereal_nondecreasing_cvgn (Hinc (MCValue a) I). }
  rewrite mathcomp_kernel_root_bind.
  under eq_integral do rewrite -Hlim.
  rewrite (monotone_convergence _ measurableT Hf Hpos Hinc).
  apply: cvg_lim => //; apply: ereal_nondecreasing_cvgn.
  apply/nondecreasing_seqP => n.
  change (mathcomp_kernel_root (mathcomp_kernel_bind mu (fun x => chain x n)) U <=
    mathcomp_kernel_root (mathcomp_kernel_bind mu (fun x => chain x n.+1)) U).
  apply: mathcomp_native_bind_le_k => // x; exact: Hi.
Qed.
Lemma mathcomp_native_bind_ae_eq {A B} (mu : M A) (Good : A -> Prop)
    (k h : A -> M B) :
  mathcomp_kernel_ae mu Good ->
  (forall x, Good x -> mathcomp_kernel_eq (k x) (h x)) ->
  mathcomp_kernel_eq (mathcomp_kernel_bind mu k) (mathcomp_kernel_bind mu h).
Proof.
  move=> Hae He U mU Hb; rewrite !mathcomp_kernel_root_bind.
  apply: ae_eq_integral => //.
  rewrite /ae_eq /almost_everywhere.
  eapply negligibleS; last exact Hae.
  move=> [|a] Hbad /=; first by exfalso; apply: Hbad.
  move=> Ha; apply: Hbad => _; exact: He.
Qed.

Lemma mathcomp_native_bind_lub_ae {A B} (mu : M A) (Good : A -> Prop)
    (chain : A -> nat -> M B) (out : A -> M B) :
  mathcomp_kernel_ae mu Good ->
  (forall x, Good x -> forall n, mathcomp_node_le (chain x n) (chain x n.+1)) ->
  (forall x, Good x -> mathcomp_kernel_lub (chain x) (out x)) ->
  mathcomp_kernel_lub (fun n => mathcomp_kernel_bind mu (fun x => chain x n))
    (mathcomp_kernel_bind mu out).
Proof.
  move=> Hae Hi Hl.
  pose c x n := if asbool (Good x) then chain x n else mathcomp_kernel_zero R.
  pose o x := if asbool (Good x) then out x else mathcomp_kernel_zero R.
  have Hc x n : mathcomp_node_le (c x n) (c x n.+1).
  { rewrite /c; case: asboolP => H; [exact: Hi|exact: mathcomp_native_le_refl]. }
  have Ho x : mathcomp_kernel_lub (c x) (o x).
  { rewrite /c /o; case: asboolP => H; [exact: Hl|exact: mathcomp_native_lub_constant]. }
  have Hlim := mathcomp_native_bind_lub_k mu Hc Ho.
  have He n : mathcomp_kernel_eq (mathcomp_kernel_bind mu (fun x => c x n))
      (mathcomp_kernel_bind mu (fun x => chain x n)).
  { apply: mathcomp_native_bind_ae_eq Hae _ => x Hx.
    rewrite /c (asboolT Hx); exact: mathcomp_kernel_eq_refl. }
  have Heo : mathcomp_kernel_eq (mathcomp_kernel_bind mu o) (mathcomp_kernel_bind mu out).
  { apply: mathcomp_native_bind_ae_eq Hae _ => x Hx.
    rewrite /o (asboolT Hx); exact: mathcomp_kernel_eq_refl. }
  have Hlim' := mathcomp_kernel_lub_proper He Hlim.
  exact: mathcomp_kernel_lub_limit_proper Heo Hlim'.
Qed.

Lemma mathcomp_native_bind_zero {A B} (mu : M A) :
  mathcomp_kernel_eq (mathcomp_kernel_bind mu (fun _ => @mathcomp_kernel_zero R B))
    (mathcomp_kernel_zero R).
Proof.
  move=> U mU Hb; rewrite mathcomp_kernel_root_bind (mathcomp_native_zero_returned R Hb).
  transitivity (\int[mathcomp_kernel_root mu]_x (0 : \bar R)); last exact: integral0.
  apply: eq_integral => [[|a] _].
  - exact: mathcomp_native_zero_returned.
  - exact: mathcomp_native_zero_returned.
Qed.

#[global] Instance MathCompNativeMixedOmegaLaws :
  @MixedMeasureOmegaLaws M M (MathCompNodeSemanticMeasure R)
    (MathCompNodeSemanticMeasure R) (MathCompNativeMixedMeasure R)
    (MathCompNodeSemanticOmega R).
Proof.
  constructor; [exact @mathcomp_native_bind_zero|exact @mathcomp_native_bind_lub_ae].
Qed.
End NativeContinuity.

Section NativeDiagonal.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).

Lemma mathcomp_native_le_steps {A} (c : nat -> M A) :
  (forall n, mathcomp_node_le (c n) (c n.+1)) ->
  forall n m, (n <= m)%N -> mathcomp_node_le (c n) (c m).
Proof.
  move=> Hi n m Hnm U mU Hb.
  have Hmono : nondecreasing_seq (fun i => mathcomp_kernel_root (c i) U).
  { apply/nondecreasing_seqP => i; exact: Hi. }
  exact: Hmono.
Qed.

Lemma mathcomp_native_double_diagonal {A} (grid : nat -> nat -> M A)
    (rows : nat -> M A) out :
  (forall i n, mathcomp_node_le (grid i n) (grid i n.+1)) ->
  (forall j n, mathcomp_node_le (grid n j) (grid n.+1 j)) ->
  (forall i, mathcomp_kernel_lub (grid i) (rows i)) ->
  mathcomp_kernel_lub rows out ->
  mathcomp_kernel_lub (fun n => grid n n) out.
Proof.
  move=> Hr Hc Hrows Hout U mU Hb.
  rewrite (Hout U mU Hb).
  apply/eqP; rewrite eq_le; apply/andP; split.
  - apply: ub_ereal_sup => _ [i _ <-].
    rewrite (Hrows i U mU Hb).
    apply: ub_ereal_sup => _ [j _ <-].
    apply: ereal_sup_ge.
    exists (mathcomp_kernel_root (grid (maxn i j) (maxn i j)) U);
      first by exists (maxn i j).
    have H1 := @mathcomp_native_le_steps A (grid i) (Hr i)
      j (maxn i j) (leq_maxr i j) U mU Hb.
    have H2 := @mathcomp_native_le_steps A (fun n => grid n (maxn i j))
      (Hc (maxn i j)) i (maxn i j) (leq_maxl i j) U mU Hb.
    exact: le_trans H1 H2.
  - apply: ub_ereal_sup => _ [n _ <-].
    apply: ereal_sup_ge; exists (mathcomp_kernel_root (rows n) U);
      first by exists n.
    exact: (@mathcomp_native_lub_upper R A (grid n) (rows n) n (Hrows n) U mU Hb).
Qed.

#[global] Instance MathCompNativeFubiniLaws :
  @SemanticOmegaFubiniLaws M (MathCompNodeSemanticMeasure R)
    (MathCompNodeSemanticOmega R).
Proof. constructor; exact @mathcomp_native_double_diagonal. Qed.

Lemma mathcomp_native_bind_diagonal {A B} (source : nat -> M A) source_out
    (kernels : A -> nat -> M B) (kernel_out : A -> M B) :
  (forall n, mathcomp_node_le (source n) (source n.+1)) ->
  (forall x n, mathcomp_node_le (kernels x n) (kernels x n.+1)) ->
  mathcomp_kernel_lub source source_out ->
  (forall x, mathcomp_kernel_lub (kernels x) (kernel_out x)) ->
  mathcomp_kernel_lub
    (fun n => mathcomp_kernel_bind (source n) (fun x => kernels x n))
    (mathcomp_kernel_bind source_out kernel_out).
Proof.
  move=> Hs Hk Hsl Hkl.
  apply: (@mathcomp_native_double_diagonal B
    (fun i j => mathcomp_kernel_bind (source i) (fun x => kernels x j))
    (fun n => mathcomp_kernel_bind (source n) kernel_out)
    (mathcomp_kernel_bind source_out kernel_out)).
  - move=> i n; apply: mathcomp_native_bind_le_k => x; exact: Hk.
  - move=> j n; exact: mathcomp_native_bind_le_mu.
  - move=> i; exact: (@mathcomp_native_bind_lub_k R A B (source i) kernels kernel_out Hk Hkl).
  - exact: (@mathcomp_native_bind_lub R A B source source_out kernel_out Hs Hsl).
Qed.

#[global] Instance MathCompNativeDiagonalLaws :
  @SemanticMeasureDiagonalLaws M (MathCompNodeSemanticMeasure R)
    (MathCompNodeSemanticOmega R).
Proof. constructor; exact @mathcomp_native_bind_diagonal. Qed.
End NativeDiagonal.

Section NativeOmegaAE.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Lemma mathcomp_native_ae_zero {A} (P : A -> Prop) :
  mathcomp_kernel_ae (@mathcomp_kernel_zero R A) P.
Proof.
  apply/negligibleP; first by [].
  change (mathcomp_kernel_root (@mathcomp_kernel_zero R A) (~` mc_predicate P) = 0).
  apply: mathcomp_native_zero_returned => H; exact: H.
Qed.
Lemma mathcomp_native_ae_lub {A} (c : nat -> M A) out (P : A -> Prop) :
  mathcomp_kernel_lub c out ->
  (forall n, mathcomp_kernel_ae (c n) P) -> mathcomp_kernel_ae out P.
Proof.
  move=> Hl Hae; apply/negligibleP; first by [].
  change (mathcomp_kernel_root out (~` mc_predicate P) = 0).
  have Hb : ~ (~` mc_predicate P) MCBottom by move=> H; exact: H.
  have Hm : measurable (~` mc_predicate P) by [].
  rewrite (Hl _ Hm Hb); apply/eqP; rewrite eq_le; apply/andP; split.
  - apply: ub_ereal_sup => _ [n _ <-].
    by rewrite (measure_negligible Hm (Hae n)).
  - apply: ereal_sup_ge; exists (mathcomp_kernel_root (c 0%N) (~` mc_predicate P));
      [by exists 0%N|exact: measure_ge0].
Qed.
#[global] Instance MathCompNativeOmegaAELaws :
  @SemanticOmegaAELaws M (MathCompNodeSemanticMeasure R) (MathCompNodeSemanticOmega R).
Proof. constructor; [exact @mathcomp_native_ae_zero|exact @mathcomp_native_ae_lub]. Qed.
End NativeOmegaAE.

Lemma mathcomp_native_lub_cofinal (R : realType) {A}
    (c d : nat -> MathCompKernelMeasure R A) out :
  (forall n, exists m, mathcomp_node_le (c n) (d m)) ->
  (forall n, exists m, mathcomp_node_le (d n) (c m)) ->
  (mathcomp_kernel_lub c out <-> mathcomp_kernel_lub d out).
Proof.
  move=> Hcd Hdc.
  have He U (mU : measurable U) (Hb : ~ U MCBottom) :
    ereal_sup [set mathcomp_kernel_root (c n) U | n in setT] =
    ereal_sup [set mathcomp_kernel_root (d n) U | n in setT].
  { apply/eqP; rewrite eq_le; apply/andP; split;
      apply: ub_ereal_sup => _ [n _ <-].
    - have [m Hm] := Hcd n; apply: ereal_sup_ge.
      exists (mathcomp_kernel_root (d m) U); [by exists m|exact: Hm].
    - have [m Hm] := Hdc n; apply: ereal_sup_ge.
      exists (mathcomp_kernel_root (c m) U); [by exists m|exact: Hm]. }
  split=> Hl U mU Hb; [rewrite -(He U mU Hb)|rewrite (He U mU Hb)]; exact: Hl.
Qed.
