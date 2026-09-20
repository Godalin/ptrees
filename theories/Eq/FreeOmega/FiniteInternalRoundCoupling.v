Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure FreeOmegaNative.
From PTree.Eq Require Import PStrong FiniteInternalPlan
  UnifiedFrontier PrimitiveStableHitting.
From PTree.Eq.FreeOmega Require Import FiniteInternalNative.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RoundCoupling.
Universes node node_rep frontier.
Context {E : Type -> Type} {MN : Type@{node} -> Type@{node_rep}}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI} {A B : Type}.
Variable RR : A -> B -> Prop.
Variable sim : ptree E MN A -> ptree E MN B -> Prop.
Let treeA : Type@{frontier} := ptree E MN A.
Let treeB : Type@{frontier} := ptree E MN B.

(** Keep small path samples at the frontier level, including intermediate
    bind carriers: their incoming coupling was obtained through high-tree
    decoding/recovery and must not be specialized back to the node level. *)
Local Notation qlift := (@free_omega_qlift@{
  frontier frontier node node node node node node node node node node frontier frontier frontier
  node node node node node_rep node node node node node node node node
  node node node node node node node node node node} MN NI NO _ _).

Definition internal_round_target_rel
    (x : stable_target (ptree E MN A) (stable_head E MN A))
    (y : stable_target (ptree E MN B) (stable_head E MN B)) : Prop :=
  match x, y with
  | SHStable h, SHStable k => stable_head_rel RR sim h k
  | SHInternal t, SHInternal u => sim t u
  | _, _ => False
  end.

(** A matched guard has a NATIVE coupling of its small sample spaces.
    This is constructor inversion of pstrongF, not reflection of an
    arbitrary quotient coupling.  In the Prob case it is precisely the
    node coupling carried by the guard premise. *)
Lemma internal_guard_native_coupled t u :
  (fun t u => pstrongF RR sim (observe t) (observe u)) t u ->
  sem_lift (fun x y => internal_round_target_rel
    (native_sample_value (internal_guard_native t) x)
    (native_sample_value (internal_guard_native u) y))
    (native_sample_measure (internal_guard_native t))
    (native_sample_measure (internal_guard_native u)).
Proof.
  intro Hguard. unfold internal_guard_native in *.
  remember (observe t) as ot in Hguard |- *.
  remember (observe u) as ou in Hguard |- *.
  destruct Hguard; cbn [native_sample_measure native_sample_value internal_round_target_rel].
  - apply sem_lift_ret. constructor. exact H.
  - apply sem_lift_ret. exact H.
  - apply sem_lift_ret. constructor. exact H.
  - exact H.
Qed.

Definition internal_round_path_rel t u
    (p : @finite_internal_plan E MN A t) (q : @finite_internal_plan E MN B u)
    (x : native_sample_type (internal_plan_round_native p))
    (y : native_sample_type (internal_plan_round_native q)) : Prop :=
  internal_round_target_rel
    (native_sample_value (internal_plan_round_native p) x)
    (native_sample_value (internal_plan_round_native q) y).

Arguments internal_round_path_rel {t u} p q x y.

(** Executing the guard retains the original compression path together
    with the guard sample.  Neither cost nor latent randomness is erased.
    Different sides may have different total path costs. *)
Theorem internal_plan_round_paths_coupled t u
    (p : @finite_internal_plan E MN A t) (q : @finite_internal_plan E MN B u) :
  qlift
    (fun x y => (fun t u => pstrongF RR sim (observe t) (observe u)) (internal_plan_residual p x) (internal_plan_residual q y))
    (FOSample (internal_plan_measure p) (fun x => FORet x))
    (FOSample (internal_plan_measure q) (fun y => FORet y)) ->
  qlift (internal_round_path_rel p q)
    (FOSample (native_sample_measure (internal_plan_round_native p)) (fun x => FORet x))
    (FOSample (native_sample_measure (internal_plan_round_native q)) (fun y => FORet y)).
Proof.
  intro Hpaths.
  pose (lk := fun x : internal_plan_path p =>
    FOSample (native_sample_measure (internal_guard_native (internal_plan_residual p x)))
      (fun z => FORet (existT
        (fun x => native_sample_type (internal_guard_native (internal_plan_residual p x))) x z)) :
      FreeOmegaAt MN treeA (native_sample_type (internal_plan_round_native p))).
  pose (left := FOSample (internal_plan_measure p) lk).
  pose (rk := fun y : internal_plan_path q =>
    FOSample (native_sample_measure (internal_guard_native (internal_plan_residual q y)))
      (fun z => FORet (existT
        (fun y => native_sample_type (internal_guard_native (internal_plan_residual q y))) y z)) :
      FreeOmegaAt MN treeB (native_sample_type (internal_plan_round_native q))).
  pose (right := FOSample (internal_plan_measure q) rk).
  assert (Hl : qlift eq left
    (FOSample (native_sample_measure (internal_plan_round_native p)) (fun x => FORet x))).
  { unfold left, lk. eapply FOQLComp with (T := eq) (U := eq).
    - apply free_omega_sample_sigma.
    - eapply FOQLSample with (T := eq); [apply sem_lift_refl; intro x; reflexivity|].
      intros x y ->. destruct y. apply FOQLStructural, FOLRet. reflexivity.
    - intros x z [y [-> ->]]. reflexivity. }
  assert (Hr : qlift eq right
    (FOSample (native_sample_measure (internal_plan_round_native q)) (fun y => FORet y))).
  { unfold right, rk. eapply FOQLComp with (T := eq) (U := eq).
    - apply free_omega_sample_sigma.
    - eapply FOQLSample with (T := eq); [apply sem_lift_refl; intro x; reflexivity|].
      intros x y ->. destruct y. apply FOQLStructural, FOLRet. reflexivity.
    - intros x z [y [-> ->]]. reflexivity. }
  eapply FOQLComp with (T := eq) (U := internal_round_path_rel p q) (mid := left).
  - apply FOQLMono with (T := fun x y => y = x).
    + apply FOQLSym. exact Hl.
    + intros x y Hyx. symmetry. exact Hyx.
  - eapply FOQLComp with (T := internal_round_path_rel p q) (U := eq) (mid := right).
    + change (qlift (internal_round_path_rel p q)
        (free_omega_bind (FOSample (internal_plan_measure p) (fun x => FORet x)) lk)
        (free_omega_bind (FOSample (internal_plan_measure q) (fun y => FORet y)) rk)).
      eapply FOQLBind; [exact Hpaths|].
      intros x y Hguard. eapply FOQLSample; [exact (internal_guard_native_coupled Hguard)|].
      intros gx gy Hxy. apply FOQLStructural, FOLRet. exact Hxy.
    + exact Hr.
    + intros x z [y [Hxy ->]]. exact Hxy.
  - intros x z [y [-> Hyz]]. exact Hyz.
Qed.
End RoundCoupling.

Arguments internal_round_path_rel {E MN NI A B} RR sim {t u} p q x y.
