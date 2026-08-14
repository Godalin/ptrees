Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import List Arith.PeanoNat FunctionalExtensionality Lia.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC FrontierLiftEnum TwoLevelMeasure
  TwoLevelMeasureEnum FreeOmegaMeasure.
From PTree.Eq Require Import ShallowNew UnifiedFrontier
  OperationalProbabilisticPTS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FreeOmegaOperationalCofinality.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.

Local Notation MF := (FreeOmega MN).

Lemma free_operational_hitting_mono {R} (ot : ptree' E MN R) n m :
  Peano.le n m ->
  free_omega_approx eq
    (operational_hitting_approx (MF := MF) n ot)
    (operational_hitting_approx (MF := MF) m ot).
Proof.
  apply (operational_hitting_mono
    (FI := FreeOmegaObservableSemanticMeasureInterface)
    (FO := FreeOmegaObservableSemanticOmegaInterface)
    (MX := FreeOmegaMixedMeasureInterface)).
Qed.

Lemma free_operational_bind_diagonal_mono {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) n m :
  Peano.le n m ->
  free_omega_approx eq
    (operational_bind_diagonal_approx (MF := MF) n t k)
    (operational_bind_diagonal_approx (MF := MF) m t k).
Proof.
  apply (operational_bind_diagonal_mono
    (FI := FreeOmegaObservableSemanticMeasureInterface)
    (FO := FreeOmegaObservableSemanticOmegaInterface)
    (MX := FreeOmegaMixedMeasureInterface)).
Qed.

(** A concrete, finite obligation replacing the abstract Bind lub equality:
    every global-fuel approximant is contained in some diagonal approximant,
    and conversely. *)
Definition free_operational_bind_approx_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) : Prop :=
  free_omega_chains_cofinal eq
    (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.bind t k)))
    (fun fuel => operational_bind_diagonal_approx (MF := MF) fuel t k).

Theorem free_operational_bind_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal t k ->
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R t k.
Proof.
  intros Hcofinal out. unfold operational_bind_cofinal.
  apply free_omega_cofinal_lub_iff. exact Hcofinal.
Qed.

Lemma free_operational_bind_ret_approx_cofinal {A R}
    (a : A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal (Ret a) k.
Proof.
  split; intro n; exists n;
    unfold free_operational_bind_approx_cofinal,
      operational_bind_diagonal_approx,
      operational_head_bind_approx,
      operational_hitting_approx, operational_kernel;
    cbn.
  all: rewrite !operational_target_stableE; cbn.
  all: apply free_omega_approx_refl; intros x; reflexivity.
Qed.

Corollary free_operational_bind_ret_cofinal {A R}
    (a : A) (k : A -> ptree E MN R) :
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R (Ret a) k.
Proof.
  apply free_operational_bind_cofinal.
  apply free_operational_bind_ret_approx_cofinal.
Qed.

Lemma free_operational_bind_vis_approx_cofinal {A R X}
    (e : E X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal (Vis e c) k.
Proof.
  split; intro n; exists n;
    unfold free_operational_bind_approx_cofinal,
      operational_bind_diagonal_approx,
      operational_head_bind_approx,
      operational_hitting_approx, operational_kernel;
    cbn.
  all: rewrite !operational_target_stableE; cbn.
  all: apply free_omega_approx_refl; intros x; reflexivity.
Qed.

Corollary free_operational_bind_vis_cofinal {A R X}
    (e : E X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) :
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R (Vis e c) k.
Proof.
  apply free_operational_bind_cofinal.
  apply free_operational_bind_vis_approx_cofinal.
Qed.

Lemma free_operational_bind_tau_diagonal_left {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) n :
  free_omega_approx eq
    (operational_bind_diagonal_approx (MF := MF) n t k)
    (operational_bind_diagonal_approx (MF := MF)
      (Datatypes.S n) (Tau t) k).
Proof.
  change (free_omega_approx eq
    (free_omega_bind
      (operational_hitting_approx (MF := MF) n (observe t))
      (operational_head_bind_approx (MF := MF) n k))
    (free_omega_bind
      (operational_hitting_approx (MF := MF) n (observe t))
      (operational_head_bind_approx (MF := MF) (Datatypes.S n) k))).
  eapply free_omega_approx_bind with (R := eq) (T := eq).
  - apply free_omega_approx_refl. intros x. reflexivity.
  - intros h1 h2 ->. destruct h2 as [a|X e c];
      cbn [operational_head_bind_approx].
    + apply free_operational_hitting_mono.
      apply le_S. apply le_n.
    + apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma free_operational_bind_tau_diagonal_right {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) n :
  free_omega_approx eq
    (operational_bind_diagonal_approx (MF := MF)
      (Datatypes.S n) (Tau t) k)
    (operational_bind_diagonal_approx (MF := MF)
      (Datatypes.S n) t k).
Proof.
  change (free_omega_approx eq
    (free_omega_bind
      (operational_hitting_approx (MF := MF) n (observe t))
      (operational_head_bind_approx (MF := MF) (Datatypes.S n) k))
    (free_omega_bind
      (operational_hitting_approx (MF := MF) (Datatypes.S n) (observe t))
      (operational_head_bind_approx (MF := MF) (Datatypes.S n) k))).
  eapply free_omega_approx_bind with (R := eq) (T := eq).
  - apply free_operational_hitting_mono.
    apply le_S. apply le_n.
  - intros h1 h2 ->. apply free_omega_approx_refl.
    intros x. reflexivity.
Qed.

Lemma free_operational_bind_tau_approx_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal t k ->
  free_operational_bind_approx_cofinal (Tau t) k.
Proof.
  intros [Hglobal Hdiagonal]. split.
  - intros [|n].
    + exists 0. unfold operational_bind_diagonal_approx,
        operational_hitting_approx, operational_kernel. cbn.
      apply free_omega_approx_refl. intros x. reflexivity.
    + destruct (Hglobal n) as [m Hm]. exists (Datatypes.S m).
      rewrite observe_bind. cbn [operational_hitting_approx operational_kernel].
      eapply free_omega_approx_trans; [exact Hm|].
      apply free_operational_bind_tau_diagonal_left.
  - intros [|m].
    + exists 0. unfold operational_bind_diagonal_approx,
        operational_hitting_approx, operational_kernel. cbn.
      apply free_omega_approx_refl. intros x. reflexivity.
    + destruct (Hdiagonal (Datatypes.S m)) as [n Hn].
      exists (Datatypes.S n).
      change (free_omega_approx (fun y x => x = y)
        (operational_bind_diagonal_approx (MF := MF)
          (Datatypes.S m) (Tau t) k)
        (operational_hitting_approx (MF := MF) n
          (observe (PTree.bind t k)))).
      eapply free_omega_approx_mono with (R := eq).
      * intros x y Hxy. symmetry. exact Hxy.
      * eapply free_omega_approx_trans.
        -- apply free_operational_bind_tau_diagonal_right.
        -- eapply free_omega_approx_mono; [|exact Hn].
           intros x y Hyx. symmetry. exact Hyx.
Qed.

Corollary free_operational_bind_tau_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal t k ->
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R (Tau t) k.
Proof.
  intro Hcofinal. apply free_operational_bind_cofinal.
  exact (free_operational_bind_tau_approx_cofinal Hcofinal).
Qed.

(** Prob requires a genuinely stronger productivity condition than pointwise
    branch cofinality: each outer approximant needs one fuel bound that works
    almost everywhere for the sampled branches.  Finite Enum support can
    obtain such a bound by taking a maximum; arbitrary measures must provide
    it analytically. *)
Definition free_operational_bind_prob_uniform {A R X}
    (mu : MN X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) : Prop :=
  (forall n, exists m Good,
      sem_ae mu Good /\
      forall x, Good x -> free_omega_approx eq
        (operational_hitting_approx (MF := MF) n
          (observe (PTree.bind (c x) k)))
        (operational_bind_diagonal_approx (MF := MF) m (c x) k)) /\
  (forall m, exists n Good,
      sem_ae mu Good /\
      forall x, Good x -> free_omega_approx eq
        (operational_bind_diagonal_approx (MF := MF) m (c x) k)
        (operational_hitting_approx (MF := MF) n
          (observe (PTree.bind (c x) k)))).

Lemma free_operational_bind_prob_approx_cofinal {A R X}
    (mu : MN X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_prob_uniform mu c k ->
  free_operational_bind_approx_cofinal (Prob mu c) k.
Proof.
  intros [Hglobal Hdiagonal]. split.
  - intros [|n].
    + exists 0. unfold operational_bind_diagonal_approx,
        operational_hitting_approx, operational_kernel. cbn.
      apply free_omega_approx_refl. intros x. reflexivity.
    + destruct (Hglobal n) as [m [Good [Hae Hbranches]]].
      exists (Datatypes.S m).
      rewrite observe_bind. cbn [operational_hitting_approx operational_kernel].
      eapply FOApproxSample with
        (S := fun x y => x = y /\ Good x).
      * apply sem_lift_refl_ae. exact Hae.
      * intros x y [-> Hgood].
        eapply free_omega_approx_trans.
        -- exact (Hbranches y Hgood).
        -- apply free_operational_bind_tau_diagonal_left.
  - intros [|m].
    + exists 0. unfold operational_bind_diagonal_approx,
        operational_hitting_approx, operational_kernel. cbn.
      apply free_omega_approx_refl. intros x. reflexivity.
    + destruct (Hdiagonal (Datatypes.S m))
        as [n [Good [Hae Hbranches]]].
      exists (Datatypes.S n).
      rewrite observe_bind. cbn [operational_hitting_approx operational_kernel].
      eapply free_omega_approx_mono with (R := eq).
      * intros x y Hxy. symmetry. exact Hxy.
      * eapply FOApproxSample with
          (S := fun x y => x = y /\ Good x).
        -- apply sem_lift_refl_ae. exact Hae.
        -- intros x y [-> Hgood].
           eapply free_omega_approx_trans.
           ++ apply free_operational_bind_tau_diagonal_right.
           ++ exact (Hbranches y Hgood).
Qed.

Corollary free_operational_bind_prob_cofinal {A R X}
    (mu : MN X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_prob_uniform mu c k ->
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R (Prob mu c) k.
Proof.
  intro Huniform. apply free_operational_bind_cofinal.
  exact (free_operational_bind_prob_approx_cofinal Huniform).
Qed.

(** The analogous finite obligation for iteration rounds.  This is where
    bounded cost/productivity proofs for concrete samplers belong. *)
Definition free_operational_iter_approx_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) : Prop :=
  free_omega_chains_cofinal eq
    (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.iter step i)))
    (fun rounds => operational_iter_round_approx (MF := MF)
      rounds transition i).

(** Finite, proof-relevant productivity data.  A certificate does more than
    assert equality of two omega limits: it exhibits how much structured
    round fuel is sufficient for each operational fuel, and conversely.
    For nested samplers these schedules are where uniform/AE-uniform bounds
    must be supplied; the generic omega theory does not invent them. *)
Record free_operational_iter_productivity_certificate {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) := {
  operational_to_round_schedule : nat -> nat;
  round_to_operational_schedule : nat -> nat;
  operational_to_round_sound : forall fuel,
    free_omega_approx eq
      (operational_hitting_approx (MF := MF) fuel
        (observe (PTree.iter step i)))
      (operational_iter_round_approx (MF := MF)
        (operational_to_round_schedule fuel) transition i);
  round_to_operational_sound : forall rounds,
    free_omega_approx (fun y x => x = y)
      (operational_iter_round_approx (MF := MF) rounds transition i)
      (operational_hitting_approx (MF := MF)
        (round_to_operational_schedule rounds)
        (observe (PTree.iter step i)))
}.

Lemma free_operational_iter_certificate_approx_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) :
  free_operational_iter_productivity_certificate step transition i ->
  free_operational_iter_approx_cofinal step transition i.
Proof.
  intros cert. split.
  - intro fuel. exists (operational_to_round_schedule cert fuel).
    exact (operational_to_round_sound cert fuel).
  - intro rounds. exists (round_to_operational_schedule cert rounds).
    exact (round_to_operational_sound cert rounds).
Qed.

Corollary free_operational_iter_certificate_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) :
  free_operational_iter_productivity_certificate step transition i ->
  @operational_iter_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface I R step transition i.
Proof.
  intros cert out. unfold operational_iter_cofinal.
  apply free_omega_cofinal_lub_iff.
  exact (free_operational_iter_certificate_approx_cofinal cert).
Qed.

(** A primitive Markov step has a uniform syntactic cost: one probabilistic
    node followed by the silent back-edge inserted by [PTree.iter].  Hence
    its global stable-hitting chain and its absorbing-round chain are
    cofinal.  This theorem is entirely operational; no frontier derivation
    or iteration constructor occurs in its assumptions. *)
Section PrimitiveProbIteration.
Context {I R : Type} (transition : I -> MN (I + R)).

Definition free_primitive_iter_step (i : I) : ptree E MN (I + R) :=
  Prob (transition i) (fun next => Ret next).

Definition free_primitive_iter_program (i : I) : ptree E MN R :=
  PTree.iter free_primitive_iter_step i.

Definition free_primitive_iter_hitting (fuel : nat) (i : I) :
    MF (frontier_head E MN R) :=
  operational_hitting_approx (MF := MF) fuel
    (observe (free_primitive_iter_program i)).

Definition free_primitive_iter_rounds (rounds : nat) (i : I) :
    MF (frontier_head E MN R) :=
  operational_iter_round_approx (MF := MF) rounds transition i.

Definition free_primitive_iter_after (next : I + R) : ptree E MN R :=
  match next with
  | inl j => Tau (free_primitive_iter_program j)
  | inr r => Ret r
  end.

Definition free_primitive_iter_cont (next : I + R) : ptree E MN R :=
  PTree.bind (Ret next) (fun lr =>
    match lr with
    | inl j => Tau (free_primitive_iter_program j)
    | inr r => Ret r
    end).

Lemma free_primitive_iter_observe i :
  observe (free_primitive_iter_program i) =
  ProbF (transition i) free_primitive_iter_cont.
Proof.
  unfold free_primitive_iter_program.
  pose proof (unfold_aloop_ free_primitive_iter_step i) as Hunfold.
  rewrite (observing_observe Hunfold), observe_bind.
  assert (Hstep : observe (free_primitive_iter_step i) =
    ProbF (transition i) (fun next => Ret next)) by reflexivity.
  rewrite Hstep. reflexivity.
Qed.

Lemma free_primitive_iter_cont_observe next :
  observe (free_primitive_iter_cont next) =
  observe (free_primitive_iter_after next).
Proof.
  unfold free_primitive_iter_cont. rewrite observe_bind.
  destruct next as [j|r]; reflexivity.
Qed.

Lemma free_primitive_iter_rounds_zero i :
  free_primitive_iter_rounds 0 i = FOZero.
Proof. reflexivity. Qed.

Lemma free_primitive_iter_rounds_succ rounds i :
  free_primitive_iter_rounds (Datatypes.S rounds) i =
  FOSample (transition i) (fun next =>
    match next with
    | inl j => free_primitive_iter_rounds rounds j
    | inr r => FORet (FHRet r)
    end).
Proof.
  unfold free_primitive_iter_rounds, operational_iter_round_approx.
  cbv [mixed_iter_approx sem_bind mixed_bind sem_ret free_omega_bind
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticMeasureInterface
    FreeOmegaSemanticMeasureInterface].
  f_equal. apply functional_extensionality. intros [j|r]; reflexivity.
Qed.

Lemma free_primitive_iter_hitting_succ fuel i :
  free_primitive_iter_hitting (Datatypes.S fuel) i =
  FOSample (transition i) (fun next =>
    operational_hitting_approx (MF := MF) fuel
      (observe (free_primitive_iter_cont next))).
Proof.
  unfold free_primitive_iter_hitting. rewrite free_primitive_iter_observe.
  reflexivity.
Qed.

Lemma free_primitive_iter_retry_zero j :
  operational_hitting_approx (MF := MF) 0
    (observe (free_primitive_iter_cont (inl j))) = FOZero.
Proof. reflexivity. Qed.

Lemma free_primitive_iter_retry_succ fuel j :
  operational_hitting_approx (MF := MF) (Datatypes.S fuel)
    (observe (free_primitive_iter_cont (inl j))) =
  free_primitive_iter_hitting fuel j.
Proof.
  rewrite free_primitive_iter_cont_observe. reflexivity.
Qed.

Lemma free_primitive_iter_success fuel r :
  operational_hitting_approx (MF := MF) fuel
    (observe (free_primitive_iter_cont (inr r))) = FORet (FHRet r).
Proof.
  rewrite free_primitive_iter_cont_observe.
  unfold free_primitive_iter_after, operational_hitting_approx,
    operational_kernel. cbn. rewrite operational_target_stableE.
  reflexivity.
Qed.

Lemma free_primitive_iter_hitting_le_round fuel :
  forall i, free_omega_approx eq
    (free_primitive_iter_hitting fuel i)
    (free_primitive_iter_rounds (Datatypes.S fuel) i).
Proof.
  induction fuel as [|fuel IH]; intro i.
  - rewrite free_primitive_iter_rounds_succ.
    unfold free_primitive_iter_hitting. rewrite free_primitive_iter_observe.
    unfold operational_hitting_approx, operational_kernel. cbn.
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. destruct y as [j|r]; constructor.
  - rewrite free_primitive_iter_hitting_succ,
      free_primitive_iter_rounds_succ.
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. destruct y as [j|r].
      * eapply free_omega_approx_trans with
          (nu := free_primitive_iter_hitting fuel j).
        -- destruct fuel as [|fuel].
           ++ constructor.
           ++ rewrite free_primitive_iter_retry_succ.
              apply free_operational_hitting_mono.
              apply le_S. apply le_n.
        -- apply IH.
      * rewrite free_primitive_iter_success.
        apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma free_primitive_iter_round_le_hitting rounds :
  forall i, free_omega_approx eq
    (free_primitive_iter_rounds rounds i)
    (free_primitive_iter_hitting (2 * rounds) i).
Proof.
  induction rounds as [|rounds IH]; intro i.
  - rewrite free_primitive_iter_rounds_zero. constructor.
  - rewrite free_primitive_iter_rounds_succ.
    replace (2 * Datatypes.S rounds) with
      (Datatypes.S (Datatypes.S (2 * rounds))) by lia.
    rewrite free_primitive_iter_hitting_succ.
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. destruct y as [j|r].
      * rewrite free_primitive_iter_retry_succ. apply IH.
      * rewrite free_primitive_iter_success.
        apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Theorem free_primitive_iter_productivity i :
  free_operational_iter_productivity_certificate
    free_primitive_iter_step transition i.
Proof.
  refine {| operational_to_round_schedule := Datatypes.S;
    round_to_operational_schedule := fun rounds => 2 * rounds |}.
  - intro fuel. exact (free_primitive_iter_hitting_le_round fuel i).
  - intro rounds. eapply free_omega_approx_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + exact (free_primitive_iter_round_le_hitting rounds i).
Qed.

Corollary free_primitive_iter_approx_cofinal i :
  free_operational_iter_approx_cofinal
    free_primitive_iter_step transition i.
Proof.
  apply free_operational_iter_certificate_approx_cofinal.
  exact (free_primitive_iter_productivity i).
Qed.

Corollary free_primitive_iter_cofinal i :
  @operational_iter_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface I R
    free_primitive_iter_step transition i.
Proof.
  apply free_operational_iter_certificate_cofinal.
  exact (free_primitive_iter_productivity i).
Qed.

End PrimitiveProbIteration.

Theorem free_operational_iter_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) :
  free_operational_iter_approx_cofinal step transition i ->
  @operational_iter_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface I R step transition i.
Proof.
  intros Hcofinal out. unfold operational_iter_cofinal.
  apply free_omega_cofinal_lub_iff. exact Hcofinal.
Qed.

End FreeOmegaOperationalCofinality.

Section EnumOperationalCofinality.
Import Enum.
Context {E : Type -> Type}.

Lemma enum_uniform_nat_bound {X} (mu : Enum X) (P : X -> nat -> Prop) :
  (forall x, exists n, P x n) ->
  (forall x n m, Peano.le n m -> P x n -> P x m) ->
  exists n, forall p x, List.In (p, x) mu -> P x n.
Proof.
  intros Hex Hmono. induction mu as [|[p x] mu IH].
  - exists 0. intros q y Hin. inversion Hin.
  - destruct (Hex x) as [nx Hx].
    destruct IH as [nt Htail].
    exists (Nat.max nx nt). intros q y [Hhead|Hin].
    + inversion Hhead; subst. eapply Hmono; [apply Nat.le_max_l|exact Hx].
    + eapply Hmono; [apply Nat.le_max_r|exact (Htail _ _ Hin)].
Qed.

Theorem enum_free_operational_bind_prob_uniform {A R X}
    (mu : Enum X) (c : X -> ptree E Enum A)
    (k : A -> ptree E Enum R) :
  (forall x, free_operational_bind_approx_cofinal (c x) k) ->
  free_operational_bind_prob_uniform mu c k.
Proof.
  intro Hbranches. split.
  - intro fuel.
    destruct (enum_uniform_nat_bound mu
      (P := fun x bound => free_omega_approx eq
        (operational_hitting_approx (MF := FreeOmega Enum) fuel
          (observe (PTree.bind (c x) k)))
        (operational_bind_diagonal_approx (MF := FreeOmega Enum)
          bound (c x) k))) as [bound Hbound].
    + intro x. exact (proj1 (Hbranches x) fuel).
    + intros x n m Hnm Happrox.
      eapply free_omega_approx_trans; [exact Happrox|].
      apply free_operational_bind_diagonal_mono. exact Hnm.
    + exists bound,
        (fun x => free_omega_approx eq
          (operational_hitting_approx (MF := FreeOmega Enum) fuel
            (observe (PTree.bind (c x) k)))
          (operational_bind_diagonal_approx (MF := FreeOmega Enum)
            bound (c x) k)).
      split.
      * intros p x Hin _. exact (Hbound p x Hin).
      * intros x Hx. exact Hx.
  - intro fuel.
    destruct (enum_uniform_nat_bound mu
      (P := fun x bound => free_omega_approx eq
        (operational_bind_diagonal_approx (MF := FreeOmega Enum)
          fuel (c x) k)
        (operational_hitting_approx (MF := FreeOmega Enum) bound
          (observe (PTree.bind (c x) k))))) as [bound Hbound].
    + intro x. destruct (proj2 (Hbranches x) fuel) as [n Hn].
      exists n. eapply free_omega_approx_mono; [|exact Hn].
      intros a b Hba. symmetry. exact Hba.
    + intros x n m Hnm Happrox.
      eapply free_omega_approx_trans; [exact Happrox|].
      apply free_operational_hitting_mono. exact Hnm.
    + exists bound,
        (fun x => free_omega_approx eq
          (operational_bind_diagonal_approx (MF := FreeOmega Enum)
            fuel (c x) k)
          (operational_hitting_approx (MF := FreeOmega Enum) bound
            (observe (PTree.bind (c x) k)))).
      split.
      * intros p x Hin _. exact (Hbound p x Hin).
      * intros x Hx. exact Hx.
Qed.

Corollary enum_free_operational_bind_prob_approx_cofinal {A R X}
    (mu : Enum X) (c : X -> ptree E Enum A)
    (k : A -> ptree E Enum R) :
  (forall x, free_operational_bind_approx_cofinal (c x) k) ->
  free_operational_bind_approx_cofinal (Prob mu c) k.
Proof.
  intro Hbranches. apply free_operational_bind_prob_approx_cofinal.
  exact (enum_free_operational_bind_prob_uniform
    mu (c := c) (k := k) Hbranches).
Qed.

End EnumOperationalCofinality.
