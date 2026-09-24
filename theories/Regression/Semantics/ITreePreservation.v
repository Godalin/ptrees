(** Source weak proofs, including infinite interaction/divergence, feed the
    actual lowering. Source interp squares are not target postcomposition. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms.
From Paco Require Import paco.
From mathcomp Require Import reals.
From ITree.Core Require Import ITreeDefinition KTreeFacts.
From ITree.Eq Require Import Eqit UpToTaus Paco2.
From ITree.Interp Require Import Interp.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition ITreeBridge.
From PTree.Interp Require Import ITreeEutt ITreeSourceInterp ITreePreservation.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.Backend.MathComp.Direct.mathcomp_direct_peutt.

From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ SubEnumR.
From PTree.Interp.FreeOmega Require Import ITreePreservation ITreeCompletion.
Set Implicit Arguments.

Variant questionE : Type -> Type := Question : questionE bool.

CoFixpoint source_service : itree questionE unit :=
  ITreeDefinition.Vis Question (fun _ => ITreeDefinition.Tau source_service).
CoFixpoint delayed_service : itree questionE unit :=
  ITreeDefinition.Tau (ITreeDefinition.Vis Question
    (fun _ => ITreeDefinition.Tau (ITreeDefinition.Tau delayed_service))).

Lemma service_source_eutt : eutt eq source_service delayed_service.
Proof.
  einit. ecofix CIH.
  rewrite (itree_eta source_service), (itree_eta delayed_service).
  unfold ITreeDefinition.observe. cbn. setoid_rewrite tau_euttge. evis. intro b.
  repeat setoid_rewrite tau_eutt. ebase.
Qed.

Example embedded_infinite_service :
  @from_itree questionE SubEnumQ unit source_service ≈ₚ from_itree delayed_service.
Proof. apply free_omega_from_itree_eutt. exact service_source_eutt. Qed.

Example embedded_heterogeneous_return :
  @from_itree questionE SubEnumQ bool
    (ITreeDefinition.Tau (ITreeDefinition.Tau (ITreeDefinition.Ret true)))
  ≈ₚ[ fun (b : bool) (n : nat) => n = if b then 1 else 0 ]
  from_itree (ITreeDefinition.Tau (ITreeDefinition.Ret 1)).
Proof.
  apply free_omega_from_itree_eutt. repeat setoid_rewrite tau_eutt.
  apply eqit_Ret. reflexivity.
Qed.

Example embedded_divergence :
  @from_itree questionE SubEnumQ bool ITree.spin ≈ₚ
    from_itree (ITreeDefinition.Tau ITree.spin).
Proof. apply free_omega_from_itree_eutt. symmetry. apply tau_eutt. Qed.

Example divergence_has_no_head n :
  @itree_head_at questionE SubEnumQ bool n (ITreeDefinition.observe ITree.spin) = None.
Proof. induction n; cbn; auto. Qed.

Example source_divergence_not_return :
  ~ eutt eq (@ITree.spin questionE bool) (ITreeDefinition.Ret true).
Proof. intro H. exact (eutt_spin_Ret_abs _ H). Qed.

Definition returning_source_handler X (e : questionE X) : itree questionE X :=
  match e with Question => ITreeDefinition.Ret true end.
Definition divergent_source_handler X (e : questionE X) : itree questionE X :=
  match e with Question => ITree.spin end.
Definition two_query_source_handler X (e : questionE X) : itree questionE X :=
  match e with Question => ITreeDefinition.Vis Question (fun _ =>
    ITreeDefinition.Vis Question (fun x => ITreeDefinition.Ret x)) end.

Example returning_source_square :
  @from_itree questionE SubEnumQ unit (Interp.interp returning_source_handler source_service) ≈ₚ
  PTree.interp (fun X e => @from_itree questionE SubEnumQ X (returning_source_handler e))
    (from_itree source_service).
Proof. apply free_omega_from_itree_interp. Qed.

Example divergent_source_square :
  @from_itree questionE SubEnumQ unit (Interp.interp divergent_source_handler source_service) ≈ₚ
  PTree.interp (fun X e => @from_itree questionE SubEnumQ X (divergent_source_handler e))
    (from_itree source_service).
Proof. apply free_omega_from_itree_interp. Qed.

Example two_query_source_square :
  @from_itree questionE SubEnumQ unit (Interp.interp two_query_source_handler source_service) ≈ₚ
  PTree.interp (fun X e => @from_itree questionE SubEnumQ X (two_query_source_handler e))
    (from_itree source_service).
Proof. apply free_omega_from_itree_interp. Qed.

Definition sampling_source_handler (mu : SubEnumQ bool) X (e : questionE X) :
    itree (probE SubEnumQ +' questionE) X :=
  match e with Question => ITree.trigger (inl1 (Sample mu)) end.

Example sampling_source_square (mu : SubEnumQ bool) :
  elaborate (Interp.interp (sampling_source_handler mu) source_service) ≈ₚ
  interp_itree (fun X e => elaborate (sampling_source_handler mu e)) source_service.
Proof. apply free_omega_interp_itree_source_interp. Qed.

Example lowering_partial_source_equation :
  elaborate_closed (ITree.bind (ITree.trigger (Sample (@subenumQ_zero bool)))
    (fun x => ITreeDefinition.Ret x)) ≈ₚ
  elaborate_closed (ITree.trigger (Sample (@subenumQ_zero bool))).
Proof. apply free_omega_elaborate_closed_eutt. apply eq_sub_eutt. apply bind_ret_r. Qed.

Example lowering_heterogeneous {E A B} (RR : A -> B -> Prop)
    (t : itree (probE SubEnumQ +' E) A) (u : itree (probE SubEnumQ +' E) B) :
  eutt RR t u -> elaborate t ≈ₚ[RR] elaborate u.
Proof. apply free_omega_elaborate_eutt. Qed.

Section LocalRewriting.
Context {E : Type -> Type} {A : Type}.
Local Instance lowering_rewrite :
  Proper (eutt eq ==> canonical_peutt eq) (@elaborate SubEnumQ E A).
Proof. intros t u H. apply free_omega_elaborate_eutt. exact H. Qed.
Example lowering_setoid (t u : itree (probE SubEnumQ +' E) A) (H : eutt eq t u) :
  elaborate t ≈ₚ elaborate u.
Proof. setoid_rewrite H. reflexivity. Qed.
End LocalRewriting.

Section RealBackend.
Variable R : realType.
Example real_embedded_service :
  @from_itree questionE (SubEnumR R) unit source_service ≈ₚ from_itree delayed_service.
Proof. apply free_omega_from_itree_eutt. exact service_source_eutt. Qed.
Example real_lowering_eutt {E A B} (RR : A -> B -> Prop)
    (t : itree (probE (SubEnumR R) +' E) A) (u : itree (probE (SubEnumR R) +' E) B) :
  eutt RR t u -> elaborate t ≈ₚ[RR] elaborate u.
Proof. apply free_omega_elaborate_eutt. Qed.
End RealBackend.

Section LargeCarrier.
Universe high.
Constraint Set < high.
Example high_source_eutt (A B : Type@{high}) (RR : A -> B -> Prop)
    (t : itree questionE A) (u : itree questionE B) :
  eutt RR t u -> @from_itree questionE SubEnumQ A t ≈ₚ[RR] from_itree u.
Proof. apply free_omega_from_itree_eutt. Qed.
End LargeCarrier.
