(** Real-weight sampling plus persistent visible interaction is a client of
    the same generic two-handler proof, not a backend-specific induction. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import reals.
From PTree Require Import PTree PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumR.
Set Implicit Arguments.

Variant sourceE : Type -> Type := Sample : sourceE bool.
Variant targetE : Type -> Type := Emit : bool -> targetE unit.

Section RealClient.
Variable R : realType.
Variable mu : SubEnumR R bool.
Definition sampling X (e : sourceE X) : ptree targetE (SubEnumR R) X :=
  match e with
  | Sample => Prob mu (fun b => Vis (Emit b) (fun _ => Ret b))
  end.
Definition sampling_delay X (e : sourceE X) : ptree targetE (SubEnumR R) X :=
  Tau (sampling e).

CoFixpoint service : ptree sourceE (SubEnumR R) unit :=
  Vis Sample (fun _ => service).

Example real_sampling_handler_rel X (e : sourceE X) :
  sampling e ≈ₚ sampling_delay e.
Proof. apply peutt_tau_r. Qed.

Example real_infinite_sampling :
  interp sampling service ≈ₚ interp sampling_delay service.
Proof.
  eapply free_omega_peutt_interp_handler_rel.
  - intros X e. apply real_sampling_handler_rel.
  - apply peutt_refl.
Qed.

Example real_handler_bind_client :
  bind (interp sampling service) (fun _ => Ret true) ≈ₚ
  bind (interp sampling_delay service) (fun _ => Ret true).
Proof.
  eapply peutt_bind with (RR := eq).
  - apply real_infinite_sampling.
  - intros x y ->. apply peutt_refl.
Qed.

Example real_right_identity :
  Handler.cat sampling Handler.id_ Sample ≈ₚ sampling Sample.
Proof. apply free_omega_handler_cat_id_r. Qed.
End RealClient.

Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.Backend.MathComp.Direct.MathComp_CanonicalBehavior.

