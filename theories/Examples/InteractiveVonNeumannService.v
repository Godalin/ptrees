Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import RatSubTypes DiscreteMC TwoLevelMeasureEnum
  FreeOmegaMeasure.
From PTree.Eq Require Import ProbabilisticEutt
  OperationalProbabilisticPTSFreeOmega.
From PTree.Examples Require Import VonNeumannUnbounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.

(** A client requests a fresh bit; the server then publishes its answer.
    Both events return [unit], so the only observable choice is the reply bit. *)
Variant coin_serviceE : Type -> Type :=
  | CoinRequest : coin_serviceE unit
  | CoinReply (b : bool) : coin_serviceE unit.

Definition publish (b : bool) (next : ptree coin_serviceE Enum Empty_set) :
    ptree coin_serviceE Enum Empty_set :=
  Vis (CoinReply b) (fun _ => next).

(** One request is followed by a closed sampler and one visible reply. *)
Definition serve_round (sampler : ptree coin_serviceE Enum bool)
    (next : ptree coin_serviceE Enum Empty_set) :
    ptree coin_serviceE Enum Empty_set :=
  Vis CoinRequest (fun _ =>
    PTree.bind sampler (fun b => publish b next)).

(** The recursive call is guarded by the request [Vis]. *)
CoFixpoint von_neumann_service : ptree coin_serviceE Enum Empty_set :=
  serve_round von_neumann_third_in von_neumann_service.

CoFixpoint direct_fair_service : ptree coin_serviceE Enum Empty_set :=
  serve_round direct_fair_in direct_fair_service.

Local Notation MF := (FreeOmega Enum).

(** One service round is a congruence.  The infinite theorem cannot simply
    invoke this lemma recursively: its [Hnext] premise is exactly the
    coinductive obligation that the final proof candidate must retain. *)
Lemma serve_round_congruence
    (sampler1 sampler2 : ptree coin_serviceE Enum bool)
    (next1 next2 : ptree coin_serviceE Enum Empty_set)
    (Hsampler :
      @probabilistic_eutt coin_serviceE Enum MF
        (FreeOmegaObservableSemanticMeasureInterface
          (NI := Enum_SemanticMeasureInterface)
          (NO := Enum_SemanticOmegaInterface))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface bool bool eq
        sampler1 sampler2)
    (Hnext :
      @probabilistic_eutt coin_serviceE Enum MF
        (FreeOmegaObservableSemanticMeasureInterface
          (NI := Enum_SemanticMeasureInterface)
          (NO := Enum_SemanticOmegaInterface))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface Empty_set Empty_set eq
        next1 next2) :
  @probabilistic_eutt coin_serviceE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface Empty_set Empty_set eq
    (serve_round sampler1 next1) (serve_round sampler2 next2).
Proof.
  unfold serve_round.
  apply probabilistic_eutt_vis. intros [].
  eapply free_probabilistic_eutt_bind.
  - exact Hsampler.
  - intros b1 b2 ->. unfold publish.
    apply probabilistic_eutt_vis. intros []. exact Hnext.
Qed.

Lemma observe_von_neumann_service :
  observe von_neumann_service =
  VisF CoinRequest (fun _ =>
    PTree.bind von_neumann_third_in
      (fun b => publish b von_neumann_service)).
Proof. reflexivity. Qed.

Lemma observe_direct_fair_service :
  observe direct_fair_service =
  VisF CoinRequest (fun _ =>
    PTree.bind direct_fair_in
      (fun b => publish b direct_fair_service)).
Proof. reflexivity. Qed.
