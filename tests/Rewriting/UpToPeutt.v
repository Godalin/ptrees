(** Generic API checks, not a second case study: actual setoid rewriting
    inside the closure, heterogeneous recursive re-entry, and known closure.
    No native measure laws, countability, totality or external model. *)
From Coq Require Import Utf8 Morphisms.
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Eq Require Import PEutt UpToPeutt.
Set Implicit Arguments.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.

Section Client.
Context {E MN MF : Type → Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.

Example rewrite_both_endpoints {A B}
    (sim : ptree' E MN A → ptree' E MN B → Prop)
    (t t' : ptree E MN A) (u u' : ptree E MN B)
    (Hl : peutt (MF := MF) eq t t') (Hr : peutt (MF := MF) eq u u')
    (Hsim : sim (observe t') (observe u')) :
  peutt_upto_closure (MF := MF) sim (observe t) (observe u).
Proof.
  setoid_rewrite Hl. setoid_rewrite Hr.
  apply peutt_upto_closure_includes. exact Hsim.
Qed.

Example rewrite_then_known {A B} (RR : A → B → Prop)
    (sim : ptree' E MN A → ptree' E MN B → Prop)
    (t t' : ptree E MN A) (u u' : ptree E MN B)
    (Hl : peutt (MF := MF) eq t t') (Hr : peutt (MF := MF) eq u u')
    (Hknown : peutt (MF := MF) RR t' u') :
  peutt_upto_known_closure (MF := MF) RR sim (observe t) (observe u).
Proof.
  setoid_rewrite Hl. setoid_rewrite Hr.
  apply peutt_upto_known_closure_known. exact Hknown.
Qed.

Example pure_closure_empty {A B} (t : ptree E MN A) (u : ptree E MN B) :
  ¬ peutt_upto_closure (MF := MF) (λ _ _, False) (observe t) (observe u).
Proof. intros [x [y [_ [H _]]]]. exact H. Qed.

(** Additional laws below justify only the concrete Tau/Vis equations.
    The up-to rule above itself does not require them. *)
Context `{FB : @SemanticMeasureBindLaws MF FI}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}.
Variable tick : E bool.

CoFixpoint left_service {A} : ptree E MN A :=
  Vis tick (λ _, Tau left_service).
CoFixpoint right_service {B} : ptree E MN B :=
  Vis tick (λ _, Tau (Tau right_service)).

(** The candidate contains only roots. After visible progress, two-sided
    peutt rewriting removes administrative Tau before recursive re-entry. *)
Example heterogeneous_recursive_reentry {A B} (RR : A → B → Prop) :
  peutt (MF := MF) RR (@left_service A) (@right_service B).
Proof.
  eapply peutt_coinduction_upto_peutt with
    (sim := λ s t, s = observe (@left_service A) ∧ t = observe (@right_service B)).
  - intros s t [-> ->]. apply stable_hitting_match_vis. intro answer.
    repeat setoid_rewrite (peutt_tau_l (MF := MF)).
    apply peutt_upto_closure_includes. split; reflexivity.
  - split; reflexivity.
Qed.

CoFixpoint left_query : ptree E MN bool :=
  Vis tick (λ (retry : bool), if retry then Tau left_query else Ret true).
CoFixpoint right_query : ptree E MN nat :=
  Vis tick (λ (retry : bool), if retry then Tau (Tau right_query) else Ret 1).

Example recursive_or_known :
  peutt (MF := MF) (λ b n, b = true ∧ n = 1) left_query right_query.
Proof.
  eapply peutt_coinduction_upto_peutt_known with
    (sim := λ s t, s = observe left_query ∧ t = observe right_query).
  - intros s t [-> ->]. apply stable_hitting_match_vis. intros [].
    + repeat setoid_rewrite (peutt_tau_l (MF := MF)).
      apply peutt_upto_known_closure_includes. split; reflexivity.
    + apply peutt_upto_known_closure_known.
      apply peutt_ret. split; reflexivity.
  - split; reflexivity.
Qed.
End Client.
