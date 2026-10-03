(** Public interpretation really is the selected-sampling fold, not the
    productive implementation under a second short-name alias. *)
From Coq Require Import Utf8.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree Require Import PTree.

Example public_interp_owner : @interp = @Fold.interp.
Proof. reflexivity. Qed.

Example public_selected_fold {E MN T : Type → Type}
    `{Monad.Monad T} `{Basics.MonadIter T} `{MonadSample MN T}
    (h : ∀ X, E X → T X) {A} (t : ptree E MN A) :
  interp h t = fold h (λ X mu, msample mu) t.
Proof. reflexivity. Qed.

Fail Check PTree.interp.
Fail Check PEutt.peutt.
Fail Check FreeOmega.

From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ.

Example public_agreement {E F A}
    (h : ∀ X, E X → ptree F SubEnumQ X) (t : ptree E SubEnumQ A) :
  interp h t ≈ₚ interp_tree h t.
Proof.
  apply (interp_ptree_agrees RelationalLimit.free_omega_relational_mixed_bind
    RelationalLimit.free_omega_relational_zero RelationalLimit.free_omega_relational_lub).
Qed.

Example public_interp_bind {E F A B}
    (h : ∀ X, E X → ptree F SubEnumQ X)
    (t : ptree E SubEnumQ A) (k : A → ptree E SubEnumQ B) :
  interp h (bind t k) ≈ₚ bind (interp h t) (λ x, interp h (k x)).
Proof.
  apply (interp_ptree_bind RelationalLimit.free_omega_relational_mixed_bind
    RelationalLimit.free_omega_relational_zero RelationalLimit.free_omega_relational_lub).
Qed.

Check interp_state.
Check interp_state_run_state.
Example public_state_sampler {S X F} (mu : SubEnumQ X) (s : S) :
  @msample _ _ (@MonadSample_stateT S SubEnumQ (ptree F SubEnumQ) _ _) X mu s =
    bind (sample mu) (λ x, Ret (s,x)).
Proof. reflexivity. Qed.

Example public_interp_owner_after_facts : @interp = @Fold.interp.
Proof. reflexivity. Qed.
Fail Check PTree.Eq.Backend.MathComp.mathcomp_peutt.
