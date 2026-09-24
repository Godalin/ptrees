# Interpretation algebra: maintained scope

This is the current scope map, not a claim that every effect theorem is
generic over arbitrary iteration operators. Existing PTree behavioral
interpretation and independent execution-target folds are separate layers.

## Completed transformer / execution slice

| Effect | Canonical target | Transformer laws | Eliminator/fold agreement |
| --- | --- | --- | --- |
| State | ITree state-first `Monads.stateT S T` | Existing transformer operations | Generic base MonadLawsE + Eq1 equivalence + iteration_uniform (`fold_run_state`) |
| Exception | ExtLib `eitherT Err T` | Monad laws and inherited uniformity | Same generic target requirements (`fold_run_exception`) |
| Reader | ExtLib `readerT Env T` | Monad laws and inherited uniformity | Actual ITree target (`itree_fold_run_reader`) |
| Writer | ITree log-first `Monads.writerT W T` | Explicit append monad, accumulator iterator; MonoidLaws; inherited uniformity | Actual ITree target + MonoidLaws (`itree_fold_run_writer`) |

Reader and Writer now have genuine canonical transformer folds, strong Ret/
bind compatibility in ITree, and agreements with their **unchanged** PTree
eliminators. Writer's bind theorem combines logs by append, rather than only
threading a mutable accumulator. The generic transformer law constructors
and actual-target proofs live in different modules and have different names.

No probability capability or totality premise is needed for these squares:
each compares the same supplied sampling algebra on both routes. In contrast,
correctness of that sampling algebra, or arbitrary-fold peutt preservation,
does require a separate theorem and is not asserted here.

## Relation to the existing behavioral layer

- Generic handler preservation, composition and sum calculus are unchanged.
- State/Reader/Writer/Exception peutt preservation and finite interpreted
  effect algebra are unchanged.
- Native sampling remains Prob, never re-encoded as Vis by these folds.
- Missing mass, divergence and exceptions remain distinct; the half-mass
  sample-before-throw counterexample is retained.
- Arbitrary-return-relation peutt bind and canonical routing are unchanged.

See [handler calculus](HANDLER_CALCULUS.md),
[finite effect algebra](EFFECT_ALGEBRA.md),
[ExceptT](EXCEPTION_FOLD.md), and [ReaderT/WriterT](READER_WRITER_FOLD.md).

## Completed source ITree bridge

The subsequent [source-preservation increment](ITREE_PRESERVATION.md) proves
heterogeneous `eutt RR -> peutt RR` for `from_itree` and probability lowering,
plus the genuine source-`ITree.interp` commuting square. It handles returning,
diverging and multi-event source handlers, without changing either interpreter.
The base embedding uses an explicit classical convergence/divergence split;
its compiled probability requirements are weaker than unrestricted interp's.
These are no longer open source-bridge obligations.

## Deliberately not claimed

1. **Arbitrary-target Reader/Writer commuting.** Existing interp-based
   eliminators insert administrative Tau, unlike direct State/Exception.
   Their ITree proofs use checked weak coinduction. A future arbitrary-target
   theorem must derive the needed finite-stuttering laws from an appropriate
   lawful iteration structure (for example a suitable Elgot-law profile).
   Bare MonadIter supplies no such law; this work neither assumes the
   desired commuting conclusion nor adds a theorem-level capability class.
2. **Full iteration-law inheritance.** The new proofs establish uniformity,
   not a blanket assertion of every Conway/Elgot axiom for every transformer.
3. **Arbitrary eventful behavioral iteration congruence.** The source ITree
   obligations are now proved, but the independent PTree iteration theorem
   still carries its explicit generator-closure requirement.
4. **Additional effect interfaces.** New public local/catch operations,
   arbitrary effect-order interchange, and generic totality-conditioned
   sample erasure are not added. No synthetic Local/Catch event is introduced.
5. **Automatic public re-export.** New transformer/fold modules are opt-in;
   facade selection can follow actual client needs, without export-order
   shadowing or competing global instances.

This is a stable executable interpretation-algebra checkpoint. The open
items above are explicit mathematical/API extensions, not hidden premises
in the completed theorems. No further directory or probability-interface
reorganization is needed to use the completed slice.
