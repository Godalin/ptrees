# Relational bind congruence

`peutt_bind` now has independent source and result relations and independent
return carriers on both sides:

```coq
forall A B R1 R2 (RR : R1 -> R2 -> Prop) (RS : A -> B -> Prop)
  (t1 : ptree E MN R1) (t2 : ptree E MN R2)
  (k1 : R1 -> ptree E MN A) (k2 : R2 -> ptree E MN B),
  peutt RR t1 t2 ->
  (forall x y, RR x y -> peutt RS (k1 x) (k2 y)) ->
  peutt RS (PTree.bind t1 k1) (PTree.bind t2 k2).
```

Neither relation needs to be reflexive, transitive, symmetric or even
homogeneous. Continuations are behaviorally related, not Coq-equal.

Both `Eq/PEutt.v` and the canonical `Eq/FreeOmega/Bind.v` endpoint use this
statement under the original name. The curated generic facade automatically
exposes the stronger theorem through its existing notation. No `_rel` alias
or duplicate homogeneous theorem was added. Existing `eapply peutt_bind`
calls and homogeneous `Proper`/setoid rewriting specialize `B := A`, `RS := eq`.

## Proof and assumptions

The generic proof uses the already established heterogeneous
`bind_upto_closure_compatible`, instantiated with an empty recursive candidate.
That closure includes known behavioral pairs and binds of related sources
with related continuations. Compatibility makes it a postfixed point; greatest
fixed-point coinduction then gives the result. No induction on computations,
new probability law or equivalence assumption on `RS` is needed.

The generic theorem retains its existing global bind-cofinality premise and
measure capabilities. The FreeOmega corollary discharges cofinality with the
existing `ptree_bind_cofinal_all`, under exactly its previous native capabilities.
The elaborated capability prefixes and logical assumptions do not change.
In particular this work does not claim to remove existing classical choice or
extensionality dependencies. The homogeneous internal candidate remains for
its existing direct-MathComp client; that backend and its trust boundary are
not changed.

## Regression and contract review

`Regression/Semantics/PEuttAlgebra.v` adds:

- `canonical_heterogeneous_bind`: arbitrary event signature, four arbitrary
  carriers and two arbitrary relations, via the FreeOmega public endpoint.
- `eventful_heterogeneous_bind`: a visible query followed by fair sampling;
  the source relation is bool/nat and the result relation is nat/bool. A Tau
  occurs only in the left continuation, so the continuation evidence is weak
  behavioral equivalence rather than structural lockstep or Coq equality.

The existing homogeneous bind/setoid regression remains unchanged.

The compiled-contract refresh is deliberately limited to three entries:
`Eq.PEutt.peutt_bind`, `Eq.FreeOmega.Bind.peutt_bind` and its existing generic
facade alias. The fresh compiled statement, specialized at `B := A, RS := eq`,
must equal the old statement (modulo printing whitespace); assumption output
must be identical. All other 502 entries must be exactly unchanged.

The completed finite-carrier migration's byte-conservation unit test now
checks its frozen final checkpoint `5f6b414` against `1cba6c5`. It still checks
the current native representation/legacy boundary. This preserves the exact
historical migration claim without banning subsequent authorized generic
theory improvements or silently relaxing that migration's equality test.

## Local checks

- Full `opam exec -- dune build`, including AllImports and all old clients.
- All 505 compiled entries queried and compared before updating the three
  reviewed signatures; the other 502 entries and every assumption output match.
- 123 Python unit tests; architecture audit; 306-entry compiled API check.
- Soundness audit: 199 exact contracts, 36 generic validation endpoints,
  18 finite-real realization endpoints and 80 native MathComp endpoints;
  no change to the logical-axiom whitelist or the two-file Gate M policy.
- A joint `coqchk -silent -R _build/default/theories PTree` with separate
  `-norec` arguments for `Eq.PEutt`, `Eq.FreeOmega.Bind`, `Eq.FreeOmega.Algebra`,
  `Regression.Semantics.PEuttAlgebra` and `Interp.FreeOmega.Guarded`.

All checks listed above passed. The kernel check covers those five safe module
bodies with compiled dependencies trusted, not the whole library recursively.
No CI result is claimed and neither Gate M file is modified.
