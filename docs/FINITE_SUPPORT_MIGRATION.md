# Ordinary-scalar support obligations

Baseline: `f9485be`. Overall rational carrier migration remains open.

This increment handles a specific obligation of removing scalar subtypes:
positive-support facts need the **container** nonnegativity certificate.
`Common/FiniteSupport.v` proves indicator support, atom positivity/zero
characterizations and the bound of a nonnegative entry by its expectation.
The scalars are arbitrary `numDomainType`; indicator results do not require
equality on values. There are no new classes, semantic relations or axioms.

The forward implication from positive indicator expectation to a nonzero
selected entry does not need nonnegativity. Its converse, and zero atom mass
implying every matching coefficient is zero, explicitly require it. The
regression demonstrates why: weights `+1` and `-1` at the same value cancel
but are not a nonnegative container. It also checks rat, realType, function
carriers, duplicates/zeros and a large-universe carrier.

Production reuse is one proof: `SubEnumR/Coupling.real_enum_expect_entry_le`
now invokes the shared theorem. Its statement and all coupling constructions
are unchanged. `audit_finite_support.py` exactly reconstructs that edit and
freezes every other old theory file and compiled snapshot (apart from the
two aggregate imports and regression registration).
The historical Phase 3 client-replay unit test is pinned to its accepted
`683d3c7` source; the Phase 3 audit itself is unchanged. Its old exact edit
cannot be a perpetual ban on later audited proof deduplication. The current
client is instead locked to the one-line delegation by this increment's gate.

This is not a carrier switch, does not make negative weightings legal, and
does not change FreeOmega, native interfaces or the MathComp trust boundary.
The support obligations are ready to be consumed when the ordinary-rational
production representation is installed.

Validation commands:

```sh
opam exec -- dune build
python3 -m unittest discover -s tools -p 'test_*.py'
opam exec -- python3 tools/audit_finite_support.py
python3 tools/audit_architecture.py --check
opam exec -- python3 tools/audit_assumptions.py --check
opam exec -- python3 tools/audit_soundness.py --check
```

Targeted `coqchk -norec` checks the new Common module, its regression,
SubEnumR.Coupling and AllImports. It trusts dependencies and is not an
exhaustive recursive kernel audit. CI is intentionally not consulted.

Results: full build/AllImports, 119 tool tests, exact source conservation, architecture,
505 exact compiled contracts, and all soundness scopes (199 exact / 36 generic
quotient / 18 finite-real joint / 80 native MathComp) passed. The four-module
joint targeted kernel check passed. The 15 new endpoint assumption audit
found common/rat/high-universe facts closed; only the realType specialization
inherits existing MathComp propositional/dependent-functional extensionality
and constructive indefinite description. Module counts are 291 -> 293
(Gate S 289 -> 291, Gate M unchanged at 2); regression modules 78 -> 79.
