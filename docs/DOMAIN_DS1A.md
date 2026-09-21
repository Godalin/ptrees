# DS1a: independent expectation-functional domain

Implementation baseline: DS0 `466429d`, with the accepted follow-up plan
splitting DS1 into DS1a/DS1b and postponing general coupling realization until
after stable-hitting adequacy. **DS1a is accepted at `e65ca85`.**
The subsequent [DS1b implementation](DOMAIN_DS1B.md) is reported separately.
This stage alone does not claim standard-measure
correspondence, FreeOmega soundness, or stable-hitting adequacy.

## Mathematical object

`Prob/Domain/Expectation.v` defines one new semantic object:

```coq
OmegaVal (R : realType) (A : Type)
```

It is a record of an evaluator `(A -> R) -> R` and `OmegaValLaws`, a `Prop`
record of zero, monotonicity, bounded positive scaling, bounded addition,
mass at most one, and monotone continuity. Evaluators are only contracted on
`oval_test f`, meaning `forall x, 0 <= f x /\ f x <= 1`.

There is no syntax of probabilistic computations inside this domain. Ret,
bottom, bind and increasing-chain Lub are constructed records with direct
mathematical evaluators:

```text
oval_ret x f       = f x
oval_bottom f      = 0
oval_bind L k f    = L (fun x => k x f)
oval_lub c Hinc f  = sup_n (c n f)
```

Their law fields are proved, not supplied as axioms or assumed instances of
the existing `SemanticMeasure`/`SemanticOmega` hierarchy. Scalar supremum
lemmas use MathComp `realType` and its ordinary supremum. This module does
not import any other PTree module.

`oval_eq` and `oval_le` compare bounded tests. The order is a preorder on
records, antisymmetric up to `oval_eq`: thus a pointed omega-CPO **up to
observational equality**, not a claim that raw records form an antisymmetric
order under Coq equality. No quotient construction is needed for the API.
The regression even constructs equal domain values whose evaluators differ
on an unbounded test, so record equality would genuinely be the wrong API.

## Proved endpoints

- `oval_eq_equivalence`, `oval_le_refl`, `oval_le_trans`, `oval_le_antisym`;
- `oval_eval_bounds`, `oval_mass`, `oval_bottom_le`;
- `oval_lub_upper`, `oval_lub_least`, `oval_lub_proper`;
- `oval_bind_ret_l`, `oval_bind_ret_r`, `oval_bind_assoc`;
- `oval_bind_mono`, `oval_bind_proper`;
- `oval_bind_lub_l`, `oval_bind_lub_r`, `oval_bind_double_diagonal`;
- `oval_laws_ext`: transport all laws through equality on bounded tests.

The last helper lets later stages package the existing `free_omega_upper`
evaluator and transport its laws without defining another recursive
interpreter or choosing a representative.

The substantive supremum work is scalar: scaling, increasing-sum
interchange, and exchange of two bounded countable suprema. These prove
closure of `oval_lub` under additivity and test continuity. Right bind
continuity uses the source evaluator's continuity; left bind continuity is
pointwise. The simultaneous source/kernel diagonal theorem uses monotonicity
to dominate `(i,j)` by `(max i j, max i j)`.

## Architecture and tests

`Prob/Domain` is classified as **external validation**, not generic FreeOmega
or a concrete native backend. The architecture checker enforces both:

1. Domain can depend only on other Domain modules and external mathematical
   libraries, not on existing PTree probability interfaces or syntax.
2. Mainline modules cannot import the domain or the explicitly reserved
   validation adapters. In addition a transitive-closure check covers `PTree`,
   `API/*`, `Eq/PEutt`, `Eq/FreeOmega/*`, `Interp/*`, and `Examples/*`.

The adapter path list covers the proposed SubEnum/MathComp `Domain`,
SubEnum `Admissibility`/`DomainSoundness`/`CouplingSoundness`, and
`Eq/Backend/StableHittingDomainSubEnum`. Future validation modules with other
names require an explicit ownership-policy update. Regression imports of
validation modules are intentional. No ordinary public facade exports them.

`Regression/Probability/OmegaVal.v` checks:

- distinct Boolean Diracs and bottom/Dirac separation;
- the nonconstant chain `bottom, ret true, ret true, ...` has the expected Lub;
- alternating distinct Diracs are not increasing, and `oval_lub` cannot be
  called without an increasingness proof;
- simultaneous source/kernel diagonal continuity;
- every domain value on the empty carrier has zero mass;
- observational equality does not constrain unbounded tests;
- a high-universe result carrier containing types is allowed;
- importing Expectation has not loaded FreeOmega, SemanticMeasure or PTree.

These are domain regressions. The separate raw-FreeOmega alternating-term
non-admissibility theorem remains a DS2 obligation.

## Verification and logical assumptions

- Complete `opam exec -- dune build`, including AllImports: passed locally.
- AllImports covers all 221 other modules (222 modules total).
- Single-process targeted `coqchk -norec` on Expectation and its regression:
  passed. These modules' proof bodies were checked; dependency bodies were
  admitted by this targeted invocation. This is not Gate D.
- The original 306-entry public/helper compiled signature and assumption
  snapshot remains unchanged.
- [DS1a compiled audit](DOMAIN_DS1A_AUDIT.md): 37 selected domain/regression
  entries, including actual types and `Print Assumptions` output.
- Architecture graph and all 40 audit-tool unit tests passed, checked by
  `audit_architecture.py --check` and unittest discovery.

No new axiom or admitted proof was declared. The actual inherited logical
dependencies include MathComp propositional/function extensionality and
constructive indefinite description, and Coq functional extensionality.
The domain is therefore not advertised as constructive or axiom-free.
`realType` is the explicit scalar parameter, not a hidden backend capability.
There is no remote CI or whole-library kernel-check claim here.

## Next acceptance boundary

Pause after DS1a. DS1b will construct the independent standard-measure
adapter, using an ordinary cemetery-point carrier if needed, and establish
the expectation/integration correspondence. Only DS1a plus DS1b justifies
the full **standard probability model** claim. Neither a second free
completion nor an early general coupling theorem belongs in DS1b.
