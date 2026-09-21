# DS4: stable-hitting denotational adequacy

Baseline: **DS3 accepted at `8082a52`**. This stage connects PTree's existing
SubEnum/FreeOmega stable hitting to the independent DS1 expectation domain.
It does not change the syntax, approximation, quotient, admissibility,
stable-hitting definition, or any maintained equational theorem.

## Independent mathematical kernel and finite iterations

`Eq/Backend/StableHittingDomainSubEnum.v` first defines hitting for any
mathematical kernel `K : S -> OmegaVal R (stable_target S H)`. Write
`V_n` for `domain_target_approx` and `D_n` for `domain_hitting_approx`:

```text
V_n(Stable h)       = delta h
V_0(Internal s)     = bottom
V_(n+1)(Internal s) = bind (K s) V_n
D_n(s)             = bind (K s) V_n
D(s)               = lub_n D_n(s)
```

Increasingness is proved using the mathematical bottom and monotonicity
of bind. The `lub` is DS1's genuine supremum of an increasing OmegaVal
chain. No raw FreeOmega evaluator or approximation relation is used to
define this kernel iteration or prove it increasing.

The PTree mathematical kernel `ptree_domain_kernel` is defined directly:

```text
Ret a     -> delta (Stable (FHRet a))
Vis e k   -> delta (Stable (FHVis e k))
Tau t     -> delta (Internal (observe t))
Prob mu k -> bind (subenum_domain mu)
                 (fun x => delta (Internal (observe (k x))))
```

Native probability mass is not normalized. This stops at the next stable
head, retaining the entire visible continuation, rather than interpreting
an entire interaction history.

`stable_target_denotational_commutation` is an induction on finite fuel.
It proves that the existing formal iterates denote these independently
defined mathematical iterates, assuming a pointwise kernel interpretation.
`ptree_kernel_denotational_commutation` discharges that assumption directly
for the primitive PTree kernel. The resulting theorem is:

```text
ptree_hitting_finite_commutation:
  upper (ptree_hitting_approx n s) f = eval (D_n(s)) f
  for every bounded [0,1]-valued test f.
```

The fuel convention matches the maintained kernel: a current Ret/Vis is
already seen at fuel zero; crossing an internal Tau/Prob consumes fuel.
The six `ptree_domain_approx_*` equations make this convention explicit.

## From finite iterates to every complete witness

The commuting theorem establishes validity of each finite approximation
and increasingness in the independent domain. DS2 then proves validity and
denotation of the canonical `FOLub (fun n => ptree_hitting_approx n s)`.

Crucially, clients need not use this syntactic representative. Complete
stable hitting identifies any witness with that canonical Lub under the
existing **observable** `sem_eq`. DS3 transports both admissibility and
bounded-test equality along that equality.

With the concrete SubEnum/FreeOmega instances understood, the endpoints are:

```coq
stable_hitting_admissible :
  ptree_stable_hitting s out -> free_omega_admissible R out.

stable_hitting_denotational_adequacy :
  ptree_stable_hitting s out ->
  free_omega_domain_denotes out (ptree_domain_hitting R s).

stable_hitting_domain_eq :
  forall Hv : free_omega_admissible R out,
  ptree_stable_hitting s out ->
  oval_eq (free_omega_domain Hv) (ptree_domain_hitting R s).
```

The first two have **no admissibility premise**, no AST premise, no
eventlessness condition, and no newly assumed semantic capability. They
apply to arbitrary eventful SubEnum PTrees. The third accepts any validity
proof when a client already has one; its equality is observational, not
equality of records or raw syntax.

`stable_hitting_mass_lub` specializes to the constant-one test:

```text
mass(denote out) = sup_n mass(D_n(s)).
```

Through DS1b this is a standard subprobability measure and its cemetery
mass is exactly `1 - sup_n mass(D_n(s))`. No new measure representation is
needed here. For SubEnum this deficit may include both native mass loss
and failure to reach the next stable head. It is **not unconditionally
pure divergence probability**. An infinite visible service can have
stable-hitting mass one at every interaction without ever terminating.

## Checked boundary examples and irrational limiting mass

`Regression/Probability/StableHittingDomain.v` checks automatic validity
and adequacy for arbitrary witnesses, a noncanonical `FORet` witness,
Dirac returns, silent divergence, native zero-mass sampling, and an
infinite visible service. Silent divergence and native mass loss both
denote bottom, while the visible service has next-head mass one. Negative
import probes ensure that this bridge does not import `peutt` or the
MathComp measure-model adapter.

`Regression/Probability/IrrationalHitting.v` constructs an actual guarded
PTree, not just an isolated FreeOmega Lub. Given increasing rationals
`0 = q_0 <= q_1 <= ... < 1`, at stage `n` it continues with probability

```text
c_n = (1 - q_(n+1)) / (1 - q_n)
```

and returns unit with probability `1 - c_n`. Both weights are rational,
and `schedule_coin_total` proves that **every native coin is total**.
The finite-iteration theorem is the telescoping identity

```text
mass(D_fuel(retry n)) = 1 - (1 - q_(n+fuel)) / (1 - q_n).
```

Starting at zero, finite hitting mass is precisely `q_fuel`. Enumerating
nonnegative rational lower bounds and taking finite running maxima gives
a chain with supremum any specified real `0 < alpha < 1`. The concrete
specialization `alpha = pi/2/2` uses MathComp's proven irrationality of pi.
`pi_canonical_hitting_irrational` connects this actual PTree's canonical
**FreeOmega** behavior to its irrational mass using DS4 adequacy.

This is a classical representation theorem. Selecting rational lower
bounds uses comparison with the real parameter; we do **not** claim an
effective sampler for arbitrary real inputs. The example establishes
rational-primitive / real-limit expressivity and internal noncompletion,
not an infinite interaction-path measure or a generic AST theorem.

## Isolation and verification

The theory is a one-way external validation module, outside all mainline
API, Eq/FreeOmega, Interp and Examples dependency closures. It imports the
existing reasoning infrastructure; that infrastructure does not import it.
General relational coupling realization, MathComp-native adequacy,
FiniteInternal pruning and Gate D remain separate later stages.

`audit_domain_hitting.py --source` checks all 231 frozen baseline `.v`
files byte-for-byte, allowing only three exact AllImports insertions and
the three new files. It also checks the direct mathematical definitions,
finite-fuel induction and use of DS3 transport. The compiled audit records
38 endpoints and their logical assumptions, rejects an admissibility
premise on the adequacy theorem, and retains the DS2/DS3 logical whitelist.
Historical audits and compiled snapshots are not weakened or rewritten.

Completed local checks:

- `opam exec -- dune build`, including the complete AllImports aggregate;
- `python3 tools/check_aggregate.py`: all 233 other modules imported once;
- `python3 tools/audit_domain_hitting.py --check`: exact frozen-source
  conservation and the [38-entry compiled type/assumption report](DOMAIN_DS4_AUDIT.md);
- `python3 tools/audit_architecture.py --check`: ownership and transitive
  external-validation boundaries preserved;
- DS1a/DS1b/DS2 compiled audits (`audit_domain.py`, `audit_domain_measure.py`,
  `audit_domain_soundness.py`, each `--check`): 37/37/51 contracts unchanged;
- DS3's source audit replayed against frozen `8082a52`, and its 19-entry
  compiled report compared directly with the current library;
- DS2.5's exact source audit replayed against frozen `7a3bf82`, and its
  55 compiled native/Upper contracts compared with the current library;
- `audit_public_capabilities.py --check` and `audit_capabilities.py --check`:
  all 306 mainline and original 25 baseline entries unchanged;
- `python3 -m unittest discover -s tools -p 'test_*.py'`: 64 tests;
- `git diff --check`.

The following **joint** kernel check completed with exit status 0:

```sh
opam exec -- coqchk -silent -R _build/default/theories PTree \
  PTree.Eq.Backend.StableHittingDomainSubEnum \
  PTree.Regression.Probability.StableHittingDomain \
  PTree.Regression.Probability.IrrationalHitting
```

This checks the three new modules together with their dependencies,
including the MathComp pi irrationality development. No remote CI or
whole-library Gate D result is claimed. There are no new declared axioms
or admitted proofs; inherited classical/extensional and UIP assumptions
remain explicit in the compiled report.

**Stop here for DS4 acceptance; do not start DS5 or prune adequacy machinery.**
