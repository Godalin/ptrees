# Relational omega limits: proved scope and remaining boundary

Baseline: `6f79c197`. This is additive probability mathematics, not another
architecture migration. Existing interfaces, routing, FreeOmega relations,
MathComp implementations and PTree proofs are unchanged.

**At this increment: the countably supported external-measure case is proved;
the unrestricted native MathComp case remains open.** The subsequent
[generic consumer extraction](GENERIC_RELATIONAL_CONSUMERS.md) proves the
structural bridges with an explicit relational-limit premise, discharged for
FreeOmega but not yet for unrestricted native MathComp. The proof and
validation record below describes the original additive increment.

## 1. Countable support suffices for arbitrary relations

`Prob/Backend/Common/CountableRelationalLimit.v` proves:

```text
c and d are increasing chains of OmegaVal subprobabilities
each c_n and d_n is countably supported
each pair (c_n,d_n) has a joint concentrated on T
---------------------------------------------------------
the two lubs have an actual joint concentrated on T
```

`oval_coupled_lub` permits heterogeneous and arbitrarily large carriers,
arbitrary Prop-valued relations, deficient or zero mass, and infinite support.
Neither carrier must be countable, inhabited, or equipped with decidable
equality. No topological closedness or decidability condition is imposed on T.
The covers may depend on n and may contain duplicates and invalid codes.

`oval_coupled_lub_of_countable_limits` alternatively needs countability only
of the limits. `oval_coupled_lub_witnesses` accepts arbitrary endpoint
representatives related to the lubs by bounded observational equality.

The proof separates two mathematically different facts:

1. `Prob/Domain/RelationalLimit.oval_bidual_lub`: bounded-test inequalities
   pass through pointwise suprema. This needs no countability or supplied
   joint-limit witness. It follows directly from scalar supremum monotonicity.
2. The existing `oval_bidual_coupled`: countable transport realizes those
   limiting inequalities as an actual joint. Its previously proved
   tightness/no-mass-escape argument supplies the existence theorem.

`oval_countably_supported_lub` supplies the connection: select a cover for
each approximant and enumerate their union by nat-pair coding. AE concentration
passes through the evaluator supremum. It does not identify the cover with
the exact positive-mass support.

There is no new transport axiom or realization class. In particular, this
does not extend external joint existence to arbitrary native MN, or imply
completeness of syntactic qlift. SubEnumQ/SubEnumR modelable completions already
have countable-support theorems; their existing soundness proofs are unchanged.

## 2. A generic sufficient condition using existing probability laws

`Prob/Interface/RelationalLimit.sem_lift_lub_of_joint_chain` proves a separate
generic result. Given an **increasing joint chain** j_n with:

```text
bind j_n (ret . fst) sem_eq c_n
bind j_n (ret . snd) sem_eq d_n
AE j_n (fun (x,y) => T x y)
```

any supplied lubs of c and d are related by `sem_lift T`.

Its actual requirements are frontier measure/CoreLaws/BindLaws/AELiftLaws,
omega operations/OmegaLaws/OmegaAELaws. It uses:

```text
lub existence for j
  -> bind continuity for both projections
  -> sem_lub_proper identifies the marginal representatives
  -> AE support persists at the joint lub
  -> AE-restricted diagonal plus relational bind gives the desired lifting
```

The marginal certificates deliberately use `sem_eq`; the proof does not
assume that an equality lifting reflects into `sem_eq`. No new class,
selection of joints, or theorem-level PTree premise is hidden in this result.
The theorem is closed under the global context (its existing capabilities
are explicit parameters).

`mathcomp_coherent_joint_limit` instantiates the SAME generic theorem with
the native MathComp model, with normal universe checking. The existing
`MathCompCouplingGluing` premise remains explicit through its CoreLaws instance.
The client is not recursive frontier assembly and does not use Gate M.

## 3. Increasing joints cannot be inferred from increasing marginals

The regression proves a finite counterexample, not merely non-monotonicity
of one arbitrary sequence of selected witnesses. Let:

```text
c_0 = d_0 = (1/2) delta_true
c_n = d_n = (1/2) delta_true + (1/2) delta_false   (n >= 1)
T x y := (x = true) or (y = true)
```

Both marginal chains increase. Every level has a T-joint. At level zero,
EVERY joint has mass 1/2 on (true,true). At subsequent levels, EVERY T-joint
has mass zero there: forbidding (false,false) forces the fair marginals into
the crossed joint.

`no_increasing_joint_selection` proves that no increasing sequence of joint
witnesses for these chains exists. Consequently, a proof which picks a joint
at each n and silently applies the ordinary increasing-chain lub operation
is invalid, even on a finite carrier.

Nevertheless `noncoherent_chain_has_limit_joint` uses the new countable limit
theorem to produce a joint at the limit. Thus the counterexample refutes
**coherent selection**, NOT relational-lub closure. It also does not rule out
constructing specially coherent operational joint kernels for particular
PTree proofs; that would be a separate construction with its own obligations.

## 4. What is not established

- No unrestricted native `mathcomp_kernel_lift` relational-limit theorem.
- No theorem that every MathComp native measure is countably supported.
- No generic `pstruct/pstrong -> peutt`, algebra, or iter migration.
- No independence theorem showing the existing generic laws cannot imply
  relational-limit closure by some different proof.

The current MathComp model uses a powerset/discrete sigma-algebra on its
lifted carriers and on its joint carrier, not an arbitrary Borel/product
measurable space. Therefore neither a standard Borel coupling theorem nor a
continuous-space counterexample is silently claimed to settle its case.
Its current carrier definition does not supply a countable-support witness.

The countable theorem lives in external validation. Mainline Eq/Interp and
native MathComp laws do not import it. Closing the native gap still requires
either a native realization argument at the intended scope, or a separate
operational joint construction sufficient for the structural bridges. This
increment does not disguise that obligation as a new capability assumption.

## 5. Validation

- Full local `opam exec -- dune build`, including safe AllImports: passed.
- 465 old compiled contracts and logical assumptions: unchanged.
- 319 baseline theory modules: byte-for-byte unchanged, apart from four
  exact AllImports additions. Four modules are added; no theorem is moved.
- 22 new endpoint types and assumptions are frozen in
  `RELATIONAL_LIMIT_CONTRACTS.json`; logical dependencies use only the existing
  whitelist. No axiom/class or checker bypass is added.
- All 168 Python tool tests: passed, including new scope/boundary mutation tests.
- Architecture: 323 modules, 321 Gate S and the unchanged two Gate M modules.
  The new countable realization adapter is explicitly classified as external
  validation and rejected as a dependency of mainline/native theory.
- Four-module joint `coqchk -norec`: targeted safe bodies checked; dependencies
  trusted. Not a whole-library recursive kernel audit; no Gate M included.
- CI and environment changes excluded, as requested.

Reproducible checks: `audit_relational_limits.py --compiled`,
`audit_assumptions.py --check`, `audit_architecture.py --check`,
`audit_soundness.py --source-only`, and the Python tool tests. The previous
consumer-migration audit remains intact through an exact projection which
removes only these four new modules and aggregate lines.
