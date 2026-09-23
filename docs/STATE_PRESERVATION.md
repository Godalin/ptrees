# State-indexed behavioral preservation

Baseline: `c2c047f` (arbitrary fixed-handler preservation).
All 346 pre-existing theory modules are frozen, except the five new sorted
AllImports entries. The operational `run_state`, prior State/bind/iter proofs,
fixed-handler proof, backend definitions, and canonical routing are unchanged.

## Public result

`Interp/StatePreservation.run_state_peutt` proves:

```
t peutt[RR] u
    -> run_state t s peutt[state_result_rel RR] run_state u s

state_result_rel RR (s1,a) (s2,b) := s1 = s2 /\ RR a b.
```

Both return carriers may differ. The source premise is arbitrary weak
`peutt`, not `pstruct`, `pstrong`, syntax equality, or a finite-event condition.
Native `Prob`, residual `Vis`, partial mass and arbitrarily many state updates
remain allowed. The initial state is shared; no theorem asserts preservation
when the two initial states differ arbitrarily.

`run_state_peutt_eq` specializes the output to ordinary equality of pairs.
`run_state_peutt_eq_Proper` covers **both curried arguments** of `run_state`:

```
Proper (peutt eq ==> eq ==> peutt eq) run_state.
```

This can be registered locally and is tested by an actual `setoid_rewrite H`
under `run_state t s`; no global instance or inference hint is introduced.

## Why the state-indexed argument is needed

The fixed-handler theorem does not magically carry mutable state. We do not
apply it to a different stateless handler at each step and claim preservation.
Instead the proof explicitly threads a configuration `(s,t)` through the
same generic relational-hitting and finite/limit machinery:

* Ret `a` emits the stable result `(s,a)`;
* Get returns the current state to the source continuation, internally;
* Put changes the configuration state before continuing, internally;
* an unhandled event emits its target visible head with state-threaded
  continuations;
* native Tau/Prob work is accelerated only within these boundaries.

`StateMachine.v` relates configurations by equal states and source `peutt`.
Whole-frontier coupling respects the same dependent event, so related Get/Put
heads perform the same state update. Target recursive candidates appear only
under an actual residual target Vis. Eliminated State events stay in the
internal machine relation and are handled by finite induction plus relational
increasing-limit closure.

`StateMachineScheduling.v` separately proves adequacy with the unchanged
operational `run_state`. Its physical machine approximants are mutually below
the actual tree approximants **at the same fuel**. Its accelerated phase grid
satisfies:

```
grid(n,m,c) <= physical((n+1)*(m+1),c)
physical(n,c) <= grid(n,n,c).
```

Diagonal continuity, Fubini and directed cofinality then convert complete
machine witnesses into actual `run_state` hitting witnesses. The proof reuses
the prior generic finite-frontier associativity and kernel-continuity lemmas;
it never assumes observable equality reflects approximation order.

The final coinduction is a short source-indexed application of these results,
not a second backend theorem or a preservation class. The evolving state is
the extra mathematical datum that prevented a direct use of fixed-handler
`peutt_interp`.

## Capability and trust boundary

The generic theorem requires frontier Core laws; order/omega/cofinality,
diagonal/Fubini, bind/mixed order and selection; and the existing propositions
`relational_bind`, `relational_zero`, `relational_lub`. It does **not** need
full frontier BindLaws or any native-measure capability directly. Every new
generic machine, scheduling and preservation endpoint is closed under the
global context.

`Interp/FreeOmega/State.v` instantiates the same theorem with the established
completion certificates. SubEnumQ and SubEnumR clients both compile, using
their existing native capabilities; logical assumptions are inherited from
those instances and remain within the existing whitelist. MathComp's Gate M
allowlist is unchanged, and no unconditional direct MathComp relational-lub
claim is added.

## Regressions and earlier algebra

The new regression checks:

* arbitrary heterogeneous source peutt;
* actual rewriting under the curried `run_state`;
* eliminating Get and Put, with the correct updated state;
* the previous structural bind/iter equations promoted to peutt;
* different Boolean/natural result carriers;
* a weak Tau rewrite around the unbounded State+Prob counter;
* concrete `Put 9; Get` execution from state 3 returning `(9,9)`;
* an independent arbitrary-effect SubEnumR client;
* generic imports do not load FreeOmega, Domain or MathComp.

The earlier State algebra remains the stronger structural version. We do not
copy those proofs or change their assumptions merely to give the same equation
a weak-equivalence name.

This closes the outstanding State behavioral-preservation requirement. It
does **not** close the full roadmap: standard Reader/Writer/Exception clients,
StateT/fold commutation, general rational sampler correctness, and the complete
execution/denotational bridge still need work.

## Audit

`audit_state_preservation.py` checks exact old-source and four old-snapshot
conservation, rejects new axioms/classes/checker bypass or target-preservation
premises, and records 28 elaborated endpoints with `Print Assumptions`.
Generic endpoints additionally must be axiom-free and backend-independent.
Its mutation tests protect the weak premise and the required adequacy bridge.

Local verification completed: full `dune build` including AllImports and
extraction, 31 focused effects/handler/State Python tests, architecture and
source-conservation audits, all 28 new contracts, unchanged 465 mainline,
27 handler and 44 operational contracts, and a joint five-module `coqchk -norec` passed. The
earlier arbitrary-handler commit ran the then-complete 202-test suite; the
State follow-up does not misreport its focused run as another full suite.
Targeted `coqchk -norec` checks selected new safe module bodies while trusting
dependencies; it is not a whole-library recursive check. CI remains
intentionally out of scope.
