# Generic structural consumers

Baseline: `09d0ab2d71ede751093316a0f0f4be2f34705719`.

Follow-up: shallow left unit no longer uses the structural bridge or its
relational-lub premise. Other endpoints retain the profiles described below.
See [current capability/model status](GENERIC_CONSUMERS.md#current-capability-and-model-status).

## Ownership

The finite-kernel simulation, limit passage and PTree coinduction proofs now
have generic owners. There is no new PTree-level capability, global instance,
hint, quotient change, or canonical-route change.

```
Prob/Interface/RelationalClosure  (ordinary operation-level propositions)
                 |
Eq/RelationalHitting             (arbitrary kernels, finite and complete)
                 |
Eq/Relation                     (pstrong/pstruct -> peutt)
                 |
Eq/Algebra, Eq/Iter              (elementary and structural equations)
```

`Eq/FreeOmega/{Relation,Algebra,Iter}` retain their established theorem names
and types as thin specializations. Their thirteen migrated endpoints do not
contain a second copy of the generic upper proof. Syntax-specific finite
structural lifting and exact `free_omega_observes` transport remain in the
FreeOmega relation module: those conclusions really mention its syntax.

## Exact probability obligations

`relational_bind`, `relational_mixed_bind`, `relational_zero`, and
`relational_lub` are transparent `Prop` definitions, not classes or axioms.
They respectively state relational closure of frontier bind, native/frontier
bind, heterogeneous zero, and increasing-chain limits. They mention no
PTree relation. Full existing Bind/Mixed law packages imply the first two
by projection; callers can instead supply just their relational fields.

This distinction matters: the existing completion's full BindLaws and
MixedMeasureLaws instances require native AELift for their unrelated AE
congruence fields. The qlift relational constructors need no such premise.
Requiring those bundles would have strengthened every old structural bridge
and elementary equation. The four explicit certificates avoid that change.

The finite simulation uses CoreLaws plus relational bind/mixed bind/zero.
Complete bridges additionally use OrderLaws, OmegaLaws and relational-lub:

1. Related primitive kernels preserve the tagged stable/internal relation.
2. Fuel induction gives related finite hitting approximants.
3. OrderLaws make the two approximant sequences increasing.
4. Relational-lub relates their complete hitting witnesses.
5. Generic coinduction establishes `peutt`; `pstruct` uses the existing
   generic inclusion into `pstrong`.

The relation and return carriers are heterogeneous throughout. There is no
`no_event`, commutativity, countability, chosen joint chain, AE, or external
domain premise in these generic bridges.

## Model status

| Probability fact | FreeOmega MN | Native MathComp |
| --- | --- | --- |
| relational bind | proved from FOQLBind | proved from native bind |
| relational mixed bind | proved from FOQLSample | proved from native mixed bind |
| heterogeneous zero | proved structurally | proved by binding the empty carrier |
| increasing relational-lub | proved from existing qlift limit theorem | still open at unrestricted carrier scope |

The completion certificates require only native Measure/Core/Omega, so the
old SubEnumQ, SubEnumR and other valid completion specializations continue
to work without stronger assumptions. Real/rational eventful associativity
clients use the same generic theorem.

MathComp's three certificates are proved with normal universe checking in
`Prob/Backend/MathComp/RelationalClosure.v`; gluing is not needed for these
certificates. The existing Gate M regression checks an unconditional finite
approximant comparison, and a structural bridge/codiagonal client conditional
on `Hlimit : relational_lub NO`. Gluing remains explicit where CoreLaws need
it. No new Gate M file or checker relaxation is introduced.

**A conditional MathComp client is not a proof of unrestricted MathComp
relational continuity.** The external countable transport theorem cannot be
silently used as a mainline MathComp instance, and increasing marginals do
not provide increasing joints (see `RELATIONAL_LIMITS.md`).

## Migrated equations and remaining scope

Generic elementary equations: bind left/right unit, associativity, fmap
identity/composition and fmap over bind.

Generic structural iteration: unfold, pointwise structural congruence,
heterogeneous structural simulation, naturality and codiagonal. These accept
visible events and unbounded iteration. The previously generic conditional
eventful behavioral-iteration theorem is unchanged.

This is not a claim that every remaining FreeOmega theorem should be moved.
Eventless behavioral iteration still has a complete-row/scheduling proof in
the completion module; extracting that requires its own mathematical work.
Atomic/MDP interpretation specializations have not been migrated in this
increment. No theorem-level shortcut is introduced to call them generic.

## Preservation and verification

`audit_relational_consumers.py` compares all baseline source modules. For the
eleven extracted algebra/iter proofs it reconstructs the generic source from
the frozen old proof text, allowing only the explicit profile and bridge
specialization. Old wrapper statements, syntax-specific proofs and existing
generic proofs are unchanged. Other baseline files remain byte-frozen,
except exact aggregate insertions and approved appended certificates/clients.

`RELATIONAL_CONSUMER_CONTRACTS.json` includes the thirteen original compiled
wrapper contracts from the frozen main snapshot, plus compiled new endpoints.
Wrapper types must match exactly and logical assumptions must not grow.
The old 465-entry main snapshot and the old Gate M snapshot are not refreshed.
New Gate M observations have a separate snapshot, including unsafe-hierarchy
flags and safe controls; they are never reported as universe-checked.

Validation commands:

```
opam exec -- dune build
python3 tools/audit_relational_consumers.py --compiled --direct
python3 tools/audit_relational_limits.py --compiled
python3 tools/audit_generic_consumers.py --compiled
python3 tools/audit_architecture.py --check
python3 tools/audit_soundness.py --source-only
python3 -m unittest discover -s tools -p 'test_*.py'
```

CI and environment changes remain outside scope. Targeted `coqchk -norec`
checks safe module bodies with dependencies trusted, not a whole-library
recursive kernel audit; Gate M is excluded.

Local results: full build (including safe AllImports and the separately
classified Gate M clients), 178 Python tests, architecture/source checks,
465 unchanged main contracts, 22 previous relational-limit contracts,
54 new generic/backend/specialization contracts, and the three new Gate M
clients with six safe controls all pass. There are 328 modules: 326 Gate S
and the unchanged two Gate M modules. Neither old main nor old Gate M
compiled snapshot was modified.

The eleven-module joint `coqchk -norec` run also passed: the three generic
Eq owners, relational hitting and its probability interface, four FreeOmega
certificate/specialization modules, native MathComp relational certificates,
and the safe generic regression. Dependencies were trusted and Gate M was
excluded; this is not a full recursive kernel audit.
