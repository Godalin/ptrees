# Frozen CI toolchain

`ptree-ci.opam` is a CI-only constraint package, captured from the working local
environment on 2026-09-21. It does not tighten the library's published bounds in
`coq-ptree.opam` or `dune-project`.

The profile fixes **67 packages**, including OCaml 5.2.1, Coq 8.20.1,
Dune/dune-configurator 3.17.2, Coq-Elpi 2.4.0, Elpi 2.0.7, HB 1.8.1,
and every recorded transitive OCaml/Coq dependency. CI installs the constraint
package **before any Coq/Elpi installation**, in one dependency solve. The
package remains installed so subsequent project dependency installation cannot
upgrade these versions. Installation must fail rather than relax a constraint.
`tools/check_ci_environment.py` checks the installed versions and executable
versions before the project build; unexpected non-system dependencies also fail.

## Provenance

62 versions come from the active local switch's installed-package inventory.
Five Coq libraries are present on disk but absent from that inventory:
ExtLib 0.13.0, ITree 5.2.1, Paco 4.2.3, Coinduction 1.20, and
RelationAlgebra 1.7.11. Their versions were recovered from the existing
`ptree-buildtest` installation's opam records and checked by byte-comparing all
installed `.v` sources (117, 68, 41, 7, and 48 files respectively) against the
active installation. No local package was installed, upgraded or removed.

## Reproduction boundary

This freezes **compiler and dependency package versions**, not an entire OS
image. The working local environment is macOS; CI remains Linux, with the runner
label fixed to `ubuntu-24.04` instead of `ubuntu-latest`. Architecture, C compiler,
system libraries, runner image updates, opam repository metadata and GitHub
Actions are not claimed to be byte-identical. Extra `conf-*` packages may be
needed for Linux system probes; all probes already in the profile remain pinned.
The opam frontend for dependency solves is also fixed to local version 2.5.1,
using the official Linux binary with a checked SHA-256 digest. Self-upgrade is
disabled. `setup-ocaml` still bootstraps the compiler switch with its bundled
opam; the version check runs against the selected 2.5.1 binary before building
the project.

Do not run the installation command in the existing local switch just to check
this profile: the local environment is intentionally left unchanged. The strict
checker targets CI's package-managed installation and will correctly report the
five unregistered local libraries as missing from opam. Validate edits with
`opam lint .github/ci/ptree-ci.opam` and the tool unit tests; any local solver
experiment must use `--dry-run`.

For a **new, disposable** reproduction switch only:

```sh
opam switch create . ocaml-base-compiler.5.2.1 \
  --repos default,coq-released=https://coq.inria.fr/opam/released
eval $(opam env)
opam install ./.github/ci/ptree-ci.opam -y
opam install . --deps-only --with-test -y
python3 tools/check_ci_environment.py
opam exec -- dune build
```

The installed constraint package is deliberate: using `--deps-only` for the
profile would discard its persistent constraints. The normal project installation
still uses `--deps-only --with-test`. Existing theorem/assumption snapshots and
all audit/build/kernel-check steps are unchanged.
