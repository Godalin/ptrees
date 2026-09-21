#!/usr/bin/env bash
# CI-only: never initialize or migrate the developer's opam root/switch.
set -euo pipefail
if [[ ${GITHUB_ACTIONS:-} != true || ${RUNNER_OS:-} != Linux || ${RUNNER_ARCH:-} != X64 ]]; then
  echo 'This bootstrap is only for disposable Linux x64 GitHub runners.' >&2
  exit 1
fi
: "${RUNNER_TEMP:?}" "${GITHUB_PATH:?}" "${GITHUB_ENV:?}"

# mktemp is essential: never reuse ~/.opam or a root/cache from a newer opam.
ci_workspace=$(mktemp -d "$RUNNER_TEMP/ptree-toolchain.XXXXXX")
mkdir "$ci_workspace/bin"
curl --fail --location --retry 5 \
  https://github.com/ocaml/opam/releases/download/2.5.1/opam-2.5.1-x86_64-linux \
  --output "$ci_workspace/bin/opam"
printf '%s  %s\n' \
  33705e328d9f740026ce182079e2457639791bcf04a0e4bafbdb2024dd4d6092 \
  "$ci_workspace/bin/opam" | sha256sum --check
chmod +x "$ci_workspace/bin/opam"
export PATH="$ci_workspace/bin:$PATH"
export OPAMROOT="$ci_workspace/root"
export OPAMNOSELFUPGRADE=true
# Ignore any switch selected by the runner's ambient environment.
unset OPAMSWITCH
test "$(opam --version)" = 2.5.1
test ! -e "$OPAMROOT"

# Git commit IDs freeze the package metadata as well as package versions.
coq_revision=a506e0a4a2983bf3b4248281c487327eb19fd2b6
git init -q "$ci_workspace/coq-repository"
git -C "$ci_workspace/coq-repository" fetch --depth=1 \
  https://github.com/rocq-prover/opam.git "$coq_revision"
git -C "$ci_workspace/coq-repository" checkout -q --detach FETCH_HEAD
test "$(git -C "$ci_workspace/coq-repository" rev-parse HEAD)" = "$coq_revision"

# GitHub-hosted Ubuntu disables unprivileged user namespaces. Package build
# scripts run without opam's bubblewrap sandbox in this disposable CI runner;
# this does not change the local environment or the proof/kernel audits.
opam init --bare --no-setup --no-opamrc --disable-sandboxing -y default \
  git+https://github.com/ocaml/opam-repository.git#3c79a939b221caf909b254fdff9616f8c0266e4f
opam repository add --all-switches coq-released "$ci_workspace/coq-repository/released" -y
opam switch create ptree-ci ocaml-base-compiler.5.2.1 \
  --repositories=coq-released,default -y
export OPAMSWITCH=ptree-ci
test "$(opam exec -- ocamlc -version)" = 5.2.1

# Persist exactly this root and frontend for every later workflow step.
echo "$ci_workspace/bin" >> "$GITHUB_PATH"
printf 'OPAMROOT=%s\nOPAMSWITCH=ptree-ci\n' "$OPAMROOT" >> "$GITHUB_ENV"
opam config report
