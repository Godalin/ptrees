# Formalization of Random Behavior for Interaction Trees

## Introduction

## How to build

After cloning the PTree repository, use the following command to create a local `opam` switch and install the dependencies, and activate the switch:

```sh
opam switch create ./ --repos default,coq-released=https://coq.inria.fr/opam/released --deps-only
eval $(opam env)
```

Then run

``` sh
dune build
```

to build the theories.

### Dependencies

The dependencies are not needed to be installed manually, but we list them here:
- `coq-ext-lib`
- `coq-coinduction`
- `coq-itree`
- `coq-mathcomp`
