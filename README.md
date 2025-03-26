# Formalization of Random Behavior for Interaction Trees

## Introduction

## Meta

- Author(s):
  - Linyu Yang
  - Yuchi Su

## Building Instructions

### Obtaining the project

```sh
git clone git@github.com:Godalin/ptrees.git
cd ptrees
```

### Setting up the environment

Create a local `opam` switch and install the dependencies, and activate the switch:

```sh
opam switch create ./ --repos default,coq-released=https://coq.inria.fr/opam/released --deps-only
eval $(opam env)

# update the dependencies
opam install ./ --deps-only
```

### Build the project

Run

``` sh
dune build
```

to build the theories.

### Dependencies

We list the dependencies here, although are not needed to be installed manually if you use the local `opam` switch approach:
- `coq-ext-lib`
- `coq-coinduction`
- `coq-itree`
- `coq-mathcomp`

If you do not want to use the local `opam` switch, you can manually install the dependencies above.
