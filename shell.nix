with import <nixpkgs> { };
mkShell {
  buildInputs = [
    clang
    gnumake
    pkg-config
    gmp
  ];
}
