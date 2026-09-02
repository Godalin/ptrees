(lang dune 3.8)

(using coq 0.8)

(name coq-ptree)

(license GPL-3.0-only)

(authors "Linyu Yang")

(maintainers "Linyu Yang")

(generate_opam_files true)

(package
 (name coq-ptree)
 (synopsis "Probabilistic eventful computation trees")
 (version 0.1)
 (source (github Godalin/ptrees))
 (depends
  (coq
   (and (>= 8.20) (< 9.0)))
  (coq-ext-lib
   (>= 0.13.0))
  (coq-coinduction
   (>= 1.20))
  (coq-paco
   (>= 4.2.3))
  (coq-itree
   (>= 5.2.1))
  (coq-relation-algebra
   (>= 1.7.11))
  (coq-mathcomp-algebra
   (and (>= 2.3.0) (< 2.5.0)))
  (coq-mathcomp-analysis
   (and (>= 1.13.0) (< 1.15.0)))))
