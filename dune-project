(lang dune 3.8)

(using coq 0.8)

(name coq-ptree)

(license "GPL 3.0")

(authors "Linyu Yang")

(maintainers "Linyu Yang")

; (source
;  (github vellvm/ctrees))

; (bug_reports "https://github.com/vellvm/ctrees/issues")

(generate_opam_files true)

(package
 (name coq-ptree)
 (synopsis "probability tree")
 (version 0.1)
 (depends
  (coq
   (>= 8.18))
  (coq-ext-lib
   (>= 0.11.3))
  (coq-coinduction
   (>= 1.3))
  (coq-itree
   (>= 5.0))
  (coq-mathcomp-reals
   (>= 1.9))))
