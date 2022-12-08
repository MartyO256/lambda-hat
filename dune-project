(lang dune 3.2)

(name lambda-hat)

(implicit_transitive_deps false)

(generate_opam_files true)

(license "MIT")

(authors "Marc-Antoine Ouimet")

(maintainers "marc-antoine.ouimet@mcgill.ca")

(source
 (github "MartyO256/lambda-hat"))

(package
 (name lambda-hat)
 (synopsis
  "Implementation of the lambda-hat calculus of typed lambda-calulus with stages.")
 (depends
  dune-build-info
  odoc
  ocaml
  hamt
  yojson
  angstrom
  lambda-term
  (ocaml-lsp-server :with-test)
  (ocamlformat :with-test)
  (alcotest :with-test)
  (bisect_ppx :with-test)))
