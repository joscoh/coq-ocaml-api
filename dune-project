(lang dune 3.16)
(using coq 0.8)

(name coq_ocaml_api)

(generate_opam_files true)

(source
 (github joscoh/coq-ocaml-api))

(authors "Joshua M. Cohen")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name coq_ocaml_api)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
