(lang dune 3.15)
; Because we use menhir 3.0 we need dune 3.13, but there is a bug until 3.15
; that affects us (which prevents building packages that do not require rocq
; when it is not installed).

(using menhir 3.0)
(using coq 0.8)

(generate_opam_files)

(name cerberus)
(license BSD-2-Clause)
(maintainers "Kayvan Memarian <kayvan.memarian@cl.cam.ac.uk>")

(source
 (github rems-project/cerberus))

(homepage "https://www.cl.cam.ac.uk/~pes20/cerberus/")

(package
 (name cerberus-lib)
 (synopsis "The Cerberus C semantics as a library")
 (description "The frontend and pipeline of Cerberus as a library for building backends")
 (authors
  "Kayvan Memarian"
  "Victor B. F. Gomes"
  "Justus Matthiesen"
  "Peter Sewell"
  "Kyndylan Nienhuis"
  "Stella Lau"
  "Jean Pichon-Pharabod"
  "Christopher Pulte"
  "Rodolphe Lepigre"
  "James Lingard"
  "Thomas Sewell"
  "Dhruv Makwana"
 )
 ; !!README!! write an explanation here when updating a dependency
 ;            version constraint.
 (depends
  (ocaml (>= 4.14.0))
  ; oldest version on opam
  (lem (>= 2020-06-03))
  ; version introducing --exn-carries-state
  (menhir (>= 20211230))
  ; version introducing PPrint.range
  (pprint (>= 20180528))
  ; API changed
  (yojson (>= 2.0.0))
  ; earlier verions do not build easily on macOS (tested on Sonoma)
  ; this is also a constraint from coq 8.18 (required by cerberus-cheri)
  (zarith (>= 1.11))
  ; Dependencies of vendored SibylFS
  ; earlier versions do not build with recent C compilers
  (sha (>= 1.12))
  ; API changed
  (sexplib (>= v0.14.0))
  (ppx_sexp_conv (>= v0.14.3))
 ))

(package
 (name cerberus)
 (synopsis "The Cerberus C semantics")
 (description "The Cerberus C semantics and related tools.")
 (authors
  "Kayvan Memarian"
  "Victor B. F. Gomes"
  "Justus Matthiesen"
  "Peter Sewell"
  "Kyndylan Nienhuis"
  "Stella Lau"
  "Jean Pichon-Pharabod"
  "Christopher Pulte"
  "Rodolphe Lepigre"
  "James Lingard"
  "Thomas Sewell"
  "Dhruv Makwana")
  (depends
   cerberus-lib
   (ocaml (>= 4.14.0))
   ; version introducing the Cmd module
   (cmdliner (>= 1.1.0)))
 )

(package
 (name cerberus-bmc)
 (synopsis "Cerberus-BMC")
 (description "Cerberus-BMC: a Principled Reference Semantics and Exploration Tool for Concurrent and Sequential C")

 (authors
  "Stella Lau"
  "Jean Pichon-Pharabod"
  "Victor B. F. Gomes"
  "Kayvan Memarian"
  "Peter Sewell")
 (depends
  cerberus-lib
  (ocaml (>= 4.14.0))
  (cmdliner (>= 1.1.0))
  ; earlier version requiring python 2.7
  (z3 (>= 4.9.1))
  ; API changed
  (angstrom (>= 0.14.0)))
)

(package
 (name cerberus-web)
 (synopsis "Cerberus web application")
 (description "Server and client-side web interface for the Cerberus C semantics")
 (authors
  "Victor B. F. Gomes"
  "Kayvan Memarian")
 (depends
  cerberus-lib
  (ocaml (>= 4.14.0))
  (cmdliner (>= 1.1.0))
  ; constrained by ocaml version dependency
  (fpath (>= 0.7.3))
  (ezgzip (>= 0.2.3))
  ; API constraint
  (cohttp-lwt-unix (and (>= 4.0.0) (< 6.0.0)))
  lwt
  base64
  z3
  (angstrom (>= 0.14.0)))
)

(package
 (name cerberus-cheri)
 (synopsis "The Cerberus CHERI C semantics")
 (description "The Cerberus C semantics with the CHERI C memory model")
 (authors
  "Vadim Zaliva"
  "Kayvan Memarian")
 (depends
  cerberus-lib
  (cmdliner (>= 1.1.0))
  ounit2 ; only with test?
  (coq (= 8.18.0))
  (coq-bbv (and (>= 1.3) (<= 1.4)))
  coq-ext-lib
  ; these three are pinned (see .template file)
  coq-sail-stdpp
  coq-struct-tact
  coq-cheri-capabilities
  (landmarks :with-dev-setup)
  (landmarks-ppx :with-dev-setup)
 )
)
