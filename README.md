# A Framework for Implementing OCaml APIs in Coq

This repo provides a design pattern for writing OCaml programs in Coq that:
- Are capable of handling exceptions, mutable state, and efficient machine integers
- Can implement existing OCaml APIs that use these constructs, preserving the types
- Are fully executable within Coq (via `compute`) and via extraction to OCaml
- Can be proved correct in Coq's logic without additional axioms

The main idea is to implement the features in question differently in Coq and OCaml by *modifying the extraction process*.
For example, error handling is implemented in the error monad in Coq and via exceptions in OCaml.
We provide interfaces to enable such monadic programming in Coq while extracting correctly to the appropriately idiomatic OCaml constructs.

The core of the repo is in `CoqCompat`; this provides a small library for programming in this style, including:
- Error handling, including try-catch mechanisms, implemented using the error monad (Coq) and exceptions (OCaml)
- Machine-length (31-bit) integers, implemented using CompCert's `Integer` library (Coq) and `int` (OCaml)
- Efficient unbounded integers using `Z` (Coq) and `Zarith` (OCaml)
- Mutable state, using a state monad (Coq) and mutable references (OCaml)
- Generic ways of writing recursive functions over OCaml integers in Coq (using well-founded recursion, though this is hidden from clients)
- An implementation of the Hoare State Monad allowing proofs properties about stateful computations in Coq.

We demonstrate this design pattern on 3 examples:
- `list` implements several functions from OCaml's `List` library using exceptions and machine-length integers
- `ctr` implements a mutable counter
- `term` implements an arithmetic term library inspired by Why3; it handles variable binding by generating new unique identifiers for each created variable. We implement
(stateful) capture-avoiding substitution and prove it correct using the State Hoare Monad.

Each example has the following structure:
- `src` gives the API implementation in Coq, using utilities from `CoqCompat`
- `extract` gives the `.mli` interface and the extraction commands, as well as modifies the imports for the extracted `.ml` files
- `client-coq` is a client program in Coq that uses the API for proofs and computations
- `client-ocaml` is a client program in OCaml that uses the API for computations

## Building

This builds under OCaml 4.14.1, dune 3.16, and Coq 8.18.0. It relies on Coq libraries `compcert` (the open source component), `coq-ext-lib`, and `Equations` as well as OCaml library `Zarith`.

To build all proofs, run `dune build` from the root directory.
You can run the OCaml client programs by running `dune exec clientlist`, `dune exec clientctr`, and `dune exec clientterm`.
