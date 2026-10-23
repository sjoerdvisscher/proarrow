[![Haskell-CI](https://github.com/sjoerdvisscher/proarrow/actions/workflows/haskell-ci.yml/badge.svg)](https://github.com/sjoerdvisscher/proarrow/actions/workflows/haskell-ci.yml) [![Hackage](https://img.shields.io/hackage/v/proarrow.svg)](https://hackage.haskell.org/package/proarrow)

# proarrow

This repository holds two Haskell packages:

- [`proarrow`](proarrow) — category theory with a central role for profunctors.
- [`proarrow-equipment`](proarrow-equipment) — bicategories and proarrow equipments, built on
  top of `proarrow`.

See [`proarrow/README.md`](proarrow/README.md) for the core ideas behind the library.
The [wiki](https://github.com/sjoerdvisscher/proarrow/wiki) has worked examples and illustrated
guides to monoidal terms, sessions, optics, and tensor networks. Start with
[Einsum and hypergraph categories](https://github.com/sjoerdvisscher/proarrow/wiki/Einsum-and-hypergraph-categories)
for a tour from matrix operations to string diagrams and tensor contraction.

For executable examples, follow [a clocked digital circuit](https://github.com/sjoerdvisscher/proarrow/wiki/A-clocked-digital-circuit)
from gates to simulation and Verilog, or turn [a build pipeline into a parallel schedule](https://github.com/sjoerdvisscher/proarrow/wiki/From-a-build-pipeline-to-a-parallel-schedule)
with diagrams and a measured execution timeline.
