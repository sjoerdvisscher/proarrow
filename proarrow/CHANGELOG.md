# Revision history for proarrow

## Unreleased

* `Proarrow.Optic.Traversal`: `fromTravVL` builds a `Traversal` from a Prelude traversal, with `Baz`
  as the witness.
* `Proarrow.Category.Monoidal.Distributive`: `Traversing`, a new component of
  `StrongDistributiveProfunctor`, and `Traversable (CorepStar t)`. Eliminating a traversal with an
  unbounded witness through the generic carrier no longer loops. The `Traversable` witness
  instances need `Distributive k` and `CopyDiscard k` instead of `Bicartesian k`.
* `Proarrow.Profunctor.Instance.Star`: `Traversable (Star (Prelude g))`;
  `Strong CoprodAction (Star f)` for any strong lax monoidal `f` and `Strong ProdAction (Star f)`
  for any functor on `Type`.
* `Proarrow.Tools.SMC` no longer uses linear types. A variable used more than once is copied,
  which needs `CocommutativeComonoid`, and an unused one is discarded, which needs `Comonoid`. A
  `do` bind with a variable pattern binds a variable, so its right hand side is computed once.
  A `rec` block's variables may now also be used after the block, which copies them, or not at
  all.
  `with` takes two terms and `caseOf` takes the scrutinee and two branches, both sharing the
  variables around them. `split` allows unused variables. `call` and `closed` are gone:
  a reusable piece is compiled with `toSMC` and used with `lift`. New constraint classes
  `Thin` and `BindVar` appear in the types of `with`, `caseOf` and `split`. `Binds` is a class with
  its parameters reordered to depth, context, variable type, result type, pattern and continuation,
  and `Bind` loses its multiplicity parameter. The module exports only what its users need: the
  constructor of `Term`, the methods of `KnownObj`, `Tuple` and `Merge`, `Mul`, `synOb`, `ctxOb`,
  `withCtxOb`, `snoc`, `push2`, `Pat`, `BindPat`, `Ret`, `Rec` and `RecVars` are internal now.
* `Proarrow.Tools.SMC`: index notation for categories whose index types are `Frobenius`: `sumOver`
  binds a summed index, `delta` is the Kronecker delta, and `*^`/`^*` multiply by a scalar term.
  Examples `matMulT`, `traceIdxT`, `hadamardT`.
* `Proarrow.Category.Instance.Linear`: `CocommutativeComonoid (L (Ur a))` and
  `CocommutativeComonoid (L Bool)`.

## 0.2.0.0 -- 2026-10-04

* New `Proarrow.Tools.SMC`: linear HOAS for symmetric monoidal categories, with `do` notation,
  traces, duals, additives, and polarised System L inputs and outputs (`Consumer`, `Command`,
  `cut`, `cont`, `ret`, `classical`, the shifts `Up a = Not (Not a)` and `Dn` with `thunk` and
  `force`, and `recast` between type expressions for one object; a `do` bind of an `Up` runs it)
  over any dialogue category. With optimisation a compiled term is the category's own structure
  maps, composed.
* New `Proarrow.Category.Instance.Cps`: a closed symmetric monoidal category with a chosen answer
  object as a dialogue category, `Dual a = a ~~> r`. With `r = IO ()` this is call by push value;
  see the `Examples.Cbpv` test module. It is isomix exactly when `r` is the unit (`answerUnit`).
* New `Proarrow.Category.Monoidal.Dialogue`, now the superclass of `StarAutonomous`: `Dual`,
  `dual`, `linDist`, `linDistInv`, `doubleNegInv`, `Par` and its functions, `DualF` and the
  related helpers move there, with their laws (`DialogueStructures`, `testDialogue`, witness
  `DialogueW`). `StarAutonomous` keeps `dualInv`, `doubleNeg` and `ExpSA`. Instances split
  accordingly. New: `tripleNeg` and `bindDual`.
* New `Proarrow.Category.Monoidal.IsoMix`: dialogue categories with `Dual Unit ≅ Unit`
  (`dualUnit`, `dualUnitInv`, `dualityCounit`). It is a superclass of `CompactClosed`, which
  loses `dualUnit` and `dualityCounit` and lists `StarAutonomous` itself. `LINEAR` is isomix.
* `Proarrow.Testing` has `check`, which fails with a message unless a condition holds.
* GHC 9.14 support
  * `Testable` no longer has the quantified superclass `forall a. (TestOb a) => Ob' a`.
    `obFromTestOb` is now a `Testable` method instead, defaulting to the identity when `TestOb` is
    `Ob`; instances with their own `TestOb` define it (usually `obFromTestOb r = r`), and calls
    take the kind first (`obFromTestOb @_ @a`). `testObFromOb` is the converse.
  * `Proarrow.Testing` has `withTestOb2Def`, `withTestObProdDef`, `withTestObCoprodDef`,
    `withTestObExpDef` and `withTestObDualDef`, the objecthood witnesses for when `TestOb` is `Ob`.
  * `Functor` no longer has the quantified superclass `forall a. Ob a => Ob' (f a)`: `withObF`
    gives `Ob (f a)`.
  * The associativity superclass of `Strictly` no longer asks for `Ob b` and `Ob c`.
* Fixed: in `LINEAR`, `doubleNeg`, `dualInv` and the par eliminators returned stale values when
  compiled with optimisation, because every call of `dn` shared one reference.
* Fixed: in the Int construction, the tensor of morphisms, the associators, `linDist`,
  `linDistInv` and `distribDual` looped forever. The Int construction over `FinRel` is now
  law-tested.

## 0.1.0.0 -- 2026-09-28

* First release