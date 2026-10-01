# Revision history for proarrow

## Unreleased

* New `Proarrow.Tools.SMC`: linear HOAS for symmetric monoidal categories, with `do` notation,
  traces (`rec`, `loop`), duals (`produce`, `annihilate`), classical reasoning (`refute`,
  `byContradiction`) and additives (`with`, `caseOf`).
* New `Proarrow.Category.Monoidal.IsoMix`: *-autonomous categories whose unit of par is isomorphic to
  the unit (`dualUnit`, `dualUnitInv`), so that a dual and its object join into the unit
  (`dualityCounit`). It is a superclass of `CompactClosed`, which no longer has `dualUnit` or
  `dualityCounit`: instances move them to an `IsoMix` instance, and `dualUnitInv` is now a method.
  `dualityCounitDefault` moved to the new module. `LINEAR` is isomix without being compact closed.
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
* Fixed: in the Int construction, the tensor of morphisms, the associators, `linDist`,
  `linDistInv` and `distribDual` looped forever. The Int construction over `FinRel` is now
  law-tested.

## 0.1.0.0 -- 2026-09-28

* First release