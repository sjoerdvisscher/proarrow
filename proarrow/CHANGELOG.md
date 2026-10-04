# Revision history for proarrow

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