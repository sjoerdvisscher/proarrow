# Revision history for proarrow

## Unreleased

* New `Proarrow.Tools.SMC`: linear HOAS for symmetric monoidal categories, with `do` notation,
  traces (`rec`, `loop`) and duals (`produce`, `annihilate`).
* New `Proarrow.Category.Monoidal.IsoMix`: *-autonomous categories whose unit of par is isomorphic to
  the unit (`dualUnit`, `dualUnitInv`), so that a dual and its object join into the unit
  (`dualityCounit`). It is a superclass of `CompactClosed`, which no longer has `dualUnit` or
  `dualityCounit`: instances move them to an `IsoMix` instance, and `dualUnitInv` is now a method.
  `dualityCounitDefault` moved to the new module. `LINEAR` is isomix without being compact closed.
* Fixed: in the Int construction, the tensor of morphisms, the associators, `linDist`,
  `linDistInv` and `distribDual` looped forever. The Int construction over `FinRel` is now
  law-tested.

## 0.1.0.0 -- 2026-09-28

* First release