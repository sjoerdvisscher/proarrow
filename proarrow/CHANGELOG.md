# Revision history for proarrow

## Unreleased

* New `Proarrow.Tools.SMC`: linear HOAS for symmetric monoidal categories, with `do` notation,
  traces (`rec`, `loop`) and duals (`produce`, `annihilate`).
* Fixed: in the Int construction, the tensor of morphisms, the associators, `linDist`,
  `linDistInv` and `distribDual` looped forever. The Int construction over `FinRel` is now
  law-tested.

## 0.1.0.0 -- 2026-09-28

* First release