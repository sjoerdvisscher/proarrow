# Revision history for proarrow

## Unreleased

* `Proarrow.Tools.Einsum`: `einsum @"ij,jk->ik" a b` on tensors in hypergraph categories.
* `Proarrow.Tools.SMC`: index notation for categories whose index types are `Frobenius`: `sumOver`
  binds a summed index, `delta` is the Kronecker delta, and `*^`/`^*` multiply by a scalar term.
* `Proarrow.Tools.SMC` no longer uses linear types: a variable used more than once is copied
  (`CocommutativeComonoid`) and an unused one is discarded (`Comonoid`). `with` takes two terms and
  `caseOf` the scrutinee and two branches, sharing the variables around them. `call` and `closed`
  are removed.
* `Proarrow.Tools.SMC` is split into multiple internal modules.
* `Proarrow.Category.Instance.DecoratedCospan`: `DECCOSPAN f`, cospans whose apex carries an
  `Alternative` decoration, a hypergraph category.
* `Proarrow.Category.Instance.Cospan`: `COSPAN k` is `DECCOSPAN` with the `Undecorated` decoration.
* `Proarrow.Category.Instance.OpenHypergraph`: open hypergraphs with typed wires.
* `Proarrow.Category.Monoidal.Hypergraph`: `Sized`, the size of an object (a dimension, a number of
  elements), which the read-back of open hypergraphs and `einsum` choose their contraction order by.
* `Proarrow.Optic.Iso`: `DecidableIso`, categories that decide whether two objects are isomorphic,
  with the isomorphism as an optic of any flavour; instances for `Mat`, `FinRel`, `SVG` and `DOT`.
* `Proarrow.Object`: `ListOf c xs`, a type-level list with the evidence `c` for each element as a
  value, with `KnownListOf`. It replaces the library's own list singletons:
  * `Strictified`: `SList` is removed; `sList` is a `ListOf Ob'`.
  * `Thin`: `FNil`/`FCons` are now `Nil`/`Cons`, and `HasFiniteDefault` is removed (`finite`
    defaults to `listOf`).
  * `Edges`: `ENil`/`ECons` are removed.
* `Proarrow.Object`: `SomeOf c`, a type with the evidence `c` known only at runtime, built with
  `Some @a`. In `Proarrow.Testing`, `Some k` is `SomeOf TestOb'`, and `MkSomeList` is replaced by
  `mkSomeList`.
* `Proarrow.Optic.Kaleidoscope`, `Proarrow.Optic.Grate`: kaleidoscopes and grates now need
  `CocommutativeComonoid m` instead of `Comonoid m`.
* `Proarrow.Category.Monoidal.Applicative`: `Alternative`'s superclass is `HasBinaryCoproducts j` and
  `Monoidal k` instead of `Distributive j`.
* `Proarrow.Optic.Traversal`: `fromTravVL` builds a `Traversal` from a Prelude traversal, with `Baz`
  as the witness.
* `Proarrow.Category.Monoidal.Distributive`: `Traversing`, a new component of
  `StrongDistributiveProfunctor`, and `Traversable (CorepStar t)`. Eliminating a traversal with an
  unbounded witness through the generic carrier no longer loops. The `Traversable` witness
  instances need `Distributive k` and `CopyDiscard k` instead of `Bicartesian k`.
* `Proarrow.Profunctor.Instance.Star`: `Traversable (Star (Prelude g))`;
  `Strong CoprodAction (Star f)` for any strong lax monoidal `f` and `Strong ProdAction (Star f)`
  for any functor on `Type`.
* `Proarrow.Tools.Diagrams.Svg`: the option `bendSpiders` draws a merge point followed by a discard
  point as a cap, and a unit point followed by a copy point as a cup; `slidePoints` moves unit and
  discard points next to what uses or makes their wire.
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