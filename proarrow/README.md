[![Haskell-CI](https://github.com/sjoerdvisscher/proarrow/actions/workflows/haskell-ci.yml/badge.svg)](https://github.com/sjoerdvisscher/proarrow/actions/workflows/haskell-ci.yml)

# proarrow

A Haskell library for doing category theory with a central role for profunctors.

## Core ideas

### One category per kind

Kind-indexed categories makes life a lot easier, once you know what the kind is of a type,
you know which category it belongs to.

### Use newtype wrappers on kinds

Using kind-indexed categories means you cannot share objects between categories. Newtype
wrappers fix this. For example, if you have a category for kind `k`, it's opposite category
has kind `OP k`.

### Kind `j -> k -> Type` is reserved for profunctors

If profunctors would have kind `OP j -> k -> Type`, then `(->)` wouldn't be a profunctor
as is. This would require too many wrappers all over the place. So instead `j -> k -> Type`
is reserved for profunctors. So for the category of bifunctors we do need a wrapper.

### Use constraints to limit which objects are part of a category

You need this already when creating a category of functors, then each object needs a
`Functor` constraint. It turns out this is powerful enough to limit the objects of any
type of category.

### These constraints can be observed from arrows

If you're not careful these objects constraints can become unweildy, requiring a long list
of object constraints for each function. But if you have an arrow from `a` to `b`, that's
proof enough that `a` and `b` are objects. So there are functions `(//)` and `(\\)` to
observe the constraints.

### Functors that don't land in Type are written as representable profunctors

Functors have kind `j -> k`, but you can't just make a datatype of any kind, it must
always be of the shape `j -> k -> ... -> Type`. So for example you can't make an
identity functor that works for any `k`. But functors are isomorphic to representable
profunctors, with kind `k -> j -> Type`. (Note that the kinds swap!) So you can write
an identity representable profunctor!

### Generalize the category theory to work with profunctors

To make working with representable profunctors instead of functors easier,
the category theory should work with profunctors where possible.

## Example: defining your own category

A category is picked out by its *kind*, so a new category starts with a fresh kind -- here one
with two objects, a `Draft` and a `Live` state, and a single non-identity arrow publishing the
one as the other.

```haskell
{-# LANGUAGE TypeData, TypeFamilies #-}
import Prelude hiding (id, (.))

import Proarrow.Core (CAT, CategoryOf (..), ObId (..), Profunctor (..), Promonad (..), dimapDefault)

type data STATE = Draft | Live

type Move :: CAT STATE
data Move a b where
  KeepDraft :: Move Draft Draft
  Publish :: Move Draft Live
  KeepLive :: Move Live Live

deriving instance Show (Move a b)

-- 'id' has to produce the identity *at whichever object it is asked for*, so being an
-- object is exactly the ability to supply that identity:
instance ObId Draft where objId = KeepDraft
instance ObId Live where objId = KeepLive

instance CategoryOf STATE where
  type (~>) = Move

instance Promonad Move where
  KeepDraft . KeepDraft = KeepDraft
  Publish . KeepDraft = Publish
  KeepLive . Publish = Publish
  KeepLive . KeepLive = KeepLive

instance Profunctor Move where
  dimap = dimapDefault
  r \\ KeepDraft = r
  r \\ Publish = r
  r \\ KeepLive = r
```

Beyond `TypeData` and `TypeFamilies` above, going further needs more extensions — a
`Proarrow.Testing.TestableType` instance for `Move a b`, for instance, also needs
`UndecidableInstances`. Rather than discovering them one failed build at a time, enable the set
the library itself is built with: `GHC2024` plus the `default-extensions` block in
[`proarrow.cabal`](proarrow.cabal).

```haskell
>>> KeepLive . Publish . id
Publish
```

The `Ob` family is where the object constraints from above come in, and the `\\` method is how
those constraints are observed from an arrow — matching on a constructor reveals which objects
it runs between. Note what is *absent*: no `type Ob`, and no `id`. `Ob` defaults to `ObId`, and
`id` defaults to `objId`, so the two instances above are the whole of the object structure. A
category where every type of the kind is an object with no evidence needed says
`type Ob a = Any a` instead — that is what `Hask` does. Where the objects carry *no* non-identity
arrows at all, reach for `Proarrow.Category.Instance.Discrete`'s `DISCRETE` (see
`test/Props/Paths.hs`), and a one-object category needs no dispatch at all, being just a monoid —
`Proarrow.Category.Instance.Monoid`.

And now the generic kind-machinery applies: `OPPOSITE STATE` is the opposite category,
`(STATE, STATE)` the product category, `STATE +-> STATE` are profunctors on states, and so on.
The `Proarrow` module exports the curated core vocabulary; `Proarrow.Core` explains the design
in depth, and the `Proarrow.Category.Instance.*` modules contain many more worked examples of
categories.

To property-test the laws of your own category, depend on the public sublibrary
`proarrow:testing`: a `Testable` instance for your kind plus the law checks from
`Proarrow.Testing.Laws` (`testCategory`, `testMonoidal`, ...) give it a test suite —
proarrow's own tests are built from exactly these pieces.

## Laws as code

A class's laws are written down next to the class, as ordinary proarrow code that works in any
category with the structure: a `Laws` instance from `Proarrow.Tools.Laws`, keyed by the list of
structures the laws mention. For example, from `Proarrow.Category.Monoidal`:

```haskell
instance Laws '[Monoidal] where
  laws =
    [ ...
    , Law "associator naturality" \ @a @b @c @d mor -> do
        f <- mor @a @b "f"
        g <- mor @b @c "g"
        h <- mor @c @d "h"
        associator @_ @b @c @d . ((f ** g) ** h) === (f ** (g ** h)) . associator @_ @a @b @c
    , ...
    ]
```

A law binds the object variables it uses and asks the supply `mor` for named arbitrary arrows
between them, then states its equation with `===`. `testLaws` from `Proarrow.Testing.Laws.Run`
checks each law as its own property. It draws random objects and arrows, runs the law in a
category whose arrows also describe themselves, and on failure prints both sides as the code
they were built from:

```
Failed swap naturality:
swap . (f ** g) = ...
(g ** f) . swap = ...
```

`testMonoidal`, `testClosed` and the other checks for proarrow's own classes are built this way,
and a class of your own can be checked the same way: `test/Examples/CustomLaws.hs` walks through
a complete one.
