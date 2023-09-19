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
as is. This would require too many wrapper all over the place. So instead `j -> k -> Type`
is reserved for profunctors. This means that bifunctors need to use `(j, k) -> Type`.

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

To make working with representable profunctors instead of functors, the category theory
should work with profunctors where possible.
