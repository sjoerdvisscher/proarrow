module Proarrow.Category.Bicategory.Product where

import Prelude (type (~))

import Proarrow.Category.Bicategory (Bicategory (..), Adjunction (..), Monad (..), Comonad (..))
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault)

type PRODK :: CAT j -> CAT k -> CAT (j, k)
data PRODK jj kk j k where
  PROD :: jj (Fst ik) (Fst jl) -> kk (Snd ik) (Snd jl) -> PRODK jj kk ik jl

type family PRODFST (p :: PRODK jj kk j k) :: jj (Fst j) (Fst k) where
  PRODFST (PROD p q) = p
type family PRODSND (p :: PRODK jj kk j k) :: kk (Snd j) (Snd k) where
  PRODSND (PROD p q) = q
type family Fst (p :: (j, k)) :: j where
  Fst '(a, b) = a
type family Snd (p :: (j, k)) :: k where
  Snd '(a, b) = b

type Prod :: CAT (PRODK jj kk j k)
data Prod a b where
  Prod :: { fst :: a ~> b, snd :: c ~> d } -> Prod (PROD a c) (PROD b d)

instance (CategoryOf (jj (Fst ik) (Fst jl)), CategoryOf (kk (Snd ik) (Snd jl))) => Profunctor (Prod :: CAT (PRODK jj kk ik jl)) where
  dimap = dimapDefault
  r \\ Prod f g = r \\ f \\ g
instance (CategoryOf (jj (Fst ik) (Fst jl)), CategoryOf (kk (Snd ik) (Snd jl))) => Promonad (Prod :: CAT (PRODK jj kk ik jl)) where
  id = Prod id id
  Prod f1 g1 . Prod f2 g2 = Prod (f1 . f2) (g1 . g2)
instance (CategoryOf (jj (Fst ik) (Fst jl)), CategoryOf (kk (Snd ik) (Snd jl))) => CategoryOf (PRODK jj kk ik jl) where
  type (~>) = Prod
  type Ob (p :: PRODK jj kk ik jl) = (Ob (PRODFST p), Ob (PRODSND p), p ~ PROD (PRODFST p) (PRODSND p))

instance (Bicategory jj, Bicategory kk) => Bicategory (PRODK jj kk) where
  type Ob0 (PRODK jj kk) jk = (Ob0 jj (Fst jk), Ob0 kk (Snd jk))
  type I = PROD I I
  type PROD a b `O` PROD c d = PROD (a `O` c) (b `O` d)
  r \\\ Prod f g = r \\\ f \\\ g
  iObj = Prod iObj iObj
  Prod f g `o` Prod h i = Prod (f `o` h) (g `o` i)
  leftUnitor (Prod p q) = Prod (leftUnitor p) (leftUnitor q)
  leftUnitorInv (Prod p q) = Prod (leftUnitorInv p) (leftUnitorInv q)
  rightUnitor (Prod p q) = Prod (rightUnitor p) (rightUnitor q)
  rightUnitorInv (Prod p q) = Prod (rightUnitorInv p) (rightUnitorInv q)
  associator (Prod p q) (Prod r s) (Prod t u) = Prod (associator p r t) (associator q s u)
  associatorInv (Prod p q) (Prod r s) (Prod t u) = Prod (associatorInv p r t) (associatorInv q s u)

instance (Adjunction (PRODFST l) (PRODFST r), Adjunction (PRODSND l) (PRODSND r), Ob l, Ob r) => Adjunction l r where
  unit = Prod (unit @(PRODFST l) @(PRODFST r)) (unit @(PRODSND l) @(PRODSND r))
  counit = Prod (counit @(PRODFST l) @(PRODFST r)) (counit @(PRODSND l) @(PRODSND r))

instance (Monad (PRODFST m), Monad (PRODSND m), Ob m) => Monad m where
  eta = Prod eta eta
  mu = Prod mu mu

instance (Comonad (PRODFST m), Comonad (PRODSND m), Ob m) => Comonad m where
  epsilon = Prod epsilon epsilon
  delta = Prod delta delta

instance (HasCompanions hj vj, HasCompanions hk vk) => HasCompanions (PRODK hj hk) (PRODK vj vk) where
  type Companion (PRODK hj hk) (PRODK vj vk) fg = PROD (Companion hj vj (PRODFST fg)) (Companion hk vk (PRODSND fg))
  mapCompanion (Prod f g) = Prod (mapCompanion f) (mapCompanion g)
  compToId = Prod compToId compToId
  compFromId = Prod compFromId compFromId
  compToCompose (Prod fl fr) (Prod gl gr) = Prod (compToCompose fl gl) (compToCompose fr gr)
  compFromCompose (Prod fl fr) (Prod gl gr) = Prod (compFromCompose fl gl) (compFromCompose fr gr)

instance (Equipment hj vj, Equipment hk vk) => Equipment (PRODK hj hk) (PRODK vj vk) where
  type Conjoint (PRODK hj hk) (PRODK vj vk) fg = PROD (Conjoint hj vj (PRODFST fg)) (Conjoint hk vk (PRODSND fg))
  mapConjoint (Prod f g) = Prod (mapConjoint f) (mapConjoint g)
  conjToId = Prod conjToId conjToId
  conjFromId = Prod conjFromId conjFromId
  conjToCompose (Prod fl fr) (Prod gl gr) = Prod (conjToCompose fl gl) (conjToCompose fr gr)
  conjFromCompose (Prod fl fr) (Prod gl gr) = Prod (conjFromCompose fl gl) (conjFromCompose fr gr)
  comConUnit (Prod f g) = Prod (comConUnit f) (comConUnit g)
  comConCounit (Prod f g) = Prod (comConCounit f) (comConCounit g)