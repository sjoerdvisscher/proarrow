{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The laws of "Proarrow.Category.Instance.Paths", exercised on a schema that carries equations:
-- the Employee and Department schema of Fong and Spivak, /Seven Sketches in Compositionality/
-- (arXiv:1803.05316), section 3.1.
--
-- A quiver with no equations generates a free category and the laws hold structurally. The
-- interesting case is a quiver with a 'Rewrite' instance, where composition normalises and
-- associativity holds only if that rewriting system is confluent. Nothing checks confluence, so
-- 'propCategory' below is what stands between a plausible-looking set of equations and a category
-- that is not one.
--
-- The instance then carries the second, separate obligation: that the data satisfies the
-- constraints the equations state. See the last two properties.
module Props.Paths (test) where

import Control.Monad (unless)
import Data.Type.Equality ((:~:) (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testFailed, testProperty)
import Prelude hiding (id, (.))

import Proarrow.Category.Enriched.Thin (Finite (..), Indexed (..), Member (..), memberIndex)
import Proarrow.Category.Instance.Discrete (DISCRETE (..))
import Proarrow.Category.Instance.Paths (EqGen (..), PATHS (..), Paths (..), Rewrite (..), emb, pathLength)
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Functor (Copresheaf)
import Proarrow.Testing
  ( GenTotal
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genSomeFinite
  , oneOfTotal
  , optGen
  )
import Proarrow.Testing.Laws (propCategory, propProfunctor)

-- | The points of the schema, as bare data: two entity points and one attribute point. The
-- category over them is 'DISCRETE', which supplies the identity arrows and makes 'Ob' the point\'s
-- own index. @(\':~:\')@ would serve as the arrows just as well, but its 'Ob' is vacuous, and then
-- the test suite has to carry a singleton class of its own to say which point it has been handed.
-- 'DISCRETE' supplies that, and enumerability with it.
type data HRPoint = EmployeeP | DepartmentP | StrP

instance Indexed HRPoint
instance Finite HRPoint where type Objects HRPoint = '[EmployeeP, DepartmentP, StrP]

type HR' = DISCRETE HRPoint

type Employee' = D EmployeeP :: HR'
type Department' = D DepartmentP :: HR'
type Str' = D StrP :: HR'

-- | A singleton for the points. 'memberIndex' already refines a point to the one it is, but
-- positionally -- @There (There Here)@ says nothing about which point that is -- so the three
-- positions get names, as pattern synonyms rather than as a separate type with a dispatcher.
type SHR (a :: HR') = Member a (Objects HR')

pattern SEmployee :: () => (a ~ Employee') => SHR a
pattern SEmployee = Here

pattern SDepartment :: () => (a ~ Department') => SHR a
pattern SDepartment = There Here

pattern SStr :: () => (a ~ Str') => SHR a
pattern SStr = There (There Here)

{-# COMPLETE SEmployee, SDepartment, SStr #-}

type GHR :: CAT HR'
data GHR a b where
  Mngr :: GHR Employee' Employee'
  WorksIn :: GHR Employee' Department'
  Secr :: GHR Department' Employee'
  FName :: GHR Employee' Str'
  DName :: GHR Department' Str'

deriving instance Show (GHR a b)

-- | Generators are distinguishable, and each one determines where it starts.
instance EqGen GHR where
  eqGen Mngr Mngr = Just Refl
  eqGen WorksIn WorksIn = Just Refl
  eqGen Secr Secr = Just Refl
  eqGen FName FName = Just Refl
  eqGen DName DName = Just Refl
  eqGen _ _ = Nothing

-- | The two equations, as a rewriting system: a department's secretary works in that department,
-- and an employee's manager works in the same department. Each is one clause, matching the junction
-- between the arrow being composed on and the normal path it lands on. The second recurses, because
-- dropping a @Mngr@ can expose another one.
instance Rewrite GHR where
  rewrite WorksIn (PCons Secr more) = more
  rewrite WorksIn (PCons Mngr more) = rewrite WorksIn more
  rewrite q f = PCons q f

-- | The book's own running schema (section 3.1), which the airline one deliberately avoids: two
-- entity points, one attribute point, and two path equations. Equations are what a graph cannot
-- express and a category can, and they are the reason a schema is a category at all.
type HR = PATHS GHR

type Employee = PTH Employee' :: HR
type Department = PTH Department' :: HR
type Str = PTH Str' :: HR

-- | The book's instance, equation 3.1.
--
-- > Employee | FName | WorksIn | Mngr      Department | DName | Secr
-- > 1        | Alan  | 101     | 2         101        | Sales | 1
-- > 2        | Ruth  | 101     | 2         102        | IT    | 3
-- > 3        | Kris  | 102     | 3
type Staff :: Copresheaf HR
data Staff u a where
  Emp1, Emp2, Emp3 :: Staff '() Employee
  Dep101, Dep102 :: Staff '() Department
  Txt :: String -> Staff '() Str

deriving instance Eq (Staff u a)
deriving instance Show (Staff u a)

staffStep :: GHR a b -> Staff '() (PTH a) -> Staff '() (PTH b)
staffStep Mngr Emp1 = Emp2
staffStep Mngr Emp2 = Emp2
staffStep Mngr Emp3 = Emp3
staffStep WorksIn Emp1 = Dep101
staffStep WorksIn Emp2 = Dep101
staffStep WorksIn Emp3 = Dep102
staffStep Secr Dep101 = Emp1
staffStep Secr Dep102 = Emp3
staffStep FName Emp1 = Txt "Alan"
staffStep FName Emp2 = Txt "Ruth"
staffStep FName Emp3 = Txt "Kris"
staffStep DName Dep101 = Txt "Sales"
staffStep DName Dep102 = Txt "IT"

instance Profunctor Staff where
  dimap Unit PNil x = x
  dimap Unit (PCons g rest) x = staffStep g (dimap Unit rest x)
  r \\ s = case s of
    Emp1 -> r
    Emp2 -> r
    Emp3 -> r
    Dep101 -> r
    Dep102 -> r
    Txt _ -> r

allEmployees :: [Staff '() Employee]
allEmployees = [Emp1, Emp2, Emp3]

allDepartments :: [Staff '() Department]
allDepartments = [Dep101, Dep102]

-- * Law checking

-- | The singleton at a path-category object, which is the one at its vertex.
theHR :: forall (a :: HR). (Ob a) => SHR (UN PTH a)
theHR = memberIndex @(UN PTH a)

instance Testable HR where
  showOb @a = case theHR @a of
    SEmployee -> "Employee"
    SDepartment -> "Department"
    SStr -> "Str"
  genSome = genSomeFinite

-- | Grow a path backwards from its target, normalising as it goes, so every generated arrow is in
-- normal form like every other one.
genPath :: Int -> SHR x -> SHR y -> GenTotal (Paths (PTH x :: HR) (PTH y))
genPath n sx sy = oneOfTotal (stay ++ grow)
  where
    stay = case (sx, sy) of
      (SEmployee, SEmployee) -> [pure PNil]
      (SDepartment, SDepartment) -> [pure PNil]
      (SStr, SStr) -> [pure PNil]
      _ -> []
    grow
      | n <= 0 = []
      | otherwise = case sy of
          SEmployee -> [rewrite Mngr <$> genPath (n - 1) sx SEmployee, rewrite Secr <$> genPath (n - 1) sx SDepartment]
          SDepartment -> [rewrite WorksIn <$> genPath (n - 1) sx SEmployee]
          SStr -> [rewrite FName <$> genPath (n - 1) sx SEmployee, rewrite DName <$> genPath (n - 1) sx SDepartment]

-- | Comparing paths needs nothing of the endpoints: 'EqGen' decides it from the generators.
instance TestingEqShow (Paths (a :: HR) b)

instance (Ob a, Ob b) => TestableType (Paths (a :: HR) b) where
  gen = genPath 3 (theHR @a) (theHR @b)

instance TestableProfunctor (Paths :: CAT HR)

instance TestingEqShow (Staff u b)

instance (Ob b) => TestableType (Staff '() b) where
  gen = case theHR @b of
    SEmployee -> optGen allEmployees
    SDepartment -> optGen allDepartments
    SStr -> optGen (Txt <$> ["Alan", "Ruth", "Kris", "Sales", "IT"])

instance TestableProfunctor (Staff :: HR +-> ())

test :: TestTree
test =
  testGroup
    "Paths"
    [ testProperty "the schema's equations hold in the schema, by construction" $ do
        unless
          (pathLength (emb WorksIn . emb Secr :: Department ~> Department) == 0)
          (testFailed "a secretary followed by where they work should be the identity")
        unless
          (pathLength (emb WorksIn . emb Mngr :: Employee ~> Department) == 1)
          (testFailed "a manager followed by where they work should be just where they work")
    , -- Normalisation makes the equations hold of the /schema/ whatever the data says, so this is
      -- not implied by the test above: it is the separate, unchecked obligation that the instance
      -- satisfies the constraints, which is the property the whole approach is sold on.
      testProperty "and the instance satisfies them, which is a separate matter" $ do
        unless
          (all (\d -> staffStep WorksIn (staffStep Secr d) == d) allDepartments)
          (testFailed "every department's secretary must work in that department")
        unless
          (all (\e -> staffStep WorksIn (staffStep Mngr e) == staffStep WorksIn e) allEmployees)
          (testFailed "every employee's manager must work in the same department")
    , propCategory @HR
    , testProperty "Staff is a profunctor" $ propProfunctor @Staff
    ]
