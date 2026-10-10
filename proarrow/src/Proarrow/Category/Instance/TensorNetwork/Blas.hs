{-# LANGUAGE CPP #-}

-- | Matrix products from the system's BLAS, for "Proarrow.Category.Instance.TensorNetwork". With
-- the package's @blas@ flag off they are all 'Nothing', and contractions use the generic loop.
module Proarrow.Category.Instance.TensorNetwork.Blas (Gemm, gemmDouble, gemmFloat, gemmComplexDouble) where

import Data.Complex (Complex (..))
import Data.Kind (Type)
import Data.Vector.Storable qualified as SV
import Prelude (Bool, Double, Float, Int, Maybe (..))

#ifdef BLAS
import Data.Vector.Storable.Mutable qualified as MSV
import Foreign.C.Types (CInt (..))
import Foreign.Marshal.Utils (with)
import Foreign.Ptr (Ptr)
import Foreign.Storable (Storable)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Prelude (IO, fromIntegral, ($), (*))
#endif

-- | A matrix product: whether the first and second matrix are stored transposed, the numbers of
-- rows, columns and summed indices, and the two matrices, row by row; the result row by row.
type Gemm :: Type -> Type
type Gemm e = Bool -> Bool -> Int -> Int -> Int -> SV.Vector e -> SV.Vector e -> SV.Vector e

gemmDouble :: Maybe (Gemm Double)
gemmFloat :: Maybe (Gemm Float)
gemmComplexDouble :: Maybe (Gemm (Complex Double))

#ifdef BLAS
-- | A BLAS matrix product, with its scalars as the type @s@: the layout, whether each matrix is
-- transposed, the numbers of rows, columns and summed indices, then alpha, the first matrix and its
-- row length, the second and its row length, beta, and the result and its row length.
type CblasGemm :: Type -> Type -> Type
type CblasGemm e s =
  CInt -> CInt -> CInt -> CInt -> CInt -> CInt -> s -> Ptr e -> CInt -> Ptr e -> CInt -> s -> Ptr e -> CInt -> IO ()

foreign import ccall safe "cblas_dgemm" cblas_dgemm :: CblasGemm Double Double
foreign import ccall safe "cblas_sgemm" cblas_sgemm :: CblasGemm Float Float
foreign import ccall safe "cblas_zgemm" cblas_zgemm :: CblasGemm (Complex Double) (Ptr (Complex Double))

-- | The product through a BLAS routine, given the scalars 1 and 0 as it takes them.
gemmWith :: (Storable e) => CblasGemm e s -> ((s -> s -> IO ()) -> IO ()) -> Gemm e
gemmWith routine scalars ta tb m n k a b = unsafeDupablePerformIO $ do
  -- beta is 0, so the result is not read before it is written
  c <- MSV.unsafeNew (m * n)
  scalars \one zero ->
    SV.unsafeWith a \pa -> SV.unsafeWith b \pb -> MSV.unsafeWith c \pc ->
      routine rowMajor (trans ta) (trans tb) (cint m) (cint n) (cint k) one pa (lead ta k m) pb (lead tb n k) zero pc (cint n)
  SV.unsafeFreeze c
  where
    rowMajor = 101
    trans t = if t then 112 else 111
    cint = fromIntegral
    -- the length of a stored row
    lead t notTransposed transposed = cint (if t then transposed else notTransposed)

gemmDouble = Just (gemmWith cblas_dgemm \k -> k 1 0)
gemmFloat = Just (gemmWith cblas_sgemm \k -> k 1 0)
gemmComplexDouble = Just (gemmWith cblas_zgemm \k -> with (1 :+ 0) \one -> with (0 :+ 0) \zero -> k one zero)
#else
gemmDouble = Nothing
gemmFloat = Nothing
gemmComplexDouble = Nothing
#endif
