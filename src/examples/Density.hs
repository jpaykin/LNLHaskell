{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase, FlexibleContexts, 
             RankNTypes
#-}
-- is UndecidableSuperClasses okay?

-- Implementation of density matrix interpretation of quantum computation
module Density where

import Prelim

import Control.Monad.State.Lazy
import Data.List hiding (transpose)
import Numeric.LinearAlgebra -- hmatrix library

-- There is no representational difference between a regular matrix
-- and a density matrix, but we think of density matrices as being a 
-- special case
type Mat = Matrix C
type Density = Matrix C

-- create an nxn density matrix from the elements of the list 
density :: Int -> [C] -> Density
density n = n >< n

ket0 :: Vector C
ket0 = fromList [1,0]
ket1 :: Vector C
ket1 = fromList [0,1]

density0 :: Density
density0 = density 2 [1,0,0,0]

density1 :: Density
density1 = density 2 [0,0,0,1]

newDensity :: Bool -> Density
newDensity True  = density1
newDensity False = density0

-- Unitaries

hadamard :: Mat
hadamard = 1/sqrt 2 `scale` (2 >< 2) [1,1,1,-1]

i :: C
i = 0 :+ 1

pauliX = ((2><2) [0,1,1,0]  :: Mat)
pauliY = ((2><2) [0,-i,i,0] :: Mat)
pauliZ = ((2><2) [1,0,0,-1] :: Mat)

cnot :: Mat
cnot = (4 >< 4) [1,0,0,0
                ,0,1,0,0
                ,0,0,0,1
                ,0,0,1,0]

-- conjugate transpose
transpose :: Mat -> Mat
transpose = tr

tensor :: Mat -> Mat -> Mat
tensor = kronecker

applyMat :: Mat -> Density -> Density
applyMat m ρ = transpose m <> ρ <> m


-- Manipulating the sizes of matrices


-- logSize ρ is n where ρ is a 2^n x 2^n matrix
logSize :: Mat -> Int
logSize ρ = floor . logBase 2 $ coerceIntegral n 
  where
    (n,_) = size ρ

-- if mat is a 2^mx2^m matrix and m <= n
-- then expandMat mat will be a 2^n x 2^n matrix
-- achieved by tensoring mat with the identity matrix of size 2^(n-m)
expandMat :: Mat -> Int -> Mat
expandMat mat n = mat `tensor` ident (2^(n-m))
  where
    m = logSize mat


-- first expand the matrix to be the same size as the density matrix,
-- and then apply.
applySubMat :: Mat -> Density -> Density
applySubMat mat ρ = applyMat (expandMat mat (logSize ρ)) ρ



-- Permutations ----------------------------------------

-- A permutation is a list of indices representing an isomorphism between
-- integers (see mkPermutation). It will be extended to an isomorphism between
-- columns of a density matrix.
--
-- Permutations will be used to apply operations to fragments of a density
-- matrix. For example, to apply the CNOT gate to qubits 2 and 0 of a system:
--      - Permute the columns of the state so that qubits 2 and 0 
--        appear in the first two columns
--      - Expand CNOT to the size of the state by multiplying it 
--        with the identity matrix.
--      - Multiply the state (ρ) with (CNOT⊗I)^† ρ (CNOT⊗I)
--      - Apply the inverse permutation to the result
type Permutation = [Int]

-- mkPermutation ls results in an isomorphism that maps
--   0 to the first element in the list,
--   1 to the second element in the list,
--   etc
-- Examples:
--      mkPermutation [2,3] = 0 |-> 2
--                            1 |-> 3
--                            2 |-> 0
--                            3 |-> 1
-- 
--      mkPermutation [2,0] = 0 |-> 2
--                            1 |-> 0
--                            2 |-> 1
-- The isomorphism is the identity of elements greater than the
-- max element in the list
mkPermutation :: [Int] -> (Int -> Int)
mkPermutation ls = fromAssocList $ zip [0..] (pad ls)

-- mkInversePermutation ls creates the inverse to mkPermutation
mkInversePermutation :: [Int] -> (Int -> Int)
mkInversePermutation ls = fromAssocList $ zip (pad ls) [0..]


-- pad ls will construct a list ls ++ ls'
-- where ls' contains all the integers not in ls
pad :: [Int] -> [Int]
pad ls = ls ++ ([0..] \\ ls)

-- convert from an association list to a function
fromAssocList :: [(Int,a)] -> Int -> a
fromAssocList assoc i = case lookup i assoc of
    Just a  -> a
    Nothing -> error $ "Index " ++ show i ++ " out of bounds"

-- applies the permutation to the rows of a density matrix
permutation :: [Int] -> Density -> Density
permutation = applyPermutation . mkPermutation 

inversePermutation :: [Int] -> Density -> Density
inversePermutation = applyPermutation . mkInversePermutation

applyPermutation :: (Int -> Int) -> Density -> Density
applyPermutation f d = assoc (m,n) 0 ls
  where
    (m,n) = size d
    ls = [((i,j), d `atIndex` (i,f j)) | i <- [0..m-1] ,
                                         j <- [0..n-1] ]


coerceIntegral :: (Integral a, Num b) => a -> b
coerceIntegral = fromInteger . toInteger


-- Applying a unitary transformation to a subset of qubits
-- in a density matrix

applyUnitary :: Mat -> [Int] -> Density -> Density
applyUnitary mat perm ρ = 
    -- move the relevant qubits to the front of the matrix
    -- then apply the submatrix to the front of the state
    -- finally apply the inverse permutation
    inversePermutation perm $ applySubMat mat $ permutation perm ρ

-- The monad
type DensityMonad = StateT Density []

-- TODO: check
newM :: Bool -> DensityMonad Int
newM b = do
    ρ <- get
    put $ ρ `tensor` newDensity b 
    return $ logSize ρ

applyUnitaryM :: Mat -> [Int] -> DensityMonad ()
applyUnitaryM m perm = modify $ applyUnitary m perm

measM :: Int -> DensityMonad Bool
measM i = undefined
