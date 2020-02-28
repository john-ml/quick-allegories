{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Test.QuickCheck
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Char as C
import Data.Function (on)

-- Printable characters
newtype PChar = PChar {unPChar :: Char} deriving (Eq, Ord)

instance Show PChar where show = show . unPChar

instance Enum PChar where
  toEnum = PChar . C.chr
  fromEnum = C.ord . unPChar

instance Bounded PChar where
  minBound = PChar ' '
  maxBound = PChar '~'

instance Arbitrary PChar where
  arbitrary = elements [minBound .. maxBound]

type Rel = [(PChar, PChar)]

infix 4 =~=
(=~=) :: Rel -> Rel -> Bool
(=~=) = (==) `on` S.fromList

infixl 7 ·
(·) :: Rel -> Rel -> Rel
r · s = [(x, z) | (x, y) <- s, (y', z) <- r, y == y']

idt :: Rel
idt = [(x, x) | x <- [minBound .. maxBound]]

infix 4 ⊆
(⊆) :: Rel -> Rel -> Bool
r ⊆ s = S.fromList r `S.isSubsetOf` S.fromList s

infixl 5 ∩
(∩) :: Rel -> Rel -> Rel
r ∩ s = S.toList (S.fromList r `S.intersection` S.fromList s)

op :: Rel -> Rel
op = map (\(x, y) -> (y, x))

infix 2 <=>
(<=>) :: Bool -> Bool -> Bool
(<=>) = (==)

checkCategoryFacts = do
  quickCheck \ r s t -> r · (s · t) =~= (r · s) · t
  quickCheck \ r -> r · idt =~= r
  quickCheck \ r -> idt · r =~= r

checkAllegoryFacts = do
  -- Facts about meets
  quickCheck \ x r s -> x ⊆ r ∩ s <=> x ⊆ r && x ⊆ s
  quickCheck \ r s -> r ∩ s =~= s ∩ r
  quickCheck \ r s t -> r ∩ (s ∩ t) =~= (r ∩ s) ∩ t
  quickCheck \ r -> r ∩ r =~= r
  -- Meets and inclusions
  quickCheck \ r s -> r ⊆ s <=> r ∩ s =~= r
  quickCheck \ r s t -> r · (s ∩ t) ⊆ (r · s) ∩ (r · t)
  quickCheck \ r s t -> (r ∩ s) · t ⊆ (r · t) ∩ (s · t)
  -- Converse
  quickCheck \ r -> op (op r) =~= r

main = do
  checkCategoryFacts
  checkAllegoryFacts
