{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Test.Hspec
import Test.QuickCheck
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Char as C
import Data.Function (on)
import Control.Monad

-- Printable characters
newtype Int' = Int' {unInt' :: Int} deriving (Eq, Ord)

instance Show Int' where show = show . unInt'

instance Enum Int' where
  toEnum = Int'
  fromEnum = unInt'

instance Bounded Int' where
  minBound = Int' 0
  maxBound = Int' 100

instance Arbitrary Int' where
  arbitrary = elements [minBound .. maxBound]

type Rel = [(Int', Int')]

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

adjAll :: (a -> a -> Bool) -> [a] -> Bool
adjAll f = \case
  [] -> True
  [_] -> True
  x : xs@(y : _) -> f x y && adjAll f xs

equivalent :: [Bool] -> Bool
equivalent = adjAll (==)

ascending :: [Rel] -> Bool
ascending = adjAll (⊆)

chain :: [Bool] -> Bool
chain = adjAll (\ x y -> not x || y)

dom :: Rel -> Rel
dom r = [(x, x) | (x, _) <- r]

ran :: Rel -> Rel
ran r = [(x, x) | (_, x) <- r]

coreflexive :: Rel -> Bool
coreflexive r = r ⊆ idt

latestOnly :: Bool
latestOnly = True

check :: (HasCallStack, Testable a) => String -> a -> SpecWith (Arg Property)
check s p = it s (property p)

check' :: (HasCallStack, Testable a) => a -> SpecWith (Arg Property)
check' = check ""

lemma :: (HasCallStack, Testable a) => String -> a -> SpecWith (Arg Property)
lemma s p = it s (property p)

lemma' :: (HasCallStack, Testable a) => a -> SpecWith (Arg Property)
lemma' p = it "lemma" (property p)

proof :: (HasCallStack, Testable a) => a -> SpecWith (Arg Property)
proof p = it "proof" (property p)

main = hspec do
  describe "Category axioms" do
    check "associativity" \ r s t -> r · (s · t) =~= (r · s) · t
    check "left id" \ r -> r · idt =~= r
    check "right id" \ r -> r · idt =~= r
  describe "Allegory basics" do
    describe "Facts about meets" do
      check "universal property" \ x r s -> x ⊆ r ∩ s <=> x ⊆ r && x ⊆ s
      check "commutativity" \ r s -> r ∩ s =~= s ∩ r
      check "associativity" \ r s t -> r ∩ (s ∩ t) =~= (r ∩ s) ∩ t
      check "idempotency" \ r -> r ∩ r =~= r
    describe "Meets and inclusions" do
      check' \ r s -> r ⊆ s <=> r ∩ s =~= r
      check "comp left-distrib meet" \ r s t -> r · (s ∩ t) ⊆ (r · s) ∩ (r · t)
      check "comp right-distrib meet" \ r s t -> (r ∩ s) · t ⊆ (r · t) ∩ (s · t)
    describe "Converse" do
      check "op involution" \ r -> op (op r) =~= r
      check "op ⊆ contra"  \ r s -> r ⊆ s <=> op r ⊆ op s
      check "op comp distr"  \ r s -> op (r · s) =~= op s · op r
      check "op meet distr"  \ r s -> op (r ∩ s) =~= op r ∩ op s
    describe "Modular law" do
      let
        modularL r s t = (r · s) ∩ t ⊆ (r ∩ t · op s) · s
        modularR r s t = (r · s) ∩ t ⊆ r · (s ∩ op r · t)
        modularLR r s t = (r · s) ∩ t ⊆ (r ∩ t · op s) · (s ∩ op r · t)
      check "modular left" modularL
      check "modular right" modularR
      check "modular both" modularLR
      check "all the above are equivalent" \ r s t ->
        equivalent [modularL r s t, modularR r s t, modularLR r s t]
      lemma "useful op lemma" \ r s -> (op r · s) ∩ idt ⊆ op (r ∩ s) · (r ∩ s)
      proof \ r s -> ascending
        [ (op r · s) ∩ idt
        , (op r ∩ (idt · op s)) · (s ∩ (op (op r) · idt)) -- modular law
        , (op r ∩ op s) · (s ∩ r) -- simplification
        , op (r ∩ s) · (s ∩ r) -- op meet distrib
        ]
      lemma' \ r -> r ⊆ r · op r · r
      proof \ r -> ascending
        [ r
        , (r · idt) ∩ r
        , r · (idt ∩ (op r · r)) -- modular law
        , r · op r · r
        ]
  describe "Domain and range" do
     check' \ r -> dom r =~= ran (op r)
     check "range universal property" \ r x -> ran r ⊆ x <=> r ⊆ x · r
     check "range direct definition" \ r -> ran r =~= r · op r ∩ idt
     lemma "range left id" \ r -> r =~= ran r · r
     proof \ r -> and
       [ -- ==>
         chain
         [ r ⊆ ran r · r
         , ran r ⊆ ran r -- universal property of ran r
         ]
       , -- <==
         ascending
         [ ran r · r
         , idt · r -- ran r is coreflexive
         , r
         ]
       ]
     check "range left comp" \ r s -> ran (r · s) ⊆ ran r
     check' \ r s -> ran (r · s) =~= ran (r · ran s)
     check' \ r s -> dom (r · s) =~= dom (dom r · s)
     check "range coreflexive" \ r -> coreflexive (ran r)
     lemma "range meet" \ r s -> ran (r ∩ s) =~= idt ∩ (r · op s)
     proof \ r s -> and
       [ ascending
         [ran (r ∩ s)
         , ((r ∩ s) · op (r ∩ s)) ∩ idt -- direct range definition
         , ((r · op r) ∩ (r · op s) ∩ (s · op r) ∩ (s · op s)) ∩ idt -- distribution
         , (r · op s) ∩ idt -- monotonicity of meet
         ]
       , True
       ]
