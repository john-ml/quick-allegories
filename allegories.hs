{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
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

equivalent :: Eq a => [a] -> Bool
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

coreflexiv :: Rel -> Rel
coreflexiv = filter (uncurry (==))

reflexive :: Rel -> Bool
reflexive r = idt ⊆ r

reflexiv :: Rel -> Rel
reflexiv r = r ++ idt

transitive :: Rel -> Bool
transitive r = r · r ⊆ r

idempotent :: Rel -> Bool
idempotent r = r · r =~= r

symmetric :: Rel -> Bool
symmetric r = r ⊆ op r

symmetri :: Rel -> Rel
symmetri r = r ++ op r

antisymmetric :: Rel -> Bool
antisymmetric r = r ∩ op r ⊆ idt

simple :: Rel -> Bool
simple r = r · op r ⊆ idt

simpl :: Rel -> Rel
simpl = L.nubBy ((==) `on` fst)

entire :: Rel -> Bool
entire r = idt ⊆ op r · r

entir :: Rel -> Rel
entir = (++ idt)

funcn :: Rel -> Bool
funcn = liftM2 (&&) simple entire

func :: Rel -> Rel
func = simpl . entir

--------------------------------------------------------------------------------

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

basics = hspec do
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
      lemma "useful ran lemma" \ r s -> (op r · s) ∩ idt ⊆ op (r ∩ s) · (r ∩ s)
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
   lemma "range left comp eqn" \ r s -> ran (r · s) =~= ran (r · ran s)
   proof \ r s -> and
     [ -- ==>
       ascending
       [ ran (r · s)
       , ran (r · ran s · s) -- ran left id
       , ran (r · ran s) -- ran left comp
       ]
     , -- <==
       ascending
       [ ran (r · ran s)
       , ran (r · ((s · op s) ∩ idt)) -- defn of ran
       , ran (r · s · op s) -- monotonicity of meet
       , ran (r · s) -- ran comp left
       ]
     ]
   check' \ r s -> dom (r · s) =~= dom (dom r · s)
   check "range coreflexive" \ r -> coreflexive (ran r)
   lemma "range meet" \ r s -> ran (r ∩ s) =~= idt ∩ (r · op s)
   proof \ r s -> and
     [ ascending
       [ ran (r ∩ s)
       , ((r ∩ s) · op (r ∩ s)) ∩ idt -- direct range definition
       , (r · op s) ∩ idt -- monotonicity
       ]
     , ascending
       [ idt ∩ (r · op s)
       , (r · op s) ∩ idt ∩ idt
       , (op (op r ∩ op s) · (op r ∩ op s)) ∩ idt -- useful op lemma
       , ((r ∩ s) · op (r ∩ s)) ∩ idt
       , ran (r ∩ s) ∩ idt
       ]
     ]
  describe "Reflexivity, transitivity, etc." do
    check "reflexiv correct" \ r -> reflexive (reflexiv r)
    check "coreflexiv correct" \ r -> coreflexive (coreflexiv r)
    check "symmetri correct" \ r -> symmetric (symmetri r)
    lemma "coreflexive ==> transitive" \ (coreflexiv -> r) -> transitive r
    proof \ (coreflexiv -> r) -> ascending [r · r, r · idt, r]
    lemma "coreflexive symmetric" \ (coreflexiv -> r) -> symmetric r
    proof \ (coreflexiv -> r) -> ascending
      [ r
      , r · op r · r -- lemma from above
      , idt · op r · idt -- r ⊆ id
      , op r
      ]
    lemma "coreflexive comp = meet" \ (coreflexiv -> r) (coreflexiv -> s) -> r · s =~= r ∩ s
    proof \ (coreflexiv -> r) (coreflexiv -> s) -> and
      [ -- ==>
        and
        [ ascending [r · s, r · idt, r] -- s is coreflexive
        , r · s ⊆ s -- r is coreflexive
        ]
      , -- <==
        ascending
        [ r ∩ s
        , (r · idt) ∩ s
        , r · (idt ∩ (op r · s)) -- modular law
        , r · (idt ∩ (r · s)) -- r coreflexive ==> r = op r
        , r · r · s -- r · s coreflexive
        , r · s -- r coreflexive ==> r transitive
        ]
      ]
    lemma "coreflexive comp meet" \ (coreflexiv -> c) r s -> (c · r) ∩ s =~= c · (r ∩ s)
    proof \ (coreflexiv -> c) r s -> and
      [ -- <==
        ascending
        [ c · (r ∩ s)
        , (c · r) ∩ (c · s) -- distrib
        , (c · r) ∩ s -- c ⊆ id
        ]
      , -- ==>
        ascending
        [ (c · r) ∩ s
        , c · (r ∩ (op c · s)) -- modular law
        , c · (r ∩ c · s) -- c = op c
        , c · (r ∩ s) -- c ⊆ id
        ]
      ]
    lemma "coreflexive outside range" \ (coreflexiv -> c) r -> ran (c · r) =~= c · ran r
    check "corefl out range dual" \ (coreflexiv -> c) r -> dom (r · c) =~= dom r · c
    pure "(c ·) is a restriction. ran(restrict r) is the same as restrict(ran r)."
    proof \ (coreflexiv -> c) r -> and
      [ -- ==>
        ascending
        [ ran (c · r)
        , (c · r · op r · op c) ∩ idt -- direct defn of range
        , c · ((r · op r · op c) ∩ idt) -- coreflexive comp meet
        , c · ((r · op r) ∩ idt) -- op c coreflexive
        , c · ran r -- defn of range
        ]
      , -- <==
        ascending
        [ c · ran r
        , c · ((r · op r) ∩ idt) -- defn of range
        , (c · r · op r) ∩ idt -- corefl comp meet
        , (op c · c · r · op r) ∩ idt -- c is symmetric and transitive
        , (op c ∩ (c · r · op r)) ∩ idt -- corefl comp = meet (c · r · op r corefl b/c ran(c · ...) ⊆ ran c)
        , ((c · r · op r) · op c) ∩ idt -- corefl comp = meet
        , ran (c · r) -- defn of range
        ]
      ]
    lemma "sym trans <=>" \ r -> symmetric r && transitive r <=> r =~= r · op r
    proof \ r -> and
      [ -- ==>
        chain
        [ symmetric r && transitive r
        , equivalent
          [ r
          , r · r -- r is transitive
          , r · op r -- r is symmetric
          ]
        ]
      , -- <==
        and
        [ -- symmetry
          chain
          [ r =~= r · op r
          , op r =~= r · op r -- op both sides
          , r =~= op r
          ]
        , -- transitivity
          chain
          [ r =~= r · op r
          , r =~= r · r -- symmetry
          ]
        ]
      ]
  describe "Simple and entire arrows" do
    check "simpl correct" \ r -> simple (simpl r)
    lemma "simple modular law" \ (simpl -> s) r t -> (s · r) ∩ t =~= s · (r ∩ (op s · t))
    proof \ (simpl -> s) r t -> ascending -- suffices to show right-to-left
      [ s · (r ∩ (op s · t))
      , (s · r) ∩ (s · op s · t) -- distr
      , (s · r) ∩ (idt · t) -- s is simple
      , (s · r) ∩ t
      ]
    lemma "simple modular law (R)" \ (simpl -> s) r t -> (r · op s) ∩ t =~= (r ∩ (t · s)) · op s
    proof \ (simpl -> s) r t -> ascending
      [ (r ∩ (t · s)) · op s
      , (r · op s) ∩ (t · s · op s) -- distr
      , (r · op s) ∩ t -- s simple
      ]
    lemma "simple comp right distr meet" \ r t (simpl -> s) -> (r ∩ t) · s =~= (r · s) ∩ (t · s)
    proof \ r t (simpl -> s) -> ascending -- suffices to show right-to-left
      [ (r · s) ∩ (t · s)
      , (r ∩ (t · s · op s)) · s -- modular law
      , (r ∩ t) · s -- s simple
      ]
    check "entir correct" \ r -> entire (entir r)
    check "entire dom" \ r -> entire r <=> dom r =~= idt
    lemma "meet entire" \ r s -> entire (r ∩ s) <=> idt ⊆ op r · s
    proof \ r s -> chain
      [ entire (r ∩ s)
      , dom (r ∩ s) =~= idt
      , ran (op r ∩ op s) =~= idt -- dom = ran . op
      , idt ∩ (op r · s) =~= idt -- range meet
      , idt ⊆ op r · s -- universal property of meet
      ]
    check "func correct" \ r -> funcn (func r)
    lemma "shunting" \ (func -> f) r s -> f · r ⊆ s <=> r ⊆ op f · s
    proof \ (func -> f) r s -> chain
      [ f · r ⊆ s
      , op f · f · r ⊆ op f · s -- monotonicity of · over ⊆
      , idt · r ⊆ op f · s -- f entire
      , r ⊆ op f · s
      , f · r ⊆ f · op f · s -- monotonicity again
      , f · r ⊆ s -- f simple
      ]
    check "dual shunting" \ (func -> f) r s -> r · op f ⊆ s <=> r ⊆ s · f
    -- Note: r · f ⊆ s <=> r ⊆ s · op f does not hold (f func not necessarily imply op f func)
    lemma "func ⊆ ==> =" \ (func -> f) (func -> g) -> f ⊆ g <=> g ⊆ f
    proof \ (func -> f) (func -> g) -> equivalent -- suffices to prove one direction
      [ f ⊆ g
      , op f · f ⊆ op f · g -- shunting f
      , idt ⊆ op f · g -- f entire
      , op g ⊆ op f -- shunting g
      , g ⊆ f -- op monotonic involution
      ]
    lemma "range meet comp" \ r s t -> ran (r ∩ (s · t)) =~= ran ((r · op t) ∩ s)
    proof \ r s t -> and
      [ -- ==>
        ascending
        [ ran (r ∩ (s · t))
        , ran ((s ∩ (r · op t)) · t) -- modular
        , ran (s ∩ (r · op t)) -- range comp left
        ]
      , -- <==
        ascending
        [ ran ((r · op t) ∩ s)
        , ran ((r ∩ (s · t)) · op t) -- modular
        , ran (r ∩ (s · t)) -- range comp left
        ]
      ]
    lemma "simple left distr" \ (simpl -> f) r s -> op f · (r ∩ s) =~= (op f · r) ∩ (op f · s)
    lemma "dom func" \ r (func -> f) -> dom r · f =~= f · dom (r · f)
    -- proof: TODO
    --proof \ r (func -> f) -> and
    --  [ -- ==> 
    --    equivalent
    --    [ dom r · f ⊆ f · dom (r · f)
    --    , dom r · f ⊆ f · dom (dom r · f)
    --    , dom r · f ⊆ f · ran (op f · op (dom r))
    --    , dom r · f ⊆ f · ((op f · op (dom r) · dom r · f) ∩ idt)
    --    , ((op r · r) ∩ idt) · f ⊆ f · ((op f · op (dom r) · dom r · f) ∩ idt)
    --    , (op r · r · f) ∩ f ⊆ f · ((op f · op (dom r) · dom r · f) ∩ idt) -- f simple
    --    , (op r · r · f) ∩ f ⊆ f · ((op f · op (dom r) · dom r · f) ∩ idt) -- f simple
    --    ascending
    --    [ dom r · f
    --    , ((op r · r) ∩ idt) · f
    --    , (op r · r · f) ∩ f -- distrib
    --    ]
    --    [ dom r · f ⊆ f · dom (r · f)
    --    , op f · dom r · f ⊆ dom (r · f)
    --    , op f · ((op r · r) ∩ idt) · f ⊆ 
    --  , chain
    --    [ f · dom (r · f) ⊆ dom r · f
    --    , f · dom (r · f) · op f ⊆ dom r -- dual shunting
    --    , dom (r · f) · op f ⊆ op f · dom r -- shunting
    --    , ran (op f · op r) · op f ⊆ op f · dom r -- shunting
    --    ]
    --  ]

main = do
  basics
