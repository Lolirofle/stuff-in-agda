module Test where

import Automaton.DeterministicFinite
import Automaton.NonDeterministicFinite
import Automaton.Pushdown
import Automaton.TuringMachine
import Boolean
import Boolean.Theorems
import Boolean.Operators
import Data
import Data.Tuple.List
import FFI.IO   as FFI
import FFI.Type as FFI
import FormalLanguage
import FormalLanguage.ContextFreeGrammar
import FormalLanguage.Properties
import FormalLanguage.RegularExpression
import Functional
import Functional.Equals
import Functional.Raise
import Functional.PrimitiveRecursion
import Functional.Properties
import Level as Lvl
import List
import List.Properties
import List.Relation
import List.Theorems
import Logic.Classic.Propositional.ProofSystem
import Logic.Classic.Propositional.Semantics
import Logic.Classic.Propositional.Syntax
import Logic.DiagonalProof
import Logic.LambdaCalculus
import Logic.Propositional
import Logic.Predicate
import Logic.Theorems
import Numeral.Integer
import Numeral.Integer.Oper
import Numeral.Integer.Relation
import Numeral.Integer.Sign
import Numeral.Integer.Theorems
import Numeral.Natural
import Numeral.Natural.Finite
import Numeral.Natural.Function
import Numeral.Natural.BooleanOper
import Numeral.Natural.Oper
import Numeral.Natural.Oper.Properties
import Numeral.Natural.Prime
import Numeral.Natural.Relation
import Numeral.Natural.Relation.Countable
import Numeral.Natural.Relation.Properties
import Numeral.Natural.TotalOper
import Numeral.Natural.UnclosedOper
import Numeral.Real
import Numeral.Real.Properties
import Numeral.Sign
import Numeral.Sign.Oper
import Numeral.Sign.Oper0
import Operator.Equals
import Relator.Bijection
import Relator.Congruence
import Relator.Equals
import Sets.AdditiveSet
import Sets.FnSet
import Sets.ListSet
import Sets.TypeSet
import Structure.Function.Domain
import Structure.Function.Linear
import Structure.Function.Ordering
import Structure.Operator.Field
import Structure.Operator.Group
import Structure.Operator.Properties
import Structure.Operator.SetAlgebra
import Structure.Operator.Vector
import Structure.Relator.Equivalence as Eq
import Structure.Relator.Ordering
import Structure.Relator.Properties
import String
import Type

module NumAndDivisionProofs where
  open Functional
  open Logic.Propositional{Lvl.𝟎}
  open Numeral.Natural
  open Numeral.Natural.Oper
  open Numeral.Natural.Relation
  open Relator.Equals{Lvl.𝟎}{Lvl.𝟎}

  ℕ4IsEven : Even((𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎))
  ℕ4IsEven = Even0 ⇒ Even𝐒 ⇒ Even𝐒

  ℕ5IsOdd : Odd((𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎))
  ℕ5IsOdd = Odd0 ⇒ Odd𝐒 ⇒ Odd𝐒

  ℕ2Dividesℕ4 : (𝐒 ∘ 𝐒)(𝟎) divides (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎)
  ℕ2Dividesℕ4 = Div𝟎 ⇒ Div𝐒 ⇒ Div𝐒

  ℕ6IsDividesℕ12 : (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎) divides (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎)
  ℕ6IsDividesℕ12 = Div𝟎 ⇒ Div𝐒 ⇒ Div𝐒

  ℕ4IsDividesℕ12 : (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎) divides (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎)
  ℕ4IsDividesℕ12 = Div𝟎 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒

  ℕ3IsDividesℕ12 : (𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎) divides (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎)
  ℕ3IsDividesℕ12 = Div𝟎 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒

  ℕ2IsDividesℕ12 : (𝐒 ∘ 𝐒)(𝟎) divides (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎)
  ℕ2IsDividesℕ12 = Div𝟎 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒

  ℕ1IsDividesℕ12 : 𝐒(𝟎) divides (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎)
  ℕ1IsDividesℕ12 = Div𝟎 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒

  ℕ3IsDividesℕ7Remℕ1 : 3 divides 7 withRemainder 1
  ℕ3IsDividesℕ7Remℕ1 = DivRem𝟎 ⇒ DivRem𝐒 ⇒ DivRem𝐒

  ℕ3Eqℕ2+1 : (𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎) ≡ (𝐒 ∘ 𝐒)(𝟎) + 𝐒(𝟎)
  ℕ3Eqℕ2+1 = [≡]-reflexivity

  testImpl : 𝐒(𝟎) ≡ (𝟎 ⇒ 𝐒)
  testImpl = [≡]-reflexivity

  fnℕ+1 : (𝟎 ≡ 𝐒(𝟎)) → (𝐒(𝟎) ≡ (𝐒 ∘ 𝐒)(𝟎))
  fnℕ+1 = [≡]-with-[ 𝐒 ]

  fnℕ+3 : ∀{x} → (x ≡ 5) → (x + 3 ≡ 8)
  fnℕ+3 = [≡]-with-[ (x ↦ x + 3) ]

  ℕ8Eqℕ2⋅4 : 8 ≡ 2 ⋅ 4
  ℕ8Eqℕ2⋅4 = [≡]-reflexivity

  ℕ0Eqℕ0⋅4 : 0 ≡ 0 ⋅ 4
  ℕ0Eqℕ0⋅4 = [≡]-reflexivity

  testBottom : (⊥ ∧ ℕ) → ℕ
  testBottom = [∧]-elimᵣ

module DataTest where
  open Data
  open Type{Lvl.𝟎}

  data Data1 : Type where
    data1,1 : Data1

  data Data2 : Type where
    data2,1 : Data2
    data2,2 : Data2

  data Data3 : Type where
    data3,1 : Data3
    data3,2 : Data3
    data3,3 : Data3

  dataTest : (Data1 ⨯ Data2 ⨯ Data3) → Data3
  dataTest(x , y , z) = z

-- coprimes m n = ((2*m-n,m) , (2*m+n,m) , (m+2*n,n))
-- coprimes' m n = (a1/a2,b1/b2,c1/c2) where ((a1,a2),(b1,b2),(c1,c2))=f m n
-- map (\m -> map (\n -> (m,n,coprimes m n,coprimes' m n)) [1..m-1]) [1..10]

-- 2 − n/m
-- 2 + n/m
-- 2 + m/n

-- 2 − n₁/m₁ + 2 − n₂/m₂
-- 4 − n₁/m₁ − n₂/m₂
-- 4 − (m₂⋅n₁ − m₁⋅n₂)/(m₁⋅m₂)
-- 4 + (m₁⋅n₂ − m₂⋅n₁)/(m₁⋅m₂)
-- 2 + 2 + (m₁⋅n₂ − m₂⋅n₁)/(m₁⋅m₂)
-- 2 + (2⋅m₁⋅m₂)/(m₁⋅m₂) + (m₁⋅n₂ − m₂⋅n₁)/(m₁⋅m₂)
-- 2 + (2⋅m₁⋅m₂ + m₁⋅n₂ − m₂⋅n₁)/(m₁⋅m₂)

-- 1  1
-- 2  3
-- 3  6
-- 4  10
-- 5  15
-- 6  21
-- 7  28
-- 8  36
-- 9  45
-- 10 55
-- n⋅(n+1)/2 = x
-- n⋅(n+1) = 2⋅x
-- n²+n = 2⋅x
-- n = 1/2 + √(1/4+2⋅x)
-- n = 1/2 + √(9⋅x/4)
-- n = 1/2 + 3⋅√x/2
-- n = (1 + 3⋅√x)/2
-- permutation with sum 4: 1/3 2/2 3/1

-- curryN : {T : Set}{a : _} → ℕ → (a → T) → (a → T)
-- curryN 𝟎 = id
-- curryN (𝐒(n)) = Tuple.curry ∘ (curryN n)

-- test : {a b b1 c : _} → (((a , b) , b1) -> c) -> a -> b -> b1 -> c
-- test = curryN 2

-- test : {a b c d : Set} → (((a ⨯ b) ⨯ c) -> d) -> a -> b -> c -> d
-- test = Tuple.curry ∘ Tuple.curry

-- data repeatType (b : Set) : ∀{q} {a : Set q} -> a -> Set where
--   simple : repeatType b (b -> b)
--   complex : repeatType b (b -> (∀{c : Set} -> b -> c))

-- repeat2 : ∀{b d c} {q : repeatType c d} -> (r : repeatType b c) -> c -> b -> d
-- repeat2 f x simple = f (f x)
-- repeat2 f x complex = f (f x)

module TestRepeatingStuff where
  open Data
  open Numeral.Natural
  open Type

  repeat : {R : Set} → R → (R → R) → ℕ → R
  repeat x _ 𝟎 = x
  repeat x f (𝐒 n) = f(repeat x f n)

  _⨯^_ : ∀{n} → Set n → ℕ → Set n
  _⨯^_ _    𝟎      = Unit
  _⨯^_ type (𝐒(𝟎)) = type
  _⨯^_ type (𝐒(n)) = type ⨯ (type ⨯^ n)

  _→^_ : ∀{n} → Set n → ℕ → Set n
  _→^_ _    𝟎      = Unit
  _→^_ type (𝐒(𝟎)) = type
  _→^_ type (𝐒(n)) = type → (type →^ n)

  repeatOp : ∀{n} → Set n → (Set n → Set n → Set n) → ℕ → Set n
  repeatOp type _  𝟎      = type
  repeatOp type op (𝐒(n)) = op type (repeatOp type op n)

  _⨯^₂_ : ∀{n} → Set n → ℕ → Set n
  _⨯^₂_ _ 𝟎 = Unit
  _⨯^₂_ type (𝐒(n)) = repeatOp type (_⨯_) n

  testTupleRaise : ℕ Tuple.^ 4 → ℕ ⨯ ℕ ⨯ ℕ ⨯ ℕ
  testTupleRaise x = x

-- curryN : {n : ℕ} → ∀{T} → (T →^ n)

-- not mine
-- data repeatType (b : Set) : ∀{q} {a : Set q} -> a -> Set where
--   simple : repeatType b (b -> b)
--   complex : repeatType b (b -> (∀{c : Set} -> b -> c))
-- repeat2 : ∀{b d c} {q : repeatType c d} -> (r : repeatType b c) -> c -> b -> d
-- repeat2 f x simple = f (f x)
-- repeat2 f x complex = f (f x)

-- module Test1 where
--   F : (ℕ ⨯ ℕ) → ℕ
--   F(x , y) = x + y
--   f : ℕ → ℕ → ℕ
--   f = (Functional.Raise.repeatᵣ 1 Tuple.curry (_∘_) id) F
-- 
--   testf₁ : F(1 , 2) ≡ 1 + 2
--   testf₁ = [≡]-reflexivity
-- 
--   testf₂ : f 1 2 ≡ 1 + 2
--   testf₂ = [≡]-reflexivity

module Test2 where
  open Functional
  open Numeral.Natural
  open Relator.Equals{Lvl.𝟎}{Lvl.𝟎}

  f : ℕ
  f = (Functional.Raise.repeatᵣ 4 𝐒 (_∘_) id) 0

  testf₁ : f ≡ 4
  testf₁ = [≡]-reflexivity

-- f₂ : ∀{n}{A B C D : TypeN n} → (((A ⨯ B) ⨯ C) -> D) -> (A -> B -> C -> D)
-- f₂ = Functional.Raise.repeatᵣ 2 id (_∘_) Tuple.curry

module TestTypeAscription where
  open Numeral.Natural
  open Type{Lvl.𝟎}

  ty = 1 :of: ℕ
  -- ty2 = 1 :of: ⊥


-- Testing universes
module TestSetUniverses {n} (Type : Set n) where
  postulate _→₂_ : Type → Type → Set n
  data TestData1 (A : Type) (B : Type) : Set n where
  -- data TestData2 (A : Type) (B : Type) : Type where -- Data of arbitrary type seems to not be okay
  data TestData3 (A : Type) (B : Type) : Set n where
    testConstruct1 : TestData3 A B
    -- testConstruct2 : A → TestData3 A B -- Because of (_→_ : (Set _) → (Set _))?
    -- testConstruct3 : A →₂ (TestData3 A B)
    testConstruct4 : (A →₂ B) → (TestData3 A B)
  testFn : Type → Type
  testFn x = x

module testEqProof where
  open Logic.Propositional{Lvl.𝟎}
  open Numeral.Natural.Oper
  open Relator.Equals{Lvl.𝟎}{Lvl.𝟎}
  open Structure.Operator.Properties{Lvl.𝟎}
  open Type{Lvl.𝟎}

  minSkit : {{_ : Absorberₗ (_⋅_) (0)}} → {{_ : Identityᵣ (_+_) (0)}} → ∀{x} → (1 ≡ ((0 ⋅ x) + 1) + 0)
  minSkit {{absorb}} {{id}} {x} =
    ([≡]-transitivity([∧]-intro
      (([≡]-with-[(_+ 1)]
        (([≡]-symmetry (absorb {x})) :of: (0 ≡ 0 ⋅ x))
      ) :of: (1 ≡ (0 ⋅ x) + 1))
      (([≡]-symmetry id) :of: (_ ≡ ((0 ⋅ x) + 1) + 0))
    ))

module testDiv where
  open Numeral.Natural.Oper
  open Numeral.Natural.UnclosedOper
  open Relator.Equals{Lvl.𝟎}{Lvl.𝟎}

  testDiv1 : 4 ⌈/₀⌉ 2 ≡ 2
  testDiv1 = [≡]-reflexivity

  testDiv2 : 2 ⌈/₀⌉ 2 ≡ 1
  testDiv2 = [≡]-reflexivity

  testDiv3 : 1 ⌈/₀⌉ 2 ≡ 1
  testDiv3 = [≡]-reflexivity

  -- test1 : ∀{f : ℕ → ℕ} → (f(0) ≡ 0) ∧ (∀{n : ℕ} → f(n + 1) ≡ f(n) + n + 1) → (∀{n : ℕ} → f(n) ≡ (n ⋅ (n + 1)) ⌈/₀⌉ 2)
  -- test1 ()

module testList where
  open List
  open Relator.Equals{Lvl.𝟎}{Lvl.𝟎}

  -- rev1 : (4 ⊰ 3 ⊰ 2 ⊰ 1 ⊰ ∅) → reverse(1 ⊰ 2 ⊰ 3 ⊰ 4 ⊰ ∅)
  -- rev1 = id

  len1 : length(1 ⊰ 2 ⊰ 3 ⊰ 4 ⊰ ∅) ≡ 4
  len1 = [≡]-intro

  testFoldᵣ : (foldᵣ (_⊰_) ∅ (1 ⊰ 2 ⊰ 3 ⊰ 4 ⊰ ∅)) ≡ (1 ⊰ 2 ⊰ 3 ⊰ 4 ⊰ ∅)
  testFoldᵣ = [≡]-intro

  testReduceOrᵣ0 : (reduceOrᵣ (_++_) (0 ⊰ ∅) ∅) ≡ (0 ⊰ ∅)
  testReduceOrᵣ0 = [≡]-intro

  testReduceOrᵣ1 : (reduceOrᵣ (_++_) (0 ⊰ ∅) ((1 ⊰ ∅) ⊰ ∅)) ≡ (1 ⊰ ∅)
  testReduceOrᵣ1 = [≡]-intro

  testReduceOrᵣ2 : (reduceOrᵣ (_++_) (0 ⊰ ∅) ((1 ⊰ ∅) ⊰ (2 ⊰ ∅) ⊰ (3 ⊰ ∅) ⊰ (4 ⊰ ∅) ⊰ ∅)) ≡ (1 ⊰ 2 ⊰ 3 ⊰ 4 ⊰ ∅)
  testReduceOrᵣ2 = [≡]-intro

module testTransitivity where
  open Numeral.Natural
  open Structure.Relator.Properties{Lvl.𝟎}{Lvl.𝟎}
  open Relator.Equals{Lvl.𝟎}{Lvl.𝟎}

  test1 : (0 ≡ 1) → (1 ≡ 2) → (0 ≡ 2)
  test1 (0≡1) (1≡2) = _🝖_ {_}{_≡_} {{[≡]-transitivity}} (0≡1) (1≡2)

main : FFI.IO FFI.Unit
main = FFI.printStrLn "Okay"

-- module testPropositionalLogic where
--   open Functional
--   open Logic.Propositional{Lvl.𝟎}
--   module Propositional = Logic.Classic.Propositional
--   open Type{Lvl.𝟎}
-- 
--   symbols : ∀{T : Set(Lvl.𝟎)} → Propositional.Syntax.Symbols T (const (Set(Lvl.𝟎)))
--   symbols =
--     record {
--       •_ = type-of ;
--       ⊤   = ⊤ ;
--       ⊥   = ⊥ ;
--       ¬_  = ¬_ ;
--       _∧_ = _∧_ ;
--       _∨_ = _∨_ ;
--       _⇒_ = _→ᶠ_ ;
--       _⇔_ = _↔_
--       -- _⊕_ = a ↦ b ↦ ((a ∨ b) ∧ ¬(a ∧ b))
--     }

module testListOrderedContainment where
  open Functional
  open Numeral.Natural
  open List
  open List.Theorems{Lvl.𝟎}{Lvl.𝟎}
  open List.Theorems.OrderedContainment hiding (_contains-in-order_)

  test1 : ([ 1 ]) contains-in-order ([ 1 ])
  test1 = use(empty)

  test2 : ([ 1 ⊰ 2 ]) contains-in-order ([ 1 ])
  test2 = (use ∘ skip)(empty)

  test3 : ([ 1 ⊰ 2 ]) contains-in-order ([ 1 ⊰ 2 ])
  test3 = (use ∘ use)(empty)

  test4 : ([ 1 ⊰ 10 ⊰ 2 ]) contains-in-order ([ 1 ⊰ 2 ])
  test4 = (use ∘ skip ∘ use)(empty)

  test5 : ([ 1 ⊰ 10 ⊰ 2 ⊰ 3 ]) contains-in-order ([ 1 ⊰ 2 ⊰ 3 ])
  test5 = (use ∘ skip ∘ use ∘ use)(empty)

  test6 : ([ 1 ⊰ 10 ⊰ 2 ⊰ 3 ⊰ 20 ⊰ 30 ⊰ 4 ⊰ 40 ]) contains-in-order ([ 1 ⊰ 2 ⊰ 3 ⊰ 4 ])
  test6 = (use ∘ skip ∘ use ∘ use ∘ skip ∘ skip ∘ use ∘ skip)(empty)

module testPrimitiveRecursiveDefinitions where
  open   Data
  open   Functional.PrimitiveRecursion
  open   Functional.PrimitiveRecursion.OperShortcut
  open   Numeral.Natural
  import Numeral.Natural.Oper     as Nat
  import Numeral.Natural.Function as Nat
  open   Relator.Equals{Lvl.𝟎}{Lvl.𝟎}

  plus   = Rec(2) (P(1)(0)) (Comp(1)(3) (Succ) (P(3)(1)))
  pred   = Rec(1) (Zero) (P(2)(0))
  monus  = Comp(2)(2) (Rec(2) (P(1)(0)) (Comp(1)(3) (pred) (P(3)(1)))) (P(2)(1) , P(2)(0))
  max    = Comp(2)(2) (plus) (P(2)(0) , Comp(2)(2) (monus) (P(2)(1) , P(2)(0)))
  min    = Comp(2)(2) (monus) (plus , max)
  iszero = Rec(1) (Comp(1)(0) (Succ) (Zero)) (Comp(0)(2) (Zero) <>)
  const3 = Comp(1)(0) (Succ) (Comp(1)(0) (Succ) (Comp(1)(0) (Succ) (Zero)))

  -- testPlus1 : evaluate plus(4 , 2) ≡ 6
  -- testPlus1 = [≡]-intro

  -- testMonus1 : evaluate monus(4 , 0) ≡ 4
  -- testMonus1 = [≡]-intro

  -- testMonus2 : evaluate monus(0 , 4) ≡ 0
  -- testMonus2 = [≡]-intro

  -- testMonus3 : evaluate monus(10 , 2) ≡ 8
  -- testMonus3 = [≡]-intro

  -- testMonus4 : evaluate monus(2 , 10) ≡ 0
  -- testMonus4 = [≡]-intro

  -- testMin1 : evaluate min(3 , 2) ≡ Nat.min(3)(2)
  -- testMin1 = [≡]-intro

  proofPred : ∀{n} → evaluate pred(n) ≡ 𝐏(n)
  proofPred{𝟎}    = [≡]-intro
  proofPred{𝐒(n)} = [≡]-intro

  proofPlus : ∀{a b} → evaluate plus(b , a) ≡ (a Nat.+ b)
  proofPlus{𝟎}   {𝟎}    = [≡]-intro
  proofPlus{𝐒(_)}{𝟎}    = [≡]-intro
  proofPlus{a}   {𝐒(b)} = [≡]-with-[ 𝐒 ] (proofPlus{a}{b})

  is-zero : ℕ → ℕ
  is-zero(0) = 1
  is-zero(_) = 0

  proofIsZero : ∀{n} → evaluate iszero(n) ≡ is-zero(n)
  proofIsZero{𝟎}    = [≡]-intro
  proofIsZero{𝐒(_)} = [≡]-intro

  proofMonus : ∀{a} → evaluate monus(a , 𝟎) ≡ (a Nat.−₀ 𝟎)
  proofMonus{𝟎} = [≡]-intro
  proofMonus{_} = [≡]-intro

  proofMax : ∀{a} → evaluate max(0 , a) ≡ Nat.max(a)(0)
  proofMax{𝟎}    = [≡]-intro
  proofMax{𝐒(_)} = [≡]-intro

  -- proofMin : ∀{a} → evaluate min(0 , a) ≡ Nat.min(a)(0)
  -- proofMin{𝟎}    = [≡]-intro
  -- proofMin{𝐒(_)} = [≡]-intro

module testEq where
  -- testEqInstance : ∀{T} {{_ : Equivalence {T} (_≡_ {T})}} → Symmetry {T} (_≡_ {T})
  -- testEqInstance {{eq}} = Equivalence.symmetry eq
  -- testEqInstance2 : ∀{T} → Symmetry {T} (_≡_ {T})
  -- testEqInstance2 = testEqInstance

  -- testSymInstance : ∀{T} {{_ : Symmetry {T} (_≡_ {T})}} → Symmetry {T} (_≡_ {T})
  -- testSymInstance {{sym}} = sym

module testExistential where
  -- TODO
  -- testExists : ∀{T : Type}{f : T → Type} → (∃[ x ∈ T ] (f x)) → (∃ {T} (x ↦ f x))
  -- testExists x = x

module testCantor where
  open Boolean
  open Boolean.Operators.Programming
  open Functional
  open Logic.Propositional{Lvl.𝟎}
  open Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
  open Logic.DiagonalProof{Lvl.𝟎}{Lvl.𝟎}
  open Numeral.Natural
  open Numeral.Natural.Relation.Countable{Lvl.𝟎}{Lvl.𝟎}
  open Relator.Bijection{Lvl.𝟎}{Lvl.𝟎}
  open Relator.Equals {Lvl.𝟎}{Lvl.𝟎}
  open Type{Lvl.𝟎}

  BitSequence           = (ℕ → Bool)
  CountableBitSequences = (ℕ → BitSequence)

  -- ∀l∃seq∀n. l(n)(n)≠seq(n)
  -- There is a bit sequence that is not in the countable list of bit sequences
  bitSequenceCantor : (l : CountableBitSequences) → ∃{BitSequence}(seq ↦ ∀{n : ℕ} → (l(n)(n) ≢ seq(n)))
  bitSequenceCantor = diagonal-proof (!_) ([!]-unequality) where
    [!]-unequality : ∀{b : Bool} → (b ≢ ! b)
    [!]-unequality {𝑇} ()
    [!]-unequality {𝐹} ()

  -- uncountableProof : CountableBitSequences → ¬(Countable(BitSequence))
  -- uncountableProof (l) ([∃]-intro(seq-to-n)(inj)) =
  --   [∃]-elim f (bitSequenceCantor(l)) where
  --     postulate f : ∀{seq}{x : ℕ → Bool} → {n : ℕ} → (l n n ≢ x n) → ⊥ -- ∀{T}{seq}{n : ℕ} → (l(n)(n) ≢ seq(n)) → T
  --     f : ∀{_}{_}(₎
  --     f{_}{n}(lnn≢seqn) = lnn≢seqn ∘ inj
  -- Countable: ∃(seq-to-n: (ℕ → Bool) → ℕ)∀(x₁ : ℕ → Bool)∀(x₂: ℕ → Bool). (seq-to-n(seq₁)=seq-to-n(seq₂)) → (seq₁=seq₂)

module testListSets where
  open Functional
  open List
  open Sets.ListSet{Lvl.𝟎}
  open Sets.ListSet.[∈]-proof
  open Logic.Propositional
  open Type{Lvl.𝟎}

  -- TODO: Probably incorrectly formulated
  -- Example:
  --   (∀a. a∈{P,Q} → R)
  --   P → Q → R
  -- [∈]-list : ∀{L : List(Type)}{Out : Type} → (∀{a} → (a ∈ L) → Out) → (foldᵣ (_→ᶠ_) (Out) (L))
  -- [∈]-list{∅}(f) = f ∘ [⊥]-elim ∘ [∉]-empty
  -- f            : ∀{a} → (a ∈ ∅) → Out
  -- f ∘ [⊥]-elim : ⊥ → Out

  -- [∈]-list : ∀{L : List(Type)}{Out : Type} → (foldᵣ (_→ᶠ_) (Out) (L)) → (∀{a} → (a ∈ L) → Out)
  -- [∈]-list{∅}     (out) (a∈∅)   = out
  -- [∈]-list{x ⊰ l} (f)   (a∈x⊰l) = [∈]-list{l} (f)


module testFinite where
  open Numeral.Natural.Finite

  test2-0 : Finite-ℕ(2)
  test2-0 = Finite-𝟎

  test2-1 : Finite-ℕ(2)
  test2-1 = Finite-𝐒(Finite-𝟎)

  test2-2 : Finite-ℕ(2)
  test2-2 = Finite-𝐒(Finite-𝐒(Finite-𝟎))

  -- test2-3 : Finite-ℕ(2)
  -- test2-3 = Finite-𝐒(Finite-𝐒(Finite-𝐒(Finite-𝟎)))

  -- test2-4 : Finite-ℕ(2)
  -- test2-4 = Finite-𝐒(Finite-𝐒(Finite-𝐒(Finite-𝐒(Finite-𝟎))))

module testResolveInstance where
  open Functional
  open List

  data _∈_ {T : Set} (x : T) : List(T) → Set where
    instance
      𝟎 : ∀{l} → x ∈ (x ⊰ l)
      𝐒 : ∀{l}{y} → (x ∈ l) → (x ∈ (y ⊰ l))

  test1 : (2 ∈ 1 ⊰ 2 ⊰ 3 ⊰ 4 ⊰ ∅)
  test1 = resolve-instance(_)  -- Becomes 𝐒(𝐒(𝟎))
