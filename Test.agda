module Test where

open import Data
import      FFI.IO   as FFI
import      FFI.Type as FFI
open import Functional
import      Functional.Raise
import      Level as Lvl
import      List
open import Logic Lvl.𝟎
  hiding (⊥)
open import LogicTheorems Lvl.𝟎
import      NonEmptyList
import      Numeral.Integer
import      Numeral.Integer.Oper
import      Numeral.Integer.Sign
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation
import      Numeral.Natural.UnclosedOper
import      Numeral.Real
import      Numeral.Sign
import      Numeral.Sign.Oper
import      Numeral.Sign.Oper0
open import Relator.Equals Lvl.𝟎
import      Structure.Function.Domain
import      Structure.Function.Linear
import      Structure.Operator.Field
import      Structure.Operator.Group
import      Structure.Operator.Properties
import      Structure.Operator.Vector
import      Structure.Relator.Equivalence as Eq
import      Structure.Relator.Ordering
import      Structure.Relator.Properties
import      String
open import Type

ℕ4IsEven : Even((𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎))
ℕ4IsEven = Even0 ⇒ Even𝐒 ⇒ Even𝐒

ℕ5IsOdd : Odd((𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎))
ℕ5IsOdd = Odd0 ⇒ Odd𝐒 ⇒ Odd𝐒

ℕ2Dividesℕ4 : (𝐒 ∘ 𝐒)(𝟎) divides (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎)
ℕ2Dividesℕ4 = Div0 ⇒ Div𝐒 ⇒ Div𝐒

ℕ6IsDividesℕ12 : (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎) divides (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎)
ℕ6IsDividesℕ12 = Div0 ⇒ Div𝐒 ⇒ Div𝐒

ℕ4IsDividesℕ12 : (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎) divides (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎)
ℕ4IsDividesℕ12 = Div0 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒

ℕ3IsDividesℕ12 : (𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎) divides (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎)
ℕ3IsDividesℕ12 = Div0 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒

ℕ2IsDividesℕ12 : (𝐒 ∘ 𝐒)(𝟎) divides (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎)
ℕ2IsDividesℕ12 = Div0 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒

ℕ1IsDividesℕ12 : 𝐒(𝟎) divides (𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎)
ℕ1IsDividesℕ12 = Div0 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒 ⇒ Div𝐒

ℕ3IsDividesℕ7Remℕ1 : 3 divides 7 withRemainder 1
ℕ3IsDividesℕ7Remℕ1 = DivRem0 ⇒ DivRem𝐒 ⇒ DivRem𝐒

ℕ3Eqℕ2+1 : (𝐒 ∘ 𝐒 ∘ 𝐒)(𝟎) ≡ (𝐒 ∘ 𝐒)(𝟎) + 𝐒(𝟎)
ℕ3Eqℕ2+1 = [≡]-reflexivity

testImpl : 𝐒(𝟎) ≡ (𝟎 ⇒ 𝐒)
testImpl = [≡]-reflexivity

fnℕ+1 : (𝟎 ≡ 𝐒(𝟎)) → (𝐒(𝟎) ≡ (𝐒 ∘ 𝐒)(𝟎))
fnℕ+1 = [≡]-with-[ 𝐒 ]

fnℕ+3 : ∀{x} → (x ≡ 5) → (x + 3 ≡ 8)
fnℕ+3 = [≡]-with-[ (λ x → x + 3) ]

testBottom : (⊥ ∧ ℕ) → ℕ
testBottom = [∧]-elimᵣ

repeat : {R : Set} → R → (R → R) → ℕ → R
repeat x _ 𝟎 = x
repeat x f (𝐒 n) = f(repeat x f n)

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

ℕ8Eqℕ2⋅4 : 8 ≡ 2 ⋅ 4
ℕ8Eqℕ2⋅4 = [≡]-reflexivity

ℕ0Eqℕ0⋅4 : 0 ≡ 0 ⋅ 4
ℕ0Eqℕ0⋅4 = [≡]-reflexivity

-- [⨯]-equivalenceRelation : Eq.EquivalenceRelation (_⨯_)
-- [⨯]-equivalenceRelation =
--   record {
--     reflexivity = λ X → (X ⨯ X)
--   }

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
  f : ℕ
  f = (Functional.Raise.repeatᵣ 4 𝐒 (_∘_) id) 0

  testf₁ : f ≡ 4
  testf₁ = [≡]-reflexivity

-- f₂ : ∀{n}{A B C D : TypeN n} → (((A ⨯ B) ⨯ C) -> D) -> (A -> B -> C -> D)
-- f₂ = Functional.Raise.repeatᵣ 2 id (_∘_) Tuple.curry

testTupleRaise : ℕ Tuple.^ 4 → ℕ ⨯ ℕ ⨯ ℕ ⨯ ℕ
testTupleRaise x = x

main : FFI.IO FFI.Unit
main = FFI.printStrLn "Okay"
