module Test where

open import Data
open import Functional
import      Functional.Raise
open import IO
open import Logic
open import LogicTheorems
import      Numeral.Integer
import      Numeral.Integer.Oper
import      Numeral.Integer.Sign
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation
import      Numeral.Natural.UnclosedOper
import      Numeral.Sign
import      Type as T

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

TestImpl : 𝐒(𝟎) ≡ (𝟎 ⇒ 𝐒)
TestImpl = [≡]-reflexivity

Fnℕ+1 : (𝟎 ≡ 𝐒(𝟎)) → (𝐒(𝟎) ≡ (𝐒 ∘ 𝐒)(𝟎))
Fnℕ+1 = [≡]-with-[ 𝐒 ]

Fnℕ+3 : ∀ {x} → (x ≡ 5) → (x + 3 ≡ 8)
Fnℕ+3 = [≡]-with-[ (λ x → x + 3) ]

f : (⊥ ∧ ℕ) → ℕ
f = [∧]-elimᵣ

repeat : {R : Set} → R → (R → R) → ℕ → R
repeat x _ 𝟎 = x
repeat x f (𝐒 n) = f(repeat x f n)

data Data1 : T.Type where
  data1,1 : Data1

data Data2 : T.Type where
  data2,1 : Data2
  data2,2 : Data2

data Data3 : T.Type where
  data3,1 : Data3
  data3,2 : Data3
  data3,3 : Data3

dataTest : (Data1 ⨯ Data2 ⨯ Data3) → Data3
dataTest(x , y , z) = z
