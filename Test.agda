module Test where

open import Data
open import Functional
open import Logic
open import NaturalNumbers
import Type as T

ℕ4IsEven : Even((𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆)(ℕ0))
ℕ4IsEven = Even0 ⇒ Even𝑆 ⇒ Even𝑆

ℕ5IsOdd : Odd((𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆)(ℕ0))
ℕ5IsOdd = Odd0 ⇒ Odd𝑆 ⇒ Odd𝑆

ℕ2Dividesℕ4 : (𝑆 ∘ 𝑆)(ℕ0) divides (𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆)(ℕ0)
ℕ2Dividesℕ4 = Div0 ⇒ Div𝑆 ⇒ Div𝑆

ℕ6IsDividesℕ12 : (𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆)(ℕ0) divides (𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆)(ℕ0)
ℕ6IsDividesℕ12 = Div0 ⇒ Div𝑆 ⇒ Div𝑆

ℕ4IsDividesℕ12 : (𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆)(ℕ0) divides (𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆)(ℕ0)
ℕ4IsDividesℕ12 = Div0 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆

ℕ3IsDividesℕ12 : (𝑆 ∘ 𝑆 ∘ 𝑆)(ℕ0) divides (𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆)(ℕ0)
ℕ3IsDividesℕ12 = Div0 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆

ℕ2IsDividesℕ12 : (𝑆 ∘ 𝑆)(ℕ0) divides (𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆)(ℕ0)
ℕ2IsDividesℕ12 = Div0 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆

ℕ1IsDividesℕ12 : 𝑆(ℕ0) divides (𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆 ∘ 𝑆)(ℕ0)
ℕ1IsDividesℕ12 = Div0 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆

ℕ3IsDividesℕ7Remℕ1 : 3 divides 7 withRemainder 1
ℕ3IsDividesℕ7Remℕ1 = DivRem0 ⇒ DivRem𝑆 ⇒ DivRem𝑆

ℕ3Eqℕ2+1 : (𝑆 ∘ 𝑆 ∘ 𝑆)(ℕ0) ≡ (𝑆 ∘ 𝑆)(ℕ0) + 𝑆(ℕ0)
ℕ3Eqℕ2+1 = [≡]-reflexivity

TestImpl : 𝑆(ℕ0) ≡ (ℕ0 ⇒ 𝑆)
TestImpl = [≡]-reflexivity

Fnℕ+1 : (ℕ0 ≡ 𝑆(ℕ0)) → (𝑆(ℕ0) ≡ (𝑆 ∘ 𝑆)(ℕ0))
Fnℕ+1 = [≡]-with-[ 𝑆 ]

Fnℕ+3 : ∀ {x} → (x ≡ 5) → (x + 3 ≡ 8)
Fnℕ+3 = [≡]-with-[ (λ x → x + 3) ]

f : (⊥ ∧ ℕ) → ℕ
f = [∧]-elimᵣ

repeat : {R : Set} → R → (R → R) → ℕ → R
repeat x _ ℕ0 = x
repeat x f (𝑆 n) = f(repeat x f n)

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
