module Data.ListSized.Proofs where

import      Lvl
open import Data.ListSized
open import Data.ListSized.Functions
open import Functional
open import Function.Equals
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Function
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A A₁ A₂ B B₁ B₂ C C₁ C₂ Result : Type{ℓ}
private variable a b n n₁ n₂ : ℕ
private variable f : B → C
private variable g : A → B
private variable l l₁ l₂ : List(T)(n)
private variable x : T

map-id : (map{A = A}{n = n} id ⊜ id)
_⊜_.proof map-id {∅}     = reflexivity(_≡_)
_⊜_.proof map-id {x ⊰ l} = congruence₂ᵣ(_⊰_)(_) (_⊜_.proof map-id {l})

map-[∘] : (map{n = n} (f ∘ g) ⊜ (map f) ∘ (map g))
_⊜_.proof map-[∘] {∅}     = reflexivity(_≡_)
_⊜_.proof map-[∘] {x ⊰ l} = congruence₂ᵣ(_⊰_)(_) (_⊜_.proof map-[∘] {l})

map-[++] : map f(l₁ ++ l₂) ≡ map f(l₁) ++ map f(l₂)
map-[++] {l₁ = ∅}       = reflexivity(_≡_)
map-[++] {l₁ = x₁ ⊰ l₁} = congruence₂ᵣ(_⊰_)(_) (map-[++] {l₁ = l₁})

map-repeat : map f(repeat x n) ≡ repeat (f(x)) n
map-repeat {n = 𝟎}   = reflexivity(_≡_)
map-repeat {n = 𝐒 n} = congruence₂ᵣ(_⊰_)(_) (map-repeat {n = n})

[+][++]-repeat : repeat x (n₁ + n₂) ≡ repeat x n₁ ++ repeat x n₂
[+][++]-repeat {n₁ = 𝟎}    = reflexivity(_≡_)
[+][++]-repeat {n₁ = 𝐒 n₁} = congruence₂ᵣ(_⊰_)(_) ([+][++]-repeat {n₁ = n₁})
