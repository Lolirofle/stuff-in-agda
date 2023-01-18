module Data.UniqueList where

open import Data
open import Logic.Propositional
import      Lvl
open import Structure.Relator.Apartness
open import Type

private variable ℓ ℓₙₑ : Lvl.Level
private variable T : Type{ℓ}

-- A list type without duplicates (when using a correct apartness (inequality) relation)
data UniqueList(T : Type{ℓ}) ⦃ apart : Apart{ℓₙₑ}(T) ⦄ : Type{ℓ Lvl.⊔ ℓₙₑ}
_∉_ : ⦃ apart : Apart{ℓₙₑ}(T) ⦄ → T → UniqueList(T) → Type{ℓₙₑ}

data UniqueList T where
  ∅   : UniqueList(T)
  _⊰_ : (x : T) → (l : UniqueList(T)) → ⦃ x ∉ l ⦄ → UniqueList(T)

x ∉ ∅       = Unit
x ∉ (y ⊰ l) = (x # y) ∧ (x ∉ l)

open import Structure.Setoid

private variable ℓₑ : Lvl.Level

_∈_ : ∀ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ apart : Apart{ℓₙₑ}(T) ⦄ → T → UniqueList(T) → Type{ℓₑ}
x ∈ ∅       = Empty
x ∈ (y ⊰ l) = (x ≡ y) ∨ (x ∈ l)

{-
open import Type.Properties.MereProposition
open import Type.Properties.MereProposition.Proofs

[∉]-prop : ∀ ⦃ apart : Apart{ℓₙₑ}(T) ⦄ ⦃ [#]-equiv : ∀{x y : T} → Equiv{ℓₑ}(x # y) ⦄ ⦃ [∉]-equiv : ∀{x : T}{l : UniqueList(T)} → Equiv{ℓₑ}(x ∉ l) ⦄ → (∀{x y : T} → MereProposition(x # y) ⦃ [#]-equiv ⦄) → (∀{x : T}{l : UniqueList(T)} → MereProposition(x ∉ l) ⦃ [∉]-equiv ⦄)
[∉]-prop p {l = ∅} = {!!}
[∉]-prop p {l = x ⊰ l} = {!!}
-}
