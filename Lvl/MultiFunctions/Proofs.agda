module Lvl.MultiFunctions.Proofs where

open import Data
open import Lvl hiding (𝐒)
open import Lvl.MultiFunctions
open import Data.Tuple.Raise
open import Data.Tuple.Raiseᵣ.Functions
open import Lvl.MultiFunctions
open import Numeral.Natural
open import Relator.Equals
open import Syntax.Number

max-repeat : ∀{n}{ℓ} → ((ℓ ⊔ (⨆(repeat n ℓ))) ≡ ℓ)
max-repeat {n = 0}       = [≡]-intro
max-repeat {n = 1}       = [≡]-intro
max-repeat {n = 𝐒(𝐒(n))} = max-repeat {n = 𝐒(n)}

{- TODO: Is this possible?

open import Relator.Equals.Proofs
test2 : ∀{a b} → (eq : a ≡ b) → ([≡]-substitutionᵣ eq {\n → Set(n)} (Set(a)) ≡ Set(b))

test2 : ∀{a b} → (a ≡ b) → (Set(a) ≡ Set(b))

postulate ℓ : Level
postulate n : ℕ
postulate s : Set(ℓ ⊔ (⨆{n} (repeat n ℓ)))
postulate p : Set(ℓ) → Set

want : Set
want rewrite max-repeat{n}{ℓ} = p s
-}
