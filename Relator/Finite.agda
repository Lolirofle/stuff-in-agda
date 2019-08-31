module Relator.Finite {ℓ₁} where

import      Lvl
open import Functional
open import Functional.Proofs
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Natural
open import Structure.Function.Domain{ℓ₁}
open import Structure.Relator.Properties {ℓ₁}
open import Type

-- Definition of a finite set/type
Finite : ∀{ℓ₂} → Type{ℓ₂} → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
Finite {ℓ₂} (T) = ∃{ℓ₁ Lvl.⊔ ℓ₂}{Lvl.𝟎}{ℕ}(n ↦ (∃{ℓ₁}{ℓ₂}{T → 𝕟(n)} Injective)) -- TODO: It is probably better to define this as (∃{𝕟(n) → T} Surjective) so that one gets a finite sequence. But maybe one can prove ((∃{T → 𝕟(n)} Injective) → (∃{T → 𝕟(n)} Injective ∧ Surjective)) and then (∃{𝕟(n) → T} Surjective)? So prove that a mapping (𝕟(n) → 𝕟(m)) so that (m = #T) exists, but is that even possible?
-- TODO: Create a module Relator.Injection like Relator.Bijection
