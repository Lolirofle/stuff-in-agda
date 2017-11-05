module Functional.Properties {ℓ₁} {ℓ₂} where

import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Functional
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Relator.Equals.Theorems{ℓ₁}{ℓ₂}
open import Structure.Function.Domain {ℓ₁}
open import Type

id-injective : ∀{T} → Injective(id{ℓ₂}{T})
id-injective [≡]-intro = [≡]-intro

id-surjective : ∀{T} → Surjective(id{_}{T})
id-surjective {_}{y} = [∃]-intro (y) ([≡]-intro)

id-bijective : ∀{T} → Bijective(id{_}{T})
id-bijective = [∧]-intro(id-injective)(id-surjective)
