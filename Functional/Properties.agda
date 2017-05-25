module Functional.Properties {l₁} {l₂} where

import      Level as Lvl
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Logic.Predicate{l₁}{l₂}
open import Functional
open import Relator.Equals{l₁}{l₂}
open import Structure.Function.Domain {l₁} {l₂}
open import Type

id-injective : ∀{T} → Injective(id{l₂}{T})
id-injective [≡]-intro = [≡]-intro

-- TODO: Why does this not work?
-- id-surjective : ∀{T} → Surjective(id{_}{T})
-- id-surjective {y} = [∃]-intro (y) ([≡]-intro)
