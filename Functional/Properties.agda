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

[∘]-associativity : ∀{a b c d : Type}{f : a → b}{g : b → c}{h : c → d} → ((h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f))
[∘]-associativity = [≡]-intro

[∘]-identityₗ : ∀{a b : Type}{f : a → b} → (id ∘ f ≡ f)
[∘]-identityₗ = [≡]-intro

[∘]-identityᵣ : ∀{a b : Type}{f : a → b} → (f ∘ id ≡ f)
[∘]-identityᵣ = [≡]-intro

postulate [∘]-inverseₗ : ∀{a b}{f : a → b} → ⦃ _ : Bijective(f) ⦄ → ∃(g ↦ g ∘ f ≡ id)
postulate [∘]-inverseᵣ : ∀{a b}{f : a → b} → ⦃ _ : Bijective(f) ⦄ → ∃(g ↦ f ∘ g ≡ id)

inv-fnₗ : ∀{a b} → (f : a → b) → ⦃ _ : Bijective(f) ⦄ → (b → a)
inv-fnₗ (f) = [∃]-extract([∘]-inverseₗ{_}{_}{f})

inv-fnᵣ : ∀{a b} → (f : a → b) → ⦃ _ : Bijective(f) ⦄ → (b → a)
inv-fnᵣ (f) = [∃]-extract([∘]-inverseᵣ{_}{_}{f})

inv-fn : ∀{a} → (f : a → a) → ⦃ _ : Bijective(f) ⦄ → (a → a)
inv-fn = inv-fnₗ
