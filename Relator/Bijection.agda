module Relator.Bijection {l₁} {l₂} where

import      Level as Lvl
open import Functional
open import Functional.Properties
open import Logic.Propositional{l₁ Lvl.⊔ (Lvl.𝐒 l₂)}
open import Logic.Predicate{l₁}{l₂}
open import Structure.Function.Domain{l₁}
open import Structure.Relator.Properties {l₁} {Lvl.𝐒 l₂}
open import Type{l₂}

-- TODO: Same as ∃f. Bijective(f)
data Bijection (T₁ : Type) (T₂ : Type) : Stmt where
  bijection-intro : (f : T₁ → T₂) → Bijective(f) → Bijection(T₁)(T₂)

Bijection-inverse-fn : ∀{T₁ T₂} → Bijection(T₁)(T₂) → (T₂ → T₁)
Bijection-inverse-fn(bijection-intro f ([∧]-intro injective surjective)) =
  (y ↦ [∃]-extract(surjective{y}))

-- TODO
inverse : ∀{T₁ T₂} → Bijection(T₁)(T₂) → Bijection(T₂)(T₁)
inverse{T₁}{T₂} (bijection-intro f ([∧]-intro injective surjective)) =
  bijection-intro f⁻¹ ([∧]-intro (inj f⁻¹) (surj f⁻¹)) where
    f⁻¹ = (y ↦ [∃]-extract(surjective{y}))
    postulate inj  : (f : T₂ → T₁) → Injective(f)
    postulate surj : (f : T₂ → T₁) → Surjective(f)
    -- (\{x} → [∃]-intro(f(x)))

instance
  Bijection-reflexivity : Reflexivity(Bijection)
  Bijection-reflexivity = bijection-intro(id)(id-bijective)

instance
  Bijection-symmetry : Symmetry(Bijection)
  Bijection-symmetry(bijection) = inverse(bijection)

-- TODO: Use function composition and other compositions in some way
instance
   postulate Bijection-transitivity : Transitivity(Bijection)
--   Bijection-transitivity([∧]-intro [≡]-intro [≡]-intro) = [≡]-intro
