module Functional.Equals{ℓₗ} where

import      Lvl
open import Functional
open import Logic.Propositional
open import Sets.Setoid{ℓₗ}
open import Structure.Relator.Equivalence{ℓₗ}
open import Structure.Relator.Properties{ℓₗ}
open import Type

module _ {ℓ₁}{ℓ₂} {A : Type{ℓ₁}} {B : Type{ℓ₂}} ⦃ equiv-B : Equiv(B) ⦄ where
  infixl 15 _⊜_

  -- Function equivalence. When the types and all their values are shared/equivalent.
  data _⊜_ (f : A → B) (g : A → B) : Stmt{ℓₗ Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂} where
    [⊜]-intro : (∀{x} → (f(x) ≡ g(x))) → (f ⊜ g)

  instance
    [⊜]-reflexivity : Reflexivity(_⊜_)
    reflexivity ⦃ [⊜]-reflexivity ⦄ = [⊜]-intro(reflexivity)

  instance
    [⊜]-symmetry : Symmetry(_⊜_)
    symmetry ⦃ [⊜]-symmetry ⦄ ([⊜]-intro f≡g) = [⊜]-intro(symmetry(f≡g))

  instance
    [⊜]-transitivity : Transitivity(_⊜_)
    transitivity ⦃ [⊜]-transitivity ⦄ ([⊜]-intro f≡g) ([⊜]-intro g≡h) = [⊜]-intro(transitivity(f≡g)(g≡h))

  instance
    [⊜]-equivalence : Equivalence(_⊜_)
    [⊜]-equivalence = record{}

  instance
    [⊜]-equiv : Equiv(A → B)
    [⊜]-equiv = Equiv.intro(_⊜_)

  module _ ⦃ func : ∀{x} → Function(apply(x)) ⦄ where
    [⊜]-from-[≡] : ∀{f g : A → B} → (f ≡ g) → (f ⊜ g)
    [⊜]-from-[≡] {f}{g} (proof) = [⊜]-intro (\{x} → [≡]-with (apply(x)) ⦃ func ⦄ (proof))

-- TODO: Probably incorrect?
-- [≡]-inherit-property : ∀{ℓ₁}{ℓ₂} → (∀{X : Type{ℓ₂}}{Y : Type{ℓ₂}} {a₁ b₁ : X}{a₂ b₂ : Y} → (a₁ ≡ᵥ b₁) → (a₂ ≡ᵥ b₂)) → (∀{X₁ X₂ : Type{ℓ₁}}{Y₁ Y₂ : Type{ℓ₂}}{f₁ g₁ : X₁ → Y₁}{f₂ g₂ : X₂ → Y₂} → (f₁ ≡ g₁) → (f₂ ≡ g₂))
-- [≡]-inherit-property(prop) {X₁}{X₂} {Y₁}{Y₂} {f₁}{g₁} {f₂}{g₂} =
--   [≡]-intro{_}{_} {_}{_} (\{x} → prop{_}{_} {f₁(x)}{g₁(x)} {f₂(x)}{g₂(x)})
-- P : ∀{X Y} → (X , X) → (Y , Y)
