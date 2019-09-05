module Functional.Equals where

import      Lvl
open import Functional
import      Functional.Names as Names
open import Logic
open import Logic.Propositional
open import Sets.Setoid
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

module _ {ℓ₁}{ℓ₂} {A : Type{ℓ₁}} {B : Type{ℓ₂}} ⦃ equiv-B : Equiv(B) ⦄ where
  infixl 15 _⊜_

  -- Function equivalence. When the types and all their values are shared/equivalent.
  data _⊜_ (f : A → B) (g : A → B) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    [⊜]-intro : (f Names.⊜ g) → (f ⊜ g)

  instance
    [⊜]-reflexivity : Reflexivity(_⊜_)
    Reflexivity.proof([⊜]-reflexivity) = [⊜]-intro(reflexivity(_≡_))

  instance
    [⊜]-symmetry : Symmetry(_⊜_)
    Symmetry.proof([⊜]-symmetry) ([⊜]-intro f≡g) = [⊜]-intro(symmetry(_≡_)(f≡g))

  instance
    [⊜]-transitivity : Transitivity(_⊜_)
    Transitivity.proof([⊜]-transitivity) ([⊜]-intro f≡g) ([⊜]-intro g≡h) = [⊜]-intro(transitivity(_≡_)(f≡g)(g≡h))

  instance
    [⊜]-equivalence : Equivalence(_⊜_)
    [⊜]-equivalence = record{}

  instance
    [⊜]-equiv : Equiv(A → B)
    [⊜]-equiv = Equiv.intro(_⊜_) ⦃ [⊜]-equivalence ⦄

-- TODO: Probably incorrect?
-- [≡]-inherit-property : ∀{ℓ₁}{ℓ₂} → (∀{X : Type{ℓ₂}}{Y : Type{ℓ₂}} {a₁ b₁ : X}{a₂ b₂ : Y} → (a₁ ≡ᵥ b₁) → (a₂ ≡ᵥ b₂)) → (∀{X₁ X₂ : Type{ℓ₁}}{Y₁ Y₂ : Type{ℓ₂}}{f₁ g₁ : X₁ → Y₁}{f₂ g₂ : X₂ → Y₂} → (f₁ ≡ g₁) → (f₂ ≡ g₂))
-- [≡]-inherit-property(prop) {X₁}{X₂} {Y₁}{Y₂} {f₁}{g₁} {f₂}{g₂} =
--   [≡]-intro{_}{_} {_}{_} (\{x} → prop{_}{_} {f₁(x)}{g₁(x)} {f₂(x)}{g₂(x)})
-- P : ∀{X Y} → (X , X) → (Y , Y)
