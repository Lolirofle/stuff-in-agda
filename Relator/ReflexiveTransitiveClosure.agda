open import Type

module Relator.ReflexiveTransitiveClosure {ℓ₁ ℓ₂} {T : Type{ℓ₁}} (_▫_ : T → T → Type{ℓ₂}) where

import      Lvl
open import Logic.Propositional
import      Structure.Relator.Names as Names

-- Reflexive closure of a relation.
-- Constructs a reflexive relation from an existing relation.
-- Sometimes also notated ((_▫_) ∪ (_▫⁰_)) for a relation (_▫_).
data ReflexiveClosure : T → T → Type{ℓ₁ Lvl.⊔ ℓ₂} where
  super : Names.Sub₂(_▫_)(ReflexiveClosure)
  refl  : Names.Reflexivity(ReflexiveClosure)

-- Symmetric closure of a relation.
-- Constructs a symmetric relation from an existing relation.
-- Sometimes also notated (_▫⁻¹_) or (Converse(_▫_) ∪ (_▫_)) for a relation (_▫_).
SymmetricClosure : T → T → Type{ℓ₂}
SymmetricClosure a b = (b ▫ a) ∨ (a ▫ b)

-- Reflexive-transitive closure of a relation.
-- Constructs a reflexive and transitive relation from an existing relation.
-- Sometimes also notated (_▫*_) for a relation (_▫_).
data ReflexiveTransitiveClosure : T → T → Type{ℓ₁ Lvl.⊔ ℓ₂} where
  super : Names.Sub₂(_▫_)(ReflexiveTransitiveClosure)
  refl  : Names.Reflexivity(ReflexiveTransitiveClosure)
  trans : Names.Transitivity(ReflexiveTransitiveClosure)
infixl 1000 trans

-- Transitive closure of a relation.
-- Constructs a transitive relation from an existing relation.
-- Sometimes also notated (_▫⁺_) for a relation (_▫_).
data TransitiveClosure : T → T → Type{ℓ₁ Lvl.⊔ ℓ₂} where
  super : Names.Sub₂(_▫_)(TransitiveClosure)
  trans : Names.Transitivity(TransitiveClosure)

module _ where
  open import Numeral.Natural

  -- Sometimes also notated (_▫ⁿ_) for a relation (_▫_).
  data FiniteTransitiveClosure : ℕ → T → T → Type{ℓ₁ Lvl.⊔ ℓ₂} where
    base : ∀{a} → (a ▫ a) → (FiniteTransitiveClosure 𝟎 a a)
    step : ∀{a b c} → (a ▫ b) → ∀{n} → (FiniteTransitiveClosure n b c) → (FiniteTransitiveClosure (𝐒(n)) a c)
