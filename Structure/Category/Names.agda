module Structure.Category.Names where

import      Lvl
open import Functional using (const ; swap)
open import Logic
open import Sets.Setoid
import      Structure.Operator.Names as Names
import      Structure.Relator.Names as Names
open import Type

private variable ℓₒ ℓₘ : Lvl.Level
private variable Obj : Type{ℓₒ}
private variable x y z w : Obj

-- Obj is the collection of objects.
-- _⟶_ is the collection of morphisms.
module _ (Morphism : Obj → Obj → Type{ℓₘ}) where
  -- A morphism is an endomorphism when the domain and the codomain are equal.
  -- Something which morphs itself (referring to the object).
  Endomorphism : Obj → Stmt{ℓₘ}
  Endomorphism a = Morphism a a

  module ArrowNotation where
    _⟶_ : Obj → Obj → Type{ℓₘ}
    _⟶_ = Morphism

    -- Reversed arrow
    _⟵_ : Obj → Obj → Type{ℓₘ}
    _⟵_ = swap(_⟶_)

    -- Self-pointing arrow
    ⟲_ : Obj → Type{ℓₘ}
    ⟲_ = Endomorphism

module Morphism where
  module _ (Morphism : Obj → Obj → Type{ℓₘ}) where
    open ArrowNotation(Morphism)

    -- The domain of a morphism
    dom : ∀{x y : Obj} → Morphism(x)(y) → Obj
    dom{x}{_} (_) = x

    -- The codomain of a morphism
    codom : ∀{x y : Obj} → Morphism(x)(y) → Obj
    codom{_}{y} (_) = y

  module _ {Morphism : Obj → Obj → Type{ℓₘ}} ⦃ equiv-morphism : ∀{x y} → Equiv(Morphism x y) ⦄ where
    open ArrowNotation(Morphism)

    module _ (_▫_ : Names.SwappedTransitivity(_⟶_)) where
      Associativity : Stmt
      Associativity = ∀{x y z w : Obj} → Names.AssociativityPattern {T₁ = z ⟶ w} {T₂ = y ⟶ z} {T₃ = x ⟶ y} (_▫_)(_▫_)(_▫_)(_▫_)

      module _ (id : Names.Reflexivity(_⟶_)) where
        Identityₗ : Stmt
        Identityₗ = ∀{x y}{f : x ⟶ y} → (id ▫ f ≡ f)

        Identityᵣ : Stmt
        Identityᵣ = ∀{x y}{f : x ⟶ y} → (f ▫ id ≡ f)

        Inverseₗ : ∀{x y} → (x ⟶ y) → (y ⟶ x) → Stmt
        Inverseₗ(f)(f⁻¹) = (f⁻¹ ▫ f ≡ id)

        Inverseᵣ : ∀{x y} → (x ⟶ y) → (y ⟶ x) → Stmt
        Inverseᵣ(f)(f⁻¹) = (f ▫ f⁻¹ ≡ id)
