open import Type

module Relator.ReflexiveTransitiveClosure {ℓ₁ ℓ₂} {T : Type{ℓ₁}} (_▫_ : T → T → Type{ℓ₂}) where

open import Graph.Walk
open import Graph.Walk.Proofs
import      Lvl
open import Logic
open import Logic.Propositional
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Function

-- Reflexive closure of a relation.
-- Constructs a reflexive relation from an existing relation.
-- Sometimes also notated ((_▫_) ∪ (_▫⁰_)) for a relation (_▫_).
data ReflexiveClosure : T → T → Type{ℓ₁ Lvl.⊔ ℓ₂} where
  super : Names.Subrelation(_▫_)(ReflexiveClosure)
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
  super : Names.Subrelation(_▫_)(ReflexiveTransitiveClosure)
  refl  : Names.Reflexivity(ReflexiveTransitiveClosure)
  trans : Names.Transitivity(ReflexiveTransitiveClosure)

-- Transitive closure of a relation.
-- Constructs a transitive relation from an existing relation.
-- Sometimes also notated (_▫⁺_) for a relation (_▫_).
data TransitiveClosure : T → T → Type{ℓ₁ Lvl.⊔ ℓ₂} where
  super : Names.Subrelation(_▫_)(TransitiveClosure)
  trans : Names.Transitivity(TransitiveClosure)

module _ where
  open import Numeral.Natural

  -- Sometimes also notated (_▫ⁿ_) for a relation (_▫_).
  data FiniteTransitiveClosure : ℕ → T → T → Type{ℓ₁ Lvl.⊔ ℓ₂} where
    base : ∀{a} → (a ▫ a) → (FiniteTransitiveClosure 𝟎 a a)
    step : ∀{a b c} → (a ▫ b) → ∀{n} → (FiniteTransitiveClosure n b c) → (FiniteTransitiveClosure (𝐒(n)) a c)

instance
  ReflexiveTransitiveClosure-reflexivity : Reflexivity(ReflexiveTransitiveClosure)
  ReflexiveTransitiveClosure-reflexivity = intro refl

instance
  ReflexiveTransitiveClosure-transitivity : Transitivity(ReflexiveTransitiveClosure)
  ReflexiveTransitiveClosure-transitivity = intro trans

-- The "prepend"-property of reflexive-transitive closure
ReflexiveTransitiveClosure-prepend : ∀{a b c} → (a ▫ b) → ReflexiveTransitiveClosure b c → ReflexiveTransitiveClosure a c
ReflexiveTransitiveClosure-prepend ab bc = trans (super ab) bc

-- A reflexive-transitive closure is the same as a path.
ReflexiveTransitiveClosure-Path-equivalence : ∀{a b} → (ReflexiveTransitiveClosure a b) ↔ (Walk(_▫_) a b)
ReflexiveTransitiveClosure-Path-equivalence = [↔]-intro l r where
  r : ∀{a b} → ReflexiveTransitiveClosure a b → Walk(_▫_) a b
  r ReflexiveTransitiveClosure.refl              = reflexivity(Walk(_▫_))
  r (ReflexiveTransitiveClosure.super ab)        = sub₂(_▫_)(Walk(_▫_)) ab
  r (ReflexiveTransitiveClosure.trans rab1 rb1b) = transitivity(Walk(_▫_)) (r rab1) (r rb1b)

  l : ∀{a b} → Walk(_▫_) a b → ReflexiveTransitiveClosure a b
  l Walk.at        = ReflexiveTransitiveClosure.refl
  l (Walk.prepend ab1 sb1b) = ReflexiveTransitiveClosure-prepend ab1 (l sb1b)
