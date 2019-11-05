module Type.WellOrdering where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Type
open import Type.Dependent

private variable ℓ₁ ℓ₂ : Lvl.Level

record W {A : Type{ℓ₁}} (B : A → Type{ℓ₂}) : Type{ℓ₁ ⊔ ℓ₂} where
  inductive
  constructor sup
  field
    a : A
    b : B(a) → W(B)

-- TODO: Note that this is essentially Sets.IterativeSet
V : ∀{ℓ₁} → Type{Lvl.𝐒(ℓ₁)}
V {ℓ₁} = W {A = Type{ℓ₁}} id
