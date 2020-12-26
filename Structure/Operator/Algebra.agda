module Structure.Operator.Algebra where

open import Lang.Instance
open import Logic.Predicate
import      Lvl
open import Structure.Function.Domain
open import Structure.Operator.Field
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Structure.Operator.Ring.Homomorphism
open import Structure.Operator.Vector
open import Structure.Operator.Vector.LinearMap
open import Structure.Setoid
open import Type

module _
  {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ}
  {V : Type{ℓᵥ}} ⦃ _ : Equiv{ℓᵥₑ}(V) ⦄
  {S : Type{ℓₛ}} ⦃ _ : Equiv{ℓₛₑ}(S) ⦄
  (_+ᵥ_ : V → V → V)
  (_⋅ᵥ_ : V → V → V)
  (_⋅ₛᵥ_ : S → V → V)
  (_+ₛ_ : S → S → S)
  (_⋅ₛ_ : S → S → S)
  where

  record Algebra : Type{ℓₛₑ Lvl.⊔ ℓₛ Lvl.⊔ ℓᵥₑ Lvl.⊔ ℓᵥ} where
    constructor intro
    field
      ⦃ vectorSpace ⦄      : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_)
      ⦃ [⋅ᵥ]-bilinearity ⦄ : BilinearOperator vectorSpace (_⋅ᵥ_)
    open VectorSpace(vectorSpace)
      renaming (ring to ringₛ)
      public

    ringᵥ : ⦃ Associativity(_⋅ᵥ_) ⦄ → ⦃ ∃(Identity(_⋅ᵥ_)) ⦄ → Ring(_+ᵥ_)(_⋅ᵥ_)
    Rng.[+]-commutative-group    (Ring.rng   ringᵥ) = vectorCommutativeGroup
    Rng.[⋅]-binary-operator      (Ring.rng   ringᵥ) = BilinearMap.binaryOperator [⋅ᵥ]-bilinearity
    Rng.[⋅]-associativity        (Ring.rng   ringᵥ) = infer
    Rng.[⋅][+]-distributivityₗ   (Ring.rng   ringᵥ) = BilinearOperator.[+ᵥ]-distributivityₗ vectorSpace (_⋅ᵥ_) [⋅ᵥ]-bilinearity
    Rng.[⋅][+]-distributivityᵣ   (Ring.rng   ringᵥ) = BilinearOperator.[+ᵥ]-distributivityᵣ vectorSpace (_⋅ᵥ_) [⋅ᵥ]-bilinearity
    Unity.[⋅]-identity-existence (Ring.unity ringᵥ) = infer

  -- TODO: I found some conflicting definitions for a star algebra from different sources. What is a reasonable definition?
  record ⋆-algebra (_⋆ᵥ : V → V) (_⋆ₛ : S → S) : Type{ℓₛₑ Lvl.⊔ ℓₛ Lvl.⊔ ℓᵥₑ Lvl.⊔ ℓᵥ} where
    constructor intro
    field
      ⦃ algebra ⦄ : Algebra
    open Algebra(algebra) public

    field
      ⦃ [⋅ᵥ]-commutativity ⦄             : Commutativity(_⋅ᵥ_)
      ⦃ [⋅ᵥ]-associativity ⦄             : Associativity(_⋅ᵥ_)
      ⦃ [⋅ᵥ]-identity ⦄                  : ∃(Identity(_⋅ᵥ_))
      ⦃ [⋆ₛ]-involution ⦄                : Involution(_⋆ᵥ)
      ⦃ [⋆ᵥ]-involution ⦄                : Involution(_⋆ᵥ)
      [⋆ᵥ]-distribute-over-[⋅ₛᵥ]-to-[⋆ₛ] : ∀{s}{v} → ((s ⋅ₛᵥ v)⋆ᵥ ≡ (s ⋆ₛ) ⋅ₛᵥ (v ⋆ᵥ))
      ⦃ [⋆ₛ]-antihomomorphism ⦄          : Antihomomorphism ringₛ ringₛ (_⋆ₛ)
      ⦃ [⋆ᵥ]-antihomomorphism ⦄          : Antihomomorphism ringᵥ ringᵥ (_⋆ᵥ)
