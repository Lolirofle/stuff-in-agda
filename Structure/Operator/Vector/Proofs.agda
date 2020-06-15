module Structure.Operator.Vector.Proofs where

open import Data.Tuple
open import Functional
open import Function.Equals
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid.WithLvl
open import Structure.Operator
open import Structure.Operator.Field
open import Structure.Operator.Group
open import Structure.Operator.Monoid
import      Structure.Operator.Names as Names
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
open import Structure.Operator.Vector
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

module _
  {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ : Lvl.Level}
  {V : Type{ℓᵥ}}
  ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  {S : Type{ℓₛ}}
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  {_+ᵥ_ : V → V → V}
  {_⋅ₛᵥ_ : S → V → V}
  {_+ₛ_ _⋅ₛ_ : S → S → S}
  where

  module _ ⦃ vectorSpace : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) ⦄ where
    open VectorSpace(vectorSpace)

    [⋅ₛᵥ]-absorberₗ : ∀{v} → (𝟎ₛ ⋅ₛᵥ v ≡ 𝟎ᵥ)
    [⋅ₛᵥ]-absorberₗ {v} = cancellationᵣ(_+ᵥ_) ⦃ One.cancellationᵣ-by-associativity-inverse ⦄ $
      (𝟎ₛ ⋅ₛᵥ v) +ᵥ (𝟎ₛ ⋅ₛᵥ v) 🝖-[ [⋅ₛᵥ][+ₛ][+ᵥ]-distributivityᵣ ]-sym
      (𝟎ₛ +ₛ 𝟎ₛ) ⋅ₛᵥ v         🝖-[ congruence₂ₗ(_⋅ₛᵥ_)(v) (identityₗ(_+ₛ_)(𝟎ₛ)) ]
      𝟎ₛ ⋅ₛᵥ v                 🝖-[ identityₗ(_+ᵥ_)(𝟎ᵥ) ]-sym
      𝟎ᵥ +ᵥ (𝟎ₛ ⋅ₛᵥ v)         🝖-end

    [⋅ₛᵥ]-absorberᵣ : ∀{s} → (s ⋅ₛᵥ 𝟎ᵥ ≡ 𝟎ᵥ)
    [⋅ₛᵥ]-absorberᵣ {s} = cancellationᵣ(_+ᵥ_) ⦃ One.cancellationᵣ-by-associativity-inverse ⦄ $
      (s ⋅ₛᵥ 𝟎ᵥ) +ᵥ (s ⋅ₛᵥ 𝟎ᵥ) 🝖-[ distributivityₗ(_⋅ₛᵥ_)(_+ᵥ_) ]-sym
      s ⋅ₛᵥ (𝟎ᵥ +ᵥ 𝟎ᵥ)         🝖-[ congruence₂ᵣ(_⋅ₛᵥ_)(s) (identityₗ(_+ᵥ_)(𝟎ᵥ)) ]
      s ⋅ₛᵥ 𝟎ᵥ                 🝖-[ identityₗ(_+ᵥ_)(𝟎ᵥ) ]-sym
      𝟎ᵥ +ᵥ (s ⋅ₛᵥ 𝟎ᵥ)         🝖-end

    [⋅ₛᵥ]-negation : ∀{v} → ((−ₛ 𝟏ₛ) ⋅ₛᵥ v ≡ −ᵥ v)
    [⋅ₛᵥ]-negation {v} = _⊜_.proof (One.unique-inverseᵣ-by-id (intro p) [+ᵥ]-inverseᵣ) {v} where
      p : Names.InverseFunctionᵣ(_+ᵥ_) 𝟎ᵥ ((−ₛ 𝟏ₛ) ⋅ₛᵥ_)
      p{v} =
        v +ᵥ ((−ₛ 𝟏ₛ) ⋅ₛᵥ v)          🝖-[ congruence₂ₗ(_+ᵥ_) _ (identityₗ(_⋅ₛᵥ_)(𝟏ₛ)) ]-sym
        (𝟏ₛ ⋅ₛᵥ v) +ᵥ ((−ₛ 𝟏ₛ) ⋅ₛᵥ v) 🝖-[ [⋅ₛᵥ][+ₛ][+ᵥ]-distributivityᵣ ]-sym
        (𝟏ₛ +ₛ (−ₛ 𝟏ₛ))⋅ₛᵥ v          🝖-[ congruence₂ₗ(_⋅ₛᵥ_) v (inverseFunctionᵣ(_+ₛ_) ⦃ [∃]-intro _ ⦃ [+ₛ]-identityᵣ ⦄ ⦄ (−ₛ_)) ]
        𝟎ₛ ⋅ₛᵥ v                      🝖-[ [⋅ₛᵥ]-absorberₗ ]
        𝟎ᵥ                            🝖-end
