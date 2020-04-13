module Structure.Operator.Vector.Proofs where

open import Data.Tuple
import      Lvl
open import Logic
open import Logic.Propositional
open import Structure.Setoid
open import Structure.Operator.Field
open import Structure.Operator.Group
open import Structure.Operator.Monoid
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Operator.Vector
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

module _
  {ℓᵥ ℓₛ : Lvl.Level}
  {V : Type{ℓᵥ}}
  ⦃ equiv-V : Equiv(V) ⦄
  {S : Type{ℓₛ}}
  ⦃ equiv-S : Equiv(S) ⦄
  {_+ᵥ_ : V → V → V}
  {_⋅ₛᵥ_ : S → V → V}
  {_+ₛ_ _⋅ₛ_ : S → S → S}
  where

  module _ ⦃ vectorSpace : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) ⦄ where
    open VectorSpace(vectorSpace)

    postulate [⋅ₛᵥ]-absorberₗ : ∀{v} → (𝟎ₛ ⋅ₛᵥ v ≡ 𝟎ᵥ)
    {-[⋅ₛᵥ]-absorberₗ =
      𝟎ₛ ⋅ₛᵥ v 🝖-[ ? ]
      𝟎ᵥ +ᵥ (𝟎ₛ ⋅ₛᵥ v) 🝖-[ ? ]
      𝟎ᵥ 🝖-end
    -}
    postulate [⋅ₛᵥ]-absorberᵣ : ∀{s} → (s ⋅ₛᵥ 𝟎ᵥ ≡ 𝟎ᵥ)
    postulate [⋅ₛᵥ]-negation : ∀{v} → ((−ₛ 𝟏ₛ) ⋅ₛᵥ v ≡ −ᵥ v)
