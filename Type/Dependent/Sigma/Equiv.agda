module Type.Dependent.Sigma.Equiv where

open import Functional
open import Structure.Relator.Equivalence
open import Structure.Relator.Equivalence.Proofs.On₂
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type
open import Type.Dependent.Sigma

module _
  {ℓ₁ ℓ₂ ℓₑ}
  {A : Type{ℓ₁}} ⦃ equiv : Equiv{ℓₑ}(A) ⦄
  {B : A → Type{ℓ₂}}
  where

  Σₗ-equiv : Equiv(Σ A B)
  Σₗ-equiv = intro ((_≡_) on₂ Σ.left) ⦃ on₂-equivalence{_▫_ = _≡_}{f = Σ.left} ⦃ Equiv.equivalence equiv ⦄ ⦄

module _
  {ℓ₁ ℓ₂ ℓₑ}
  {A : Type{ℓ₁}}
  {B : A → Type{ℓ₂}}
  (_≡_ : ∀{a₁ a₂} → B(a₁) → B(a₂) → Type{ℓₑ})
  (refl : ∀{a}{b : B(a)} → (b ≡ b))
  (sym : ∀{a₁ a₂}{b₁ : B(a₁)}{b₂ : B(a₂)} → (b₁ ≡ b₂) → (b₂ ≡ b₁))
  (trans : ∀{a₁ a₂ a₃}{b₁ : B(a₁)}{b₂ : B(a₂)}{b₃ : B(a₃)} → (b₁ ≡ b₂) → (b₂ ≡ b₃) → (b₁ ≡ b₃))
  where

  Σᵣ-equiv : Equiv(Σ A B)
  Σᵣ-equiv = intro (\(intro _ b₁) (intro _ b₂) → b₁ ≡ b₂) ⦃ intro ⦃ intro refl ⦄ ⦃ intro sym ⦄ ⦃ intro trans ⦄ ⦄
