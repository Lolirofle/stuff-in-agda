module Type.Dependent.Equiv where

open import Functional
open import Structure.Relator.Equivalence.Proofs
open import Structure.Setoid
open import Type
open import Type.Dependent

Σₗ-equiv : ∀{ℓ₁ ℓ₂ ℓₑ}{A : Type{ℓ₁}} ⦃ equiv : Equiv{ℓₑ}(A) ⦄ {B : A → Type{ℓ₂}} → Equiv(Σ A B)
Σₗ-equiv ⦃ equiv ⦄ = intro ((_≡_) on₂ Σ.left) ⦃ on₂-equivalence{_▫_ = _≡_}{f = Σ.left} ⦃ Equiv.equivalence equiv ⦄ ⦄
