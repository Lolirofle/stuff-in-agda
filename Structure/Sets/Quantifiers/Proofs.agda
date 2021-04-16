open import Type
open import Structure.Relator
open import Structure.Setoid renaming (_≡_ to _≡ₑ_)

module Structure.Sets.Quantifiers.Proofs {ℓₛ ℓₗ ℓₑ} {S : Type{ℓₛ}} ⦃ equiv : Equiv{ℓₑ}(S) ⦄ (_∈_ : S → S → Type{ℓₗ}) ⦃ [∈]-binaryRelator : BinaryRelator(_∈_) ⦄ where

import      Lvl
open import Structure.Relator.Proofs renaming ([≡]-binaryRelator to [≡ₑ]-binaryRelator)
open import Structure.Sets.Quantifiers(_∈_)
open import Syntax.Function

private variable ℓ : Lvl.Level
private variable A : S

[∃ₛ]-unaryRelator : ∀{P : S → S → Type{ℓ}} → ⦃ rel-P : ∀{x} → UnaryRelator(P(x)) ⦄ → UnaryRelator(\y → ∃ₛ(A)(x ↦ P(x)(y)))
[∃ₛ]-unaryRelator = [∃]-unaryRelator ⦃ rel-P = [∧]-unaryRelator ⦄

[∀ₛ]-unaryRelator : ∀{P : S → S → Type{ℓ}} → ⦃ rel-P : ∀{x} → UnaryRelator(P(x)) ⦄ → UnaryRelator(\y → ∀ₛ(A)(x ↦ P(x)(y)))
[∀ₛ]-unaryRelator = [∀]-unaryRelator ⦃ rel-P = [→]-unaryRelator ⦄

[∃ₛ]-binaryRelator : ∀{P : S → S → S → Type{ℓ}} → ⦃ rel-P : ∀{x} → BinaryRelator(P(x)) ⦄ → BinaryRelator(\A y → ∃ₛ(A)(x ↦ P(x)(A)(y)))
[∃ₛ]-binaryRelator = binaryRelator-from-unaryRelator
  ⦃ relₗ = [∃]-unaryRelator ⦃ rel-P = [∧]-unaryRelator ⦃ rel-P = binary-unaryRelatorₗ ⦄ ⦃ rel-Q = binary-unaryRelatorᵣ ⦄ ⦄ ⦄
  ⦃ relᵣ = [∃]-unaryRelator ⦃ rel-P = [∧]-unaryRelator ⦃ rel-Q = binary-unaryRelatorₗ ⦄ ⦄ ⦄

[∀ₛ]-binaryRelator : ∀{P : S → S → S → Type{ℓ}} → ⦃ rel-P : ∀{x} → BinaryRelator(P(x)) ⦄ → BinaryRelator(\A y → ∀ₛ(A)(x ↦ P(x)(A)(y)))
[∀ₛ]-binaryRelator = binaryRelator-from-unaryRelator
  ⦃ relₗ = [∀]-unaryRelator ⦃ rel-P = [→]-unaryRelator ⦃ rel-P = binary-unaryRelatorₗ ⦄ ⦃ rel-Q = binary-unaryRelatorᵣ ⦄ ⦄ ⦄
  ⦃ relᵣ = [∀]-unaryRelator ⦃ rel-P = [→]-unaryRelator ⦃ rel-Q = binary-unaryRelatorₗ ⦄ ⦄ ⦄
