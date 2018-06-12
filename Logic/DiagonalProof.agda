module Logic.DiagonalProof {ℓ₁} {ℓ₂} where

import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Functional
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}
open import Relator.Equals.Proofs{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

diagonal-proof : ∀{T₁ T₂ : Type}(diff-oper : T₂ → T₂) → (∀{x} → (x ≢ diff-oper(x))) → (ff : T₁ → T₁ → T₂) → ∃{T₁ → T₂}(f ↦ (∀{a : T₁} → ¬(ff(a)(a) ≡ f(a))))
diagonal-proof(diff-oper)(diff-proof)(ff) = [∃]-intro (a ↦ diff-oper(ff(a)(a))) ⦃ \{a} → diff-proof{ff(a)(a)} ⦄
