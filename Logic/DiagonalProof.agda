module Logic.DiagonalProof {lvl₁} {lvl₂} where

import      Level as Lvl
open import Logic.Propositional{lvl₁ Lvl.⊔ lvl₂}
open import Logic.Predicate{lvl₁}{lvl₂}
open import Functional
open import Relator.Equals{lvl₁}{lvl₂}
open import Type{lvl₂}

diagonal-proof : ∀{T₁ T₂ : Type}(diff-oper : T₂ → T₂) → (∀{x} → (x ≢ diff-oper(x))) → (ff : T₁ → T₁ → T₂) → ∃{T₁ → T₂}(f ↦ (∀{a : T₁} → ¬(ff(a)(a) ≡ f(a))))
diagonal-proof(diff-oper)(diff-proof)(ff) = [∃]-intro (a ↦ diff-oper(ff(a)(a))) (\{a} → diff-proof{ff(a)(a)})
