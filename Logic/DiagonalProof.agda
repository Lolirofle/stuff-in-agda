module Logic.DiagonalProof {lvl} where

import      Level as Lvl
open import Logic.Propositional{lvl}
open import Logic.Predicate{lvl}{Lvl.𝟎}
open import Functional
open import Relator.Equals{lvl}{Lvl.𝟎}

diagonalProof : ∀{T₁ T₂}(ff : T₁ → T₁ → T₂)(diff-oper : T₂ → T₂) → (∀{x} → (x ≢ diff-oper(x))) → ∃{T₁ → T₂}(f ↦ (∀{a : T₁} → ¬(ff(a)(a) ≡ f(a))))
diagonalProof(ff)(diff-oper)(diff-proof) = [∃]-intro (a ↦ diff-oper(ff(a)(a))) (\{a} → diff-proof{ff(a)(a)})
