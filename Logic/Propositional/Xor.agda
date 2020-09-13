module Logic.Propositional.Xor where

open import Logic.Propositional
open import Logic
import      Lvl

-- TODO: Is it possible write a general construction for arbitrary number of xors? Probably by using rotate₃Fn₃Op₂?
data _⊕₃_⊕₃_ {ℓ₁ ℓ₂ ℓ₃} (P : Stmt{ℓ₁}) (Q : Stmt{ℓ₂}) (R : Stmt{ℓ₃}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
  [⊕₃]-intro₁ : P     → (¬ Q) → (¬ R) → (P ⊕₃ Q ⊕₃ R)
  [⊕₃]-intro₂ : (¬ P) → Q     → (¬ R) → (P ⊕₃ Q ⊕₃ R)
  [⊕₃]-intro₃ : (¬ P) → (¬ Q) → R     → (P ⊕₃ Q ⊕₃ R)
