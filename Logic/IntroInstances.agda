module Logic.IntroInstances where

import      Data.Tuple as Tuple
import      Lvl
open import Logic.Predicate
open import Logic.Propositional
open import Type

private variable ℓ : Lvl.Level
private variable A B Obj : Type{ℓ}
private variable P : Obj → Type{ℓ}
private variable x : Obj

instance
  [∧]-intro-instance : ⦃ _ : A ⦄ → ⦃ _ : B ⦄ → (A ∧ B)
  [∧]-intro-instance ⦃ a ⦄ ⦃ b ⦄ = [∧]-intro a b

instance
  [∨]-introₗ-instance : ⦃ _ : A ⦄ → (A ∨ B)
  [∨]-introₗ-instance ⦃ a ⦄ = [∨]-introₗ a

instance
  [∨]-introᵣ-instance : ⦃ _ : B ⦄ → (A ∨ B)
  [∨]-introᵣ-instance ⦃ b ⦄ = [∨]-introᵣ b

instance
  [∃]-intro-instance : ⦃ _ : P(x) ⦄ → ∃(P)
  [∃]-intro-instance {x = x} ⦃ proof ⦄ = [∃]-intro (x) ⦃ proof ⦄
