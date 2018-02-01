module Syntax.Number where

import      Lvl
open import Logic.Propositional
open import Numeral.Natural

-- Syntax
record From-ℕsubset {ℓ} (T : Set(ℓ)) : Set(Lvl.𝐒(ℓ)) where
  field
    restriction  : ℕ → Set(ℓ)
    from-ℕsubset : (n : ℕ) → ⦃ _ : restriction(n) ⦄ → T
open From-ℕsubset {{...}} public using (from-ℕsubset)
{-# BUILTIN FROMNAT from-ℕsubset #-}

record From-ℕ {ℓ} (T : Set(ℓ)) : Set(ℓ) where
  field
    from-ℕ : ℕ → T
open From-ℕ {{...}} public using (from-ℕ)

instance
  From-ℕsubset-from-From-ℕ : ∀{ℓ}{T} → ⦃ _ : From-ℕ{ℓ}(T) ⦄ → From-ℕsubset{ℓ}(T)
  From-ℕsubset.restriction ( From-ℕsubset-from-From-ℕ ) (_) = ⊤
  from-ℕsubset ⦃ From-ℕsubset-from-From-ℕ ⦄ (n) ⦃ _ ⦄ = from-ℕ (n)

instance
  ℕ-From-ℕ : From-ℕ (ℕ)
  from-ℕ ⦃ ℕ-From-ℕ ⦄ (x) = x

instance
  Level-From-ℕ : From-ℕ (Lvl.Level)
  from-ℕ ⦃ Level-From-ℕ ⦄ (ℕ.𝟎)    = Lvl.𝟎
  from-ℕ ⦃ Level-From-ℕ ⦄ (ℕ.𝐒(n)) = Lvl.𝐒(from-ℕ(n))
