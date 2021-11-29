module Lang.Reflection.DoNotation where

open import Lang.Reflection
open import Syntax.Do

instance
  TC-doNotation : ∀{ℓ} → DoNotation{ℓ}(TC)
  return ⦃ TC-doNotation ⦄ = returnTC
  _>>=_  ⦃ TC-doNotation ⦄ = bindTC
