module Type.Proofs where

open import Logic
import      Lvl
-- open import Relator.Equals
open import Type

data _≡_ {ℓ₁ ℓ₂} : {A : Type{ℓ₁}}{B : Type{ℓ₂}} → A → B → Stmt{?} where
  instance [≡]-intro : ∀{T}{x : T} → (x ≡ x)

test : ∀{ℓ₁ ℓ₂ : Lvl.Level} → (ℓ₁ ≡ ℓ₂) → TYPE ℓ₁ ≡ {!TYPE ℓ₂!}
