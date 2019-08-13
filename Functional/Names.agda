import      Lvl

module Functional.Names{ℓ : Lvl.Level} where

open import Logic.Propositional
import      Relator.Equals
open import Type

FunctionExtensionality : ∀{ℓₒ₁ ℓₒ₂} → Stmt{ℓ Lvl.⊔ Lvl.𝐒(ℓₒ₁ Lvl.⊔ ℓₒ₂)}
FunctionExtensionality{ℓₒ₁}{ℓₒ₂} = (∀{A : Type{ℓₒ₁}}{B : Type{ℓₒ₂}}{f₁ f₂ : A → B}{x} → (f₁(x) ≡ f₂(x))) where
  open Relator.Equals{ℓ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂} {ℓₒ₂}
