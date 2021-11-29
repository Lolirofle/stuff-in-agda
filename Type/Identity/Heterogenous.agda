module Type.Identity.Heterogenous where

import      Lvl
open import Type

data HId {ℓ} : ∀{A B : Type{ℓ}} → A → B → Type{Lvl.𝐒(ℓ)} where
  instance intro : ∀{T}{x : T} → HId x x
