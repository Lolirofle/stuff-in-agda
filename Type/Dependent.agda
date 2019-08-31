module Type.Dependent where

import      Lvl
open import Type

-- Dependent product type (pi-type).
-- Also called: Dependent function type.
-- The right-hand side's type is a function type that uses the left-hand side's type as its "domain".
-- And then the type of the resulting function of the two types depends on the argument.
record Π {ℓ₁ ℓ₂} (A : Type{ℓ₁}) (B : A → Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  constructor intro
  field
    apply : (a : A) → B(a)

-- Dependent sum type (sigma-type).
-- Also called: Dependent pair type.
-- The right-hand side's type is a function type that uses the left-hand side's type as its "domain".
-- And then the type of the resulting pair depends on the left-hand side.
record Σ {ℓ₁ ℓ₂} (A : Type{ℓ₁}) (B : A → Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  constructor intro
  field
    left  : A
    right : B(left)
