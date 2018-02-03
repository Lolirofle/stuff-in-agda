module Structure.Operator.Monoid {ℓ₁} {ℓ₂} where

open import Functional hiding (id)
import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

-- A type and a binary operator using this type is a monoid when:
-- • The operator is associative.
-- • The operator have an identity in both directions.
record Monoid {T : Type} (_▫_ : T → T → T) : Stmt where
  field
    id : T
  field
    associativity  : Associativity    (_▫_)
    identityₗ       : Identityₗ        (_▫_) id
    identityᵣ       : Identityᵣ        (_▫_) id
