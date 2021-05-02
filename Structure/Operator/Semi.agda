module Structure.Operator.Semi where

import      Lvl
open import Logic
open import Structure.Setoid
open import Structure.Operator
open import Structure.Operator.Properties hiding (associativity)
open import Type

-- Also called: Semigroup.
-- Note: The usual name "semigroup" does not fit because of the hierarchy: semigroup < monoid < group. "Semigroup" meaning almost a group, but just semi may refer to it almost being a bigger structure.
record Semi {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ binary-operator ⦄ : BinaryOperator(_▫_)
    ⦃ associativity ⦄   : Associativity(_▫_)
