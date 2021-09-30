open import Type
open import Structure.Setoid

module Structure.Operator.Lattice.OrderRelation {ℓ ℓₑ} (L : Type{ℓ}) ⦃ equiv-L : Equiv{ℓₑ}(L) ⦄ (_▫_ : L → L → L) where

order : L → L → Type
order x y = (x ▫ y ≡ y)
