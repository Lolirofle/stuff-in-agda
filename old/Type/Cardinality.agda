import      Lvl
open import Type

module Type.Cardinality {ℓₗ : Lvl.Level} where

import Type.Functions
import Logic.Predicate

module _ {ℓₒ₁}{ℓₒ₂} (X : Type{ℓₒ₁}) (Y : Type{ℓₒ₂}) where
  open Type.Functions{ℓₗ}{ℓₒ₁}{ℓₒ₂}
  open Logic.Predicate{ℓₗ}

  _≍_ : Type{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂}
  _≍_ = ∃(Bijective{X}{Y})

  _≼_ : Type{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂}
  _≼_ = ∃(Injective{X}{Y})

  _≽_ : Type{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂}
  _≽_ = ∃(Surjective{X}{Y})
