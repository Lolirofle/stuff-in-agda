module Lang.Inspect where

open import Type
open import Structure.Setoid.WithLvl
open import Structure.Relator.Properties

{-
module _ {ℓ₁ ℓ₂} {A : Type{ℓ₁}} {B : A → Type{ℓ₂}} ⦃ eqB : ∀{x} → Equiv(B(x)) ⦄ (f : ∀(x) → B(x)) (x : A) where
  data Inspect (y : B(x)) : Type{ℓ₂} where
    intro : (f(x) ≡ y) → Inspect(y)

  inspect : Inspect(f(x))
  inspect = intro(reflexivity(_≡_ ⦃ eqB ⦄))
  {-# INLINE inspect #-}
-}

module _ {ℓ₁ ℓ₂ ℓₑ₂} {A : Type{ℓ₁}} {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ (f : A → B) (x : A) where
  data Inspect (y : B) : Type{ℓₑ₂} where
    intro : (f(x) ≡ y) → Inspect(y)

  inspect : Inspect(f(x))
  inspect = intro(reflexivity(_≡_))
  {-# INLINE inspect #-}
