module Lang.Inspect where

open import Type
open import Sets.Setoid
open import Structure.Relator.Properties

{-
module _ {ℓ₁ ℓ₂} {A : Type{ℓ₁}} {B : A → Type{ℓ₂}} ⦃ eqB : ∀{x} → Equiv(B(x)) ⦄ (f : ∀(x) → B(x)) (x : A) where
  data Inspect (y : B(x)) : Type{ℓ₂} where
    intro : (f(x) ≡ y) → Inspect(y)

  inspect : Inspect(f(x))
  inspect = intro(reflexivity(_≡_ ⦃ eqB ⦄))
  {-# INLINE inspect #-}
-}

-- TODO: Move to Lang.Inspect
module _ {ℓ₁ ℓ₂} {A : Type{ℓ₁}} {B : Type{ℓ₂}} ⦃ eqB : Equiv(B) ⦄ (f : A → B) (x : A) where
  data Inspect (y : B) : Type{ℓ₂} where
    intro : (f(x) ≡ y) → Inspect(y)

  inspect : Inspect(f(x))
  inspect = intro(reflexivity(_≡_))
  {-# INLINE inspect #-}
