module Data.Tuple where

import      Lvl
open import Type

infixl 200 _⨯_ _,_ -- TODO: Raiseᵣ gives the opposite: infixr

-- Definition of a 2-tuple
record _⨯_ {ℓ₁}{ℓ₂} (X : Type{ℓ₁}) (Y : Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  instance constructor _,_
  field
    left  : X
    right : Y
open _⨯_ public

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} {T₄ : Type{ℓ₄}} where
  map : (T₁ → T₃) → (T₂ → T₄) → (T₁ ⨯ T₂) → (T₃ ⨯ T₄)
  map f g (x , y) = (f(x) , g(y))

module _ {ℓ₁ ℓ₂ ℓ₃} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} where
  -- Curries a function taking a 2-tuple, transforming it to a function returning a function instead
  curry : ((T₁ ⨯ T₂) → T₃) → (T₁ → T₂ → T₃)
  curry f x₁ x₂ = f(x₁ , x₂)

  -- Uncurries a function taking a function, transforming it to a function taking a 2-tuple instead
  uncurry : (T₁ → T₂ → T₃) → ((T₁ ⨯ T₂) → T₃)
  uncurry f (x₁ , x₂) = f x₁ x₂

  mapLeft : (T₁ → T₃) → (T₁ ⨯ T₂) → (T₃ ⨯ T₂)
  mapLeft f(x , y) = (f(x) , y)

  mapRight : (T₂ → T₃) → (T₁ ⨯ T₂) → (T₁ ⨯ T₃)
  mapRight f(x , y) = (x , f(y))

module _ {ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} where
  -- Swaps the left and right elements of a 2-tuple
  swap : (T₁ ⨯ T₂) → (T₂ ⨯ T₁)
  swap(x , y) = (y , x)

  map1 : (T₁ → T₂) → (T₁ ⨯ T₁) → (T₂ ⨯ T₂)
  map1 f = map f f
