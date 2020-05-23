module Data.Tuple where

import      Lvl
open import Type
open import Syntax.Function

infixr 200 _⨯_ _,_

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level
private variable X Y Z X₁ X₂ Y₁ Y₂ : Type{ℓ}

-- Definition of a 2-tuple
record _⨯_ (X : Type{ℓ₁}) (Y : Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  instance constructor _,_
  field
    left  : X
    right : Y
open _⨯_ public

map : (X₁ → X₂) → (Y₁ → Y₂) → (X₁ ⨯ Y₁) → (X₂ ⨯ Y₂)
map f g (x , y) = (f(x) , g(y))

-- Curries a function taking a 2-tuple, transforming it to a function returning a function instead
curry : ((X ⨯ Y) → Z) → (X → Y → Z)
curry f x y = f(x , y)

-- Uncurries a function taking a function, transforming it to a function taking a 2-tuple instead
uncurry : (X → Y → Z) → ((X ⨯ Y) → Z)
uncurry f (x , y) = f x y

mapLeft : (X₁ → X₂) → (X₁ ⨯ Y) → (X₂ ⨯ Y)
mapLeft f = map f (x ↦ x)

mapRight : let _ = X in (Y₁ → Y₂) → (X ⨯ Y₁) → (X ⨯ Y₂)
mapRight f = map (x ↦ x) f

associateLeft : (X ⨯ (Y ⨯ Z)) → ((X ⨯ Y) ⨯ Z)
associateLeft (x , (y , z)) = ((x , y) , z)

associateRight : ((X ⨯ Y) ⨯ Z) → (X ⨯ (Y ⨯ Z))
associateRight ((x , y) , z) = (x , (y , z))

-- Swaps the left and right elements of a 2-tuple
swap : (X ⨯ Y) → (Y ⨯ X)
swap(x , y) = (y , x)

repeat : X → (X ⨯ X)
repeat x = (x , x)
