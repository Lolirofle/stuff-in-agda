module Data.Tuple where

open import Function
import      Lvl
open import Type

infixr 200 _⨯_ _,_

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level
private variable A B C A₁ A₂ B₁ B₂ : Type{ℓ}

-- Definition of a 2-tuple
record _⨯_ (A : Type{ℓ₁}) (B : Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  constructor _,_
  field
    left  : A
    right : B
open _⨯_ public

elim : ∀{P : (A ⨯ B) → Type{ℓ}} → ((a : A) → (b : B) → P(a , b)) → ((p : (A ⨯ B)) → P(p))
elim f(a , b) = f a b

invElim : ∀{P : (A ⨯ B) → Type{ℓ}} → ((a : A) → (b : B) → P(a , b)) ← ((p : (A ⨯ B)) → P(p))
invElim f a b = f(a , b)

map : (A₁ → A₂) → (B₁ → B₂) → (A₁ ⨯ B₁) → (A₂ ⨯ B₂)
map f g (x , y) = (f(x) , g(y))

-- Curries a function taking a 2-tuple, transforming it to a function returning a function instead
curry : ((A ⨯ B) → C) → (A → B → C)
curry = invElim

-- Uncurries a function taking a function, transforming it to a function taking a 2-tuple instead
uncurry : (A → B → C) → ((A ⨯ B) → C)
uncurry = elim

mapLeft : (A₁ → A₂) → (A₁ ⨯ B) → (A₂ ⨯ B)
mapLeft f = map f id

mapRight : let _ = A in (B₁ → B₂) → (A ⨯ B₁) → (A ⨯ B₂)
mapRight f = map id f

associateLeft : (A ⨯ (B ⨯ C)) → ((A ⨯ B) ⨯ C)
associateLeft (x , (y , z)) = ((x , y) , z)

associateRight : ((A ⨯ B) ⨯ C) → (A ⨯ (B ⨯ C))
associateRight ((x , y) , z) = (x , (y , z))

-- Swaps the left and right elements of a 2-tuple
swap : (A ⨯ B) → (B ⨯ A)
swap(x , y) = (y , x)

repeat : A → (A ⨯ A)
repeat x = (x , x)
