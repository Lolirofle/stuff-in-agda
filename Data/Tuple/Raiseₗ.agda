module Data.Tuple.Raiseₗ where

open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Numeral.Natural
open import Numeral.Natural.Oper using (_−₀_)
open import Type

-- A tuple with the same type of elements a specified number of times
_^_ : ∀{ℓ} → Type{ℓ} → ℕ → Type{ℓ}
_^_ type 0         = Unit
_^_ type 1         = type
_^_ type (𝐒(𝐒(n))) = (type ^ 𝐒(n)) ⨯ type

-- Returns the nth element of a tuple
index : ∀{n : ℕ}{ℓ}{T : Type{ℓ}} → ℕ → (T ^ (𝐒(n))) → T
index {n}{_}{T} i tuple = index'{n}(n −₀ i)(tuple) where
  index' : ∀{n : ℕ} → ℕ → (T ^ (𝐒(n))) → T
  index' {𝟎}          _ x     = x
  index' {𝐒(_)} 𝟎      (_ , last) = last
  index' {𝐒(n)} (𝐒(i)) (rest , _) = index'{n}(i)(rest)

-- Applies a function for every element in a tuple
map : ∀{n : ℕ}{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ → T₂) → (T₁ ^ n) → (T₂ ^ n)
map {𝟎}       f _ = <>
map {𝐒(𝟎)}    f single        = f(single)
map {𝐒(𝐒(n))} f (rest , last) = (map{𝐒(n)}(f)(rest) , f(last))

-- Returns a element repeated a specified number of times in a tuple
repeat : ∀{ℓ}{T : Type{ℓ}} → (n : _) → T → (T ^ n)
repeat(𝟎)       _ = <>
repeat(𝐒(𝟎))    x = x
repeat(𝐒(𝐒(n))) x = (repeat(𝐒(n)) x , x)

-- Returns a multivariate function from a singlevariate function
lift : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (n : _) → (A → B) → ((A ^ n) → (B ^ n))
lift(𝟎)       f(_)  = <>
lift(𝐒(𝟎))    f(x)  = f(x)
lift(𝐒(𝐒(n))) f(rest , last) = (lift(𝐒(n)) f(rest) , f(last))

-- TODO: Is this necessary?
-- _[⨯∘⨯]_ : ∀{n : ℕ}{ℓ₁ ℓ₂ ℓ₃}{A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} → ((B ^ n) → C) → (A → B) → ((A ^ n) → C)
-- _[⨯∘⨯]_ {n} fs g xs = fs(lift(n)(g)(xs))

-- TODO: Transpose
-- (((1,2),3),((4,5),6),((7,8),9))
-- (((1,2),3),((4,7),(8,5),(6,9)))
-- (((1,(4,7)),(2,(8,5)),(3,(6,9))))
