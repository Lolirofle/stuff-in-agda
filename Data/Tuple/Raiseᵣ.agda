module Data.Tuple.Raiseᵣ where

open import Data
open import Numeral.Natural
open import Type

_^_ : ∀{ℓ} → Type{ℓ} → ℕ → Type{ℓ}
_^_ type 0      = Unit
_^_ type 1      = type
_^_ type (𝐒(n)) = type ⨯ (type ^ n)

map : ∀{n : ℕ}{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ → T₂) → (T₁ ^ n) → (T₂ ^ n)
map {0}       f _ = <>
map {1}       f single        = f(single)
map {𝐒(𝐒(n))} f (init , rest) = (f(init) , map{𝐒(n)}(f)(rest))

combine : ∀{n : ℕ}{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ ^ n) → (T₂ ^ n) → ((T₁ ⨯ T₂) ^ n)
combine {0}       <>        <>        = <>
combine {1}       a         b         = (a , b)
combine {𝐒(𝐒(n))} (ah , at) (bh , bt) = ((ah , bh) , combine {𝐒(n)} (at) (bt))

-- Returns a element repeated a specified number of times in a tuple
repeat : ∀{ℓ}{T : Type{ℓ}} → (n : _) → T → (T ^ n)
repeat(0)       _ = <>
repeat(1)       x = x
repeat(𝐒(𝐒(n))) x = (x , repeat(𝐒(n)) x)

-- Returns a multivariate function from a singlevariate function
lift : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (n : _) → (A → B) → ((A ^ n) → (B ^ n))
lift(0)       f(_)  = <>
lift(1)       f(x)  = f(x)
lift(𝐒(𝐒(n))) f(first , rest) = (f(first) , lift(𝐒(n)) f(rest))

module _ {ℓ} {T : Type{ℓ}} where
  head : ∀{n : ℕ} → (T ^ (𝐒(n))) → T
  head {𝟎}    x       = x
  head {𝐒(_)} (x , _) = x

  tail : ∀{n : ℕ} → (T ^ (𝐒(n))) → (T ^ n)
  tail {𝟎}    _       = <>
  tail {𝐒(_)} (_ , x) = x

  singleton : ∀{n : ℕ} → T → (T ^ 1)
  singleton(x) = x

  index : ∀{n : ℕ} → ℕ → (T ^ (𝐒(n))) → T
  index {𝟎}    _      x          = x
  index {𝐒(_)} 𝟎      (init , _) = init
  index {𝐒(n)} (𝐒(i)) (_ , rest) = index{n}(i)(rest)

  transpose : ∀{m n : ℕ} → ((T ^ m) ^ n) → ((T ^ n) ^ m)
  transpose {0}       {_}       _       = <>
  transpose {𝐒(𝐒(n))} {0}       <>      = (<> , transpose {𝐒(n)}{0} <>)
  transpose {1}       {_}       x       = x
  transpose {_}       {1}       x       = x
  transpose {𝐒(𝐒(m))} {𝐒(𝐒(n))} (h , t) = combine{𝐒(𝐒(m))} h (transpose {𝐒(𝐒(m))} {𝐒(n)} t)
    -- transpose ((1,(2,3)),((4,(5,6)),(7,(8,9))))
    -- combine (1,(2,3)) (transpose((4,(5,6)),(7,(8,9))))
    -- combine (1,(2,3)) (combine(4,(5,6)) (transpose(7,(8,9))))
    -- combine (1,(2,3)) (combine(4,(5,6)) (combine 7 (8,9)))
    -- combine (1,(2,3)) (combine(4,(5,6)) (7,(8,9)))
    -- combine (1,(2,3)) ((4,7),((5,8),(6,9)))
    -- ((1,(4,7)),((2,(5,8)),(3,(6,9))))

    -- ((1,(2,3)),(4,(5,6)),(7,(8,9)))
    -- (((1,4),(2,5),(3,6)),(7,(8,9)))
    -- (((1,(4,7)),(2,(5,8)),(3,(6,9))))
