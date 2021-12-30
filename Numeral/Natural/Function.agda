module Numeral.Natural.Function where

open import Data.Tuple as Tuple
open import Numeral.Natural
open import Numeral.Natural.Oper

-- Maximum function
-- Returns the greatest number
max : ℕ → ℕ → ℕ
max 𝟎      𝟎      = 𝟎
max (𝐒(a)) 𝟎      = 𝐒(a)
max 𝟎      (𝐒(b)) = 𝐒(b)
max (𝐒(a)) (𝐒(b)) = 𝐒(max a b)

-- Minimum function
-- Returns the smallest number
min : ℕ → ℕ → ℕ
min 𝟎      𝟎      = 𝟎
min (𝐒(_)) 𝟎      = 𝟎
min 𝟎      (𝐒(_)) = 𝟎
min (𝐒(a)) (𝐒(b)) = 𝐒(min a b)
-- min a b = (a + b) −₀ max(a)(b)

minmax : ℕ → ℕ → (ℕ ⨯ ℕ)
minmax 𝟎      𝟎      = (𝟎 , 𝟎)
minmax (𝐒(a)) 𝟎      = (𝟎 , 𝐒(a))
minmax 𝟎      (𝐒(b)) = (𝟎 , 𝐒(b))
minmax (𝐒(a)) (𝐒(b)) = Tuple.map 𝐒 𝐒 (minmax a b)

-- min and max as binary operators
infixl 100 _[max]_ _[min]_
_[max]_ = max
_[min]_ = min

-- Fibonacci numbers
fib : ℕ → ℕ
fib(𝟎)       = 𝟎
fib(𝐒(𝟎))    = 𝐒(𝟎)
fib(𝐒(𝐒(n))) = fib(n) + fib(𝐒(n))

arithmetic-sequence : ℕ → ℕ → (ℕ → ℕ)
arithmetic-sequence init diff 𝟎      = init
arithmetic-sequence init diff (𝐒(n)) = diff + arithmetic-sequence init diff n

geometric-sequence : ℕ → ℕ → (ℕ → ℕ)
geometric-sequence init diff 𝟎      = init
geometric-sequence init diff (𝐒(n)) = diff ⋅ arithmetic-sequence init diff n
