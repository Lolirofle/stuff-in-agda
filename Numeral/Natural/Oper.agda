module Numeral.Natural.Oper where

open import Numeral.Natural

infixl 10010 _+_
infix  10010 _−₀_ _𝄩_
infixl 10020 _⋅_
-- infix  10020 _/₀_
infixl 10030 _^_

-- TODO: It would require a great amount of work, but consider changing the induction to being on the left side instead of the right on _+_ and _⋅_. It will then mirror how lists (a similar structure) uses induction in its definition. The advantage of having it on the right side as it is now is that induction using the full operator name is easier: ℕ-induction(_+_ a) vs ℕ-induction(a ↦ _+_ a b)

-- Addition
_+_ : ℕ → ℕ → ℕ
x + 𝟎 = x
x + 𝐒(y) = 𝐒(x + y)
{-# BUILTIN NATPLUS _+_ #-}

-- Multiplication
_⋅_ : ℕ → ℕ → ℕ
_ ⋅ 𝟎 = 𝟎
x ⋅ 𝐒(y) = x + (x ⋅ y)
{-# BUILTIN NATTIMES _⋅_ #-}

-- Exponentiation
_^_ : ℕ → ℕ → ℕ
x ^ 𝟎 = 𝐒(𝟎)
x ^ 𝐒(y) = x ⋅ (x ^ y)

-- Factorial
_! : ℕ → ℕ
𝟎 ! = 𝐒(𝟎)
𝐒(x) ! = 𝐒(x) ⋅ (x !)

-- Distance (Absolute subtraction) (Interval length)
_𝄩_ : ℕ → ℕ → ℕ
𝟎    𝄩 𝟎    = 𝟎
𝐒(x) 𝄩 𝟎    = 𝐒(x)
𝟎    𝄩 𝐒(x) = 𝐒(x)
𝐒(x) 𝄩 𝐒(y) = x 𝄩 y



-- Closed total subtraction (monus)
_−₀_ : ℕ → ℕ → ℕ
x    −₀ 𝟎    = x
𝟎    −₀ 𝐒(_) = 𝟎
𝐒(x) −₀ 𝐒(y) = x −₀ y
{-# BUILTIN NATMINUS _−₀_ #-}

-- Hyperoperation: (a ↑[n]↑ b) where (n=0)⇒(_ ↦ 𝐒) , (n=1)⇒(+) , (n=2)⇒(⋅) , (n=3)⇒(^)
_↑[_]↑_ : ℕ → ℕ → ℕ → ℕ
_ ↑[ 0          ]↑ b = 𝐒(b)
a ↑[ 1          ]↑ 0 = a
_ ↑[ 2          ]↑ 0 = 0
_ ↑[ 𝐒(𝐒(𝐒(n))) ]↑ 0 = 1
{-# CATCHALL #-}
a ↑[ 𝐒(n)       ]↑ (𝐒(b)) = a ↑[ n ]↑ (a ↑[ n ]↑ b)
