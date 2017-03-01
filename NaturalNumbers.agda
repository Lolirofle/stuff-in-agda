module NaturalNumbers where

open import Logic

data ℕ : Set where
  ℕ0 : ℕ
  𝑆 : ℕ → ℕ

-- Addition
infixl 5 _+_
_+_ : ℕ → ℕ → ℕ
x + ℕ0 = x
x + 𝑆(y) = 𝑆(x + y)

-- [+]-commutativity : {a : ℕ} → {b : ℕ} → (a + b) → (b + a)

-- Multiplication
infixl 6 _⋅_
_⋅_ : ℕ → ℕ → ℕ
x ⋅ ℕ0 = ℕ0
x ⋅ 𝑆(y) = x + (x ⋅ y)

-- Subtraction
_−_ : ℕ → ℕ → ℕ
x − ℕ0 = x
ℕ0 − 𝑆(x) = ℕ0
𝑆(x) − 𝑆(y) = x − y

-- Division
_/_ : ℕ → ℕ → ℕ
ℕ0 / x = ℕ0
x / ℕ0 = ℕ0
𝑆(x) / y =  y + (x / y)

-- Divisibility
data Even : ℕ → Set where
  Even0 : Even ℕ0
  Even𝑆 : {x : ℕ} → (Even x) → (Even(𝑆(𝑆(x))))

data Odd : ℕ → Set where
  Odd0 : Odd (𝑆(ℕ0))
  Odd𝑆 : {x : ℕ} → (Odd x) → (Odd(𝑆(𝑆(x))))

data _divides_ : ℕ → ℕ → Set where
  Div0 : {x : ℕ} → x divides ℕ0
  Div𝑆 : {x : ℕ} → {y : ℕ} → (x divides y) → (x divides (x + y))

data _==_ : ℕ → ℕ → Set where
  [==]-reflexivity : ∀ {x} → (x == x)
  [==]-symmetry : ∀ {x y} → (x == y) → (y == x)
  [==]-transitivity : ∀ {x y z} → (x == y) → (y == z) → (x == z)

  [==]-with-[𝑆] : ∀ {x y} → (x == y) → (𝑆(x) == 𝑆(y))
