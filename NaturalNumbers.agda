module NaturalNumbers where

open import Logic

data ℕ : Set where
  ℕ0 : ℕ
  𝑆 : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

-- Addition
infixl 5 _+_
_+_ : ℕ → ℕ → ℕ
x + ℕ0 = x
x + 𝑆(y) = 𝑆(x + y)

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
𝑆(x) / y =  y + (x / y)

-- Exponentiation
_^_ : ℕ → ℕ → ℕ
x ^ ℕ0 = 𝑆(ℕ0)
x ^ 𝑆(y) = x ⋅ (x ^ y)

-- Equals
infixl 1 _≡_
data _≡_ : ℕ → ℕ → Set where
  [≡]-reflexivity : ∀ {x} → (x ≡ x)
  [≡]-symmetry : ∀ {x y} → (x ≡ y) → (y ≡ x)
  [≡]-transitivity : ∀ {x y z} → (x ≡ y) → (y ≡ z) → (x ≡ z)

  [≡]-with-[_] : (f : ℕ → ℕ) → ∀ {x y} → (x ≡ y) → (f(x) ≡ f(y))

  [+]-commutativity : ∀ {x y} → (x + y) ≡ (y + x)
  [+]-associativity : ∀ {x y z} → ((x + y) + z) ≡ (x + (y + z))
  [+]-identity : ∀ {x} → (0 + x) ≡ x

  [⋅]-commutativity : ∀ {x y} → (x ⋅ y) ≡ (y ⋅ x)
  [⋅]-associativity : ∀ {x y z} → ((x ⋅ y) ⋅ z) ≡ (x ⋅ (y ⋅ z))
  [⋅]-absorber0 : ∀ {x} → (0 ⋅ x) ≡ x
  [⋅]-identity : ∀ {x} → (1 ⋅ x) ≡ x

  [⋅][+]-distributivity : ∀ {x y z} → (x ⋅ (y + z)) ≡ (x ⋅ y) + (x ⋅ z)

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

data _divides_withRemainder_ : ℕ → ℕ → ℕ → Set where
  DivRem0 : {x : ℕ} →{r : ℕ} → x divides r withRemainder r
  DivRem𝑆 : {x : ℕ} → {y : ℕ} → {r : ℕ} → (x divides y withRemainder r) → (x divides (x + y) withRemainder r)
