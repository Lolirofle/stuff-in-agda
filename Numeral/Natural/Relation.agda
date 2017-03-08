module Numeral.Natural.Relation where

open import Numeral.Natural
open import Numeral.Natural.Oper

[ℕ]-induction : {X : ℕ → Set} → X(𝟎) → ((i : ℕ) → X(i) → X(𝐒(i))) → (n : ℕ) → X(n)
[ℕ]-induction base next 𝟎 = base
[ℕ]-induction base next (𝐒(n)) = next(n)([ℕ]-induction base next n)

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
  Even0 : Even 𝟎
  Even𝐒 : {x : ℕ} → (Even x) → (Even(𝐒(𝐒(x))))

data Odd : ℕ → Set where
  Odd0 : Odd (𝐒(𝟎))
  Odd𝐒 : {x : ℕ} → (Odd x) → (Odd(𝐒(𝐒(x))))

data _divides_ : ℕ → ℕ → Set where
  Div0 : {x : ℕ} → x divides 𝟎
  Div𝐒 : {x : ℕ} → {y : ℕ} → (x divides y) → (x divides (x + y))

data _divides_withRemainder_ : ℕ → ℕ → ℕ → Set where
  DivRem0 : {x : ℕ} →{r : ℕ} → x divides r withRemainder r
  DivRem𝐒 : {x : ℕ} → {y : ℕ} → {r : ℕ} → (x divides y withRemainder r) → (x divides (x + y) withRemainder r)
