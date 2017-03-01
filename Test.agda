module Test where

data ℕ : Set where
  ℕ0 : ℕ
  𝑆 : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
x + ℕ0 = x
x + 𝑆(y) = 𝑆(x + y)

_⋅_ : ℕ → ℕ → ℕ
x ⋅ ℕ0 = ℕ0
x ⋅ 𝑆(y) = x + (x ⋅ y)

_−_ : ℕ → ℕ → ℕ
x − ℕ0 = x
ℕ0 − 𝑆(x) = ℕ0
𝑆(x) − 𝑆(y) = x − y

_/_ : ℕ → ℕ → ℕ
ℕ0 / x = ℕ0
x / ℕ0 = ℕ0
𝑆(x) / y =  y + (x / y)

id : (T : Set) → T → T
id _ x = x

------------------------------------------
-- Conjunction
data _∧_ (X : Set) (Y : Set) : Set where
  [∧]-intro : X → Y → (X ∧ Y)

[∧]-elimₗ : {X : Set} → {Y : Set} → (X ∧ Y) → X
[∧]-elimₗ ([∧]-intro x _) = x

[∧]-elimᵣ : {X : Set} → {Y : Set} → (X ∧ Y) → Y
[∧]-elimᵣ ([∧]-intro _ y) = y

------------------------------------------
-- Implication
[→]-elim : {X : Set} → {Y : Set} → X → (X → Y) → Y
[→]-elim x f = f x

infixl 0 _⇒_
_⇒_ : {X : Set} → {Y : Set} → X → (X → Y) → Y
x ⇒ f = [→]-elim x f

------------------------------------------
-- Equivalence
_↔_ : (X : Set) → (Y : Set) → Set
x ↔ y = (x → y) ∧ (y → x)

------------------------------------------
-- Disjunction
-- _∨_ : (X : Set) → (Y : Set) → Set

data Even : ℕ → Set where
  Even0 : Even ℕ0
  Even𝑆 : {x : ℕ} → (Even x) → (Even(𝑆(𝑆(x))))

data Odd : ℕ → Set where
  Odd0 : Odd (𝑆(ℕ0))
  Odd𝑆 : {x : ℕ} → (Odd x) → (Odd(𝑆(𝑆(x))))

ℕ4IsEven : Even(𝑆(𝑆(𝑆(𝑆(ℕ0)))))
ℕ4IsEven = Even0 ⇒ Even𝑆 ⇒ Even𝑆

ℕ5IsOdd : Odd(𝑆(𝑆(𝑆(𝑆(𝑆(ℕ0))))))
ℕ5IsOdd = Odd0 ⇒ Odd𝑆 ⇒ Odd𝑆
