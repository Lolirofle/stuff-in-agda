module Numeral.Natural.Prime{ℓ} where

import Lvl
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}
open import Numeral.Natural
open import Numeral.Natural.Relation.Divisibility{ℓ}
open import Numeral.Natural.Relation.Divisibility.Proofs{ℓ}
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Relation.Order{ℓ}
open import Numeral.Natural.Relation.Order.Proofs{ℓ}
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Proofs{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}

-- A prime number is a number `n` in which its divisors are only `{1,n}`.
record Prime(n : ℕ) : Stmt where
  constructor Prime-intro
  field
    ⦃ non-one  ⦄ : (n ≢ 1)
    proof        : ∀{x} → (𝐒(x) ∣ n) → (𝐒(x) ≡ 1)∨(𝐒(x) ≡ n)
-- ∀{x} → (x ∣ n) → (x ≡ 1)∨(x ≡ n)
-- ∀{x y : ℕ} → (n ∣ (x ⋅ y)) → (n ∣ x) ∨ (n ∣ y)
-- ∀{x y} → (x ≢ 0)∧(x ≢ 1) → (y ≢ 0)∧(y ≢ 1) → ¬(x ⋅ y ≡ n)

-- PrimeFactor(n)(p) means that `p` is a prime factor of `n`.
record PrimeFactor(n : ℕ) (p : ℕ) : Stmt where
  field
    ⦃ prime ⦄  : Prime(p)
    ⦃ factor ⦄ : (p ∣ n)

-- greater-prime-existence : ∀{p} → Prime(p) → ∃(p₂ ↦ Prime(p₂) ∧ (p₂ > p))

-- TODO: https://math.stackexchange.com/questions/2786458/a-formal-statement-of-the-fundamental-theorem-of-arithmetic
PrimeMultiset = Set
PrimeMultiSet = ((p : ℕ) → ⦃ _ : Prime(p) ⦄ → ℕ)

instance
  [0]-nonprime : ¬(Prime(0))
  [0]-nonprime (Prime-intro ⦃ _ ⦄ proof) with proof{2} (Div𝟎)
  ... | [∨]-introₗ()
  ... | [∨]-introᵣ()
  -- [0]-nonprime (Prime-intro _) = infer (TODO: Consider making (¬_) have an implicit argument: (¬_ = ⦃ _ : X ⦄ → ⊥). Not sure if it can be infered though)

instance
  [1]-nonprime : ¬(Prime(1))
  [1]-nonprime (Prime-intro ⦃ n≢1 ⦄ _) = (n≢1)([≡]-intro)

-- Prime-non-intro : (n : ℕ) → ∀{x y} → ⦃ _ : 𝐒(x) ⋅ y ≡ n ⦄ → (¬ Prime(n))
-- Prime-non-intro(n) {x}{y} (Prime-intro ⦃ _ ⦄ (xdiv4→x1xn)) = [∨]-elim (\()) (\()) (xdiv4→x1xn{x} (DivN(y)))

{-
Prime-non-intro : (n : ℕ) → ∀{x y} → ⦃ _ : x ⋅ y ≡ n ⦄ → (¬ Prime(n))
Prime-non-intro(0) = [0]-nonprime
Prime-non-intro(1) = [1]-nonprime
Prime-non-intro(𝐒(𝐒(n))) {𝐒(x)}{y} ⦃ proof ⦄ (Prime-intro only) with only(divides-intro-alt{y}{𝐒(𝐒(n))}{𝐒(x)} ⦃ proof ⦄)
... | [∨]-introₗ([≡]-intro) = [⊥]-elim(proof)
... | [∨]-introᵣ()
-}

instance
  [2]-prime : Prime(2)
  [2]-prime = Prime-intro ⦃ [𝐒]-not-0 ∘ [𝐒]-injectivity ⦄ (divisor-proof) where
    divisor-proof : ∀{x} → (𝐒(x) ∣ 2) → (𝐒(x) ≡ 1)∨(𝐒(x) ≡ 2)
    divisor-proof{0} (1div2) = [∨]-introₗ ([≡]-intro)
    divisor-proof{1} (2div2) = [∨]-introᵣ ([≡]-intro)
    divisor-proof{𝐒(𝐒(n))}   = [⊥]-elim ∘ [𝐒]-not-0 ∘ [≤]ₗ[+] ∘ divides-upper-limit

instance
  [3]-prime : Prime(3)
  [3]-prime = Prime-intro ⦃ [𝐒]-not-0 ∘ [𝐒]-injectivity ⦄ (divisor-proof) where
    divisor-proof : ∀{x} → (𝐒(x) ∣ 3) → (𝐒(x) ≡ 1)∨(𝐒(x) ≡ 3)
    divisor-proof{0} (1div3) = [∨]-introₗ ([≡]-intro)
    divisor-proof{1} (Div𝐒())
    divisor-proof{2} (3div3) = [∨]-introᵣ ([≡]-intro)
    divisor-proof{𝐒(𝐒(𝐒(n)))} = [⊥]-elim ∘ [𝐒]-not-0 ∘ [≤]ₗ[+] ∘ divides-upper-limit

instance
  [4]-nonprime : ¬(Prime(4))
  [4]-nonprime (Prime-intro ⦃ _ ⦄ (xdiv4→x1xn)) = [∨]-elim (\()) (\()) (xdiv4→x1xn{1} (DivN(2)))

instance
  [5]-prime : Prime(5)
  [5]-prime = Prime-intro ⦃ [𝐒]-not-0 ∘ [𝐒]-injectivity ⦄ (divisor-proof) where
    divisor-proof : ∀{x} → (𝐒(x) ∣ 5) → (𝐒(x) ≡ 1)∨(𝐒(x) ≡ 5)
    divisor-proof{0} (1div5) = [∨]-introₗ ([≡]-intro)
    divisor-proof{1} (Div𝐒(Div𝐒()))
    divisor-proof{2} (Div𝐒())
    divisor-proof{3} (Div𝐒())
    divisor-proof{4} (5div5) = [∨]-introᵣ ([≡]-intro)
    divisor-proof{𝐒(𝐒(𝐒(𝐒(𝐒(n)))))} = [⊥]-elim ∘ [𝐒]-not-0 ∘ [≤]ₗ[+] ∘ divides-upper-limit

instance
  [6]-nonprime : ¬(Prime(6))
  [6]-nonprime (Prime-intro ⦃ _ ⦄ (xdiv6→x1xn)) = [∨]-elim (\()) (\()) (xdiv6→x1xn{1} (DivN(3)))

instance
  [7]-prime : Prime(7)
  [7]-prime = Prime-intro ⦃ [𝐒]-not-0 ∘ [𝐒]-injectivity ⦄ (divisor-proof) where
    divisor-proof : ∀{x} → (𝐒(x) ∣ 7) → (𝐒(x) ≡ 1)∨(𝐒(x) ≡ 7)
    divisor-proof{0} (1div7) = [∨]-introₗ ([≡]-intro)
    divisor-proof{1} (Div𝐒(Div𝐒(Div𝐒())))
    divisor-proof{2} (Div𝐒(Div𝐒()))
    divisor-proof{3} (Div𝐒())
    divisor-proof{4} (Div𝐒())
    divisor-proof{5} (Div𝐒())
    divisor-proof{6} (7div7) = [∨]-introᵣ ([≡]-intro)
    divisor-proof{𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(n)))))))} = [⊥]-elim ∘ [𝐒]-not-0 ∘ [≤]ₗ[+] ∘ divides-upper-limit

instance
  [8]-nonprime : ¬(Prime(8))
  [8]-nonprime (Prime-intro ⦃ _ ⦄ (xdiv8→x1xn)) = [∨]-elim (\()) (\()) (xdiv8→x1xn{1} (DivN(4)))
