module Numeral.Natural.Prime{ℓ} where

import Lvl
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}
open import Numeral.Natural
open import Numeral.Natural.Divisibility{ℓ}
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Relation.Order{ℓ}
open import Numeral.Natural.Relation.Order.Theorems{ℓ}
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Proofs{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}

-- A prime number is a number `n` in which its divisors are only `{1,n}`.
record Prime(n : ℕ) : Stmt where
  constructor Prime-intro
  field
    ⦃ non-zero ⦄ : (n ≢ 0)
    ⦃ non-one  ⦄ : (n ≢ 1)
    proof        : ∀{x} → (x ∣ n) → (x ≡ 1)∨(x ≡ n)
-- ∀{x y : ℕ} → (n ∣ (x ⋅ y)) → (n ∣ x) ∨ (n ∣ y)
-- ∀{x y} → (x ≢ 0)∧(x ≢ 1) → (y ≢ 0)∧(y ≢ 1) → ¬(x ⋅ y ≡ n)

-- PrimeFactor(n)(p) means that `p` is a prime factor of `n`.
record PrimeFactor(n : ℕ) (p : ℕ) : Stmt where
  field
    ⦃ prime ⦄  : Prime(p)
    ⦃ factor ⦄ : (p ∣ n)

instance
  [0]-nonprime : ¬(Prime(0))
  [0]-nonprime (Prime-intro ⦃ n≢0 ⦄ ⦃ _ ⦄ _) = (n≢0)([≡]-intro)
  -- [0]-nonprime (Prime-intro _) = infer (TODO: Consider making (¬_) have an implicit argument: (¬_ = ⦃ _ : X ⦄ → ⊥). Not sure if it can be infered though)

instance
  [1]-nonprime : ¬(Prime(1))
  [1]-nonprime (Prime-intro ⦃ _ ⦄ ⦃ n≢1 ⦄ _) = (n≢1)([≡]-intro)
  -- [1]-nonprime (Prime-intro _) = infer

{-
instance
  [2]-prime : Prime(2)
  [2]-prime = Prime-intro ⦃ [𝐒]-not-0 ⦄ ⦃ [𝐒]-not-0 ∘ [𝐒]-injectivity ⦄ (divisor-proof) where
    divisor-proof : ∀{x} → (x ∣ 2) → (x ≡ 1)∨(x ≡ 2)
    divisor-proof{0} (0div2) = [⊥]-elim([0]-divides-not(0div2))
    divisor-proof{1} (1div2) = [∨]-introₗ ([≡]-intro)
    divisor-proof{2} (2div2) = [∨]-introᵣ ([≡]-intro)
    divisor-proof{𝐒(𝐒(𝐒(n)))} (xdiv2) = [⊥]-elim(divides-not-lower-limit([∃]-intro(n) ⦃ [+]-commutativity{3}{n} ⦄) (xdiv2))

instance
  [3]-prime : Prime(3)
  [3]-prime = Prime-intro ⦃ [𝐒]-not-0 ⦄ ⦃ [𝐒]-not-0 ∘ [𝐒]-injectivity ⦄ (divisor-proof) where
    divisor-proof : ∀{x} → (x ∣ 3) → (x ≡ 1)∨(x ≡ 3)
    divisor-proof{0} (0div3) = [⊥]-elim([0]-divides-not(0div3))
    divisor-proof{1} (1div3) = [∨]-introₗ ([≡]-intro)
    divisor-proof{2} (Div𝐒())
    divisor-proof{3} (3div3) = [∨]-introᵣ ([≡]-intro)
    divisor-proof{𝐒(𝐒(𝐒(𝐒(n))))} (xdiv3) = [⊥]-elim(divides-not-lower-limit([∃]-intro(n) ⦃ [+]-commutativity{4}{n} ⦄) (xdiv3))

instance
  [4]-nonprime : ¬(Prime(4))
  [4]-nonprime (Prime-intro ⦃ _ ⦄ ⦃ _ ⦄ (xdiv4→x1xn)) = [∨]-elim (\()) (\()) (xdiv4→x1xn{2} (DivN(2))) where

instance
  [5]-prime : Prime(5)
  [5]-prime = Prime-intro ⦃ [𝐒]-not-0 ⦄ ⦃ [𝐒]-not-0 ∘ [𝐒]-injectivity ⦄ (divisor-proof) where
    divisor-proof : ∀{x} → (x ∣ 5) → (x ≡ 1)∨(x ≡ 5)
    divisor-proof{0} (0div5) = [⊥]-elim([0]-divides-not(0div5))
    divisor-proof{1} (1div5) = [∨]-introₗ ([≡]-intro)
    divisor-proof{2} (Div𝐒(Div𝐒()))
    divisor-proof{3} (Div𝐒())
    divisor-proof{4} (Div𝐒())
    divisor-proof{5} (5div5) = [∨]-introᵣ ([≡]-intro)
    divisor-proof{𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(n))))))} (xdiv5) = [⊥]-elim(divides-not-lower-limit([∃]-intro(n) ⦃ [+]-commutativity{6}{n} ⦄) (xdiv5))

instance
  [6]-nonprime : ¬(Prime(6))
  [6]-nonprime (Prime-intro ⦃ _ ⦄ ⦃ _ ⦄ (xdiv6→x1xn)) = [∨]-elim (\()) (\()) (xdiv6→x1xn{2} (DivN(3))) where

instance
  [7]-prime : Prime(7)
  [7]-prime = Prime-intro ⦃ [𝐒]-not-0 ⦄ ⦃ [𝐒]-not-0 ∘ [𝐒]-injectivity ⦄ (divisor-proof) where
    divisor-proof : ∀{x} → (x ∣ 7) → (x ≡ 1)∨(x ≡ 7)
    divisor-proof{0} (0div7) = [⊥]-elim([0]-divides-not(0div7))
    divisor-proof{1} (1div7) = [∨]-introₗ ([≡]-intro)
    divisor-proof{2} (Div𝐒(Div𝐒(Div𝐒())))
    divisor-proof{3} (Div𝐒(Div𝐒()))
    divisor-proof{4} (Div𝐒())
    divisor-proof{5} (Div𝐒())
    divisor-proof{6} (Div𝐒())
    divisor-proof{7} (7div7) = [∨]-introᵣ ([≡]-intro)
    divisor-proof{𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(n))))))))} (xdiv7) = [⊥]-elim(divides-not-lower-limit([∃]-intro(n) ⦃ [+]-commutativity{8}{n} ⦄) (xdiv7))
-}
