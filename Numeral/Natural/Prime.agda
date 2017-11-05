module Numeral.Natural.Prime{ℓ} where

import Lvl
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}
open import Numeral.Natural
open import Numeral.Natural.Divisibility{ℓ}
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Relation{ℓ}
open import Numeral.Natural.Relation.Properties{ℓ}
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Theorems{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}

data Prime(n : ℕ) : Stmt where
  Prime-intro : (n ≢ 0) → (n ≢ 1) → (∀{x} → (x divides n) → (x ≡ 1)∨(x ≡ n)) → Prime(n)
-- ∀{x y : ℕ} → (n divides (x ⋅ y)) → (n divides x) ∨ (n divides y)
-- ∀{x y} → (x ≢ 0)∧(x ≢ 1) → (y ≢ 0)∧(y ≢ 1) → ¬(x ⋅ y ≡ n)

[0]-nonprime : ¬(Prime(0))
[0]-nonprime (Prime-intro (n≢0) _ _) = (n≢0)([≡]-intro)

[1]-nonprime : ¬(Prime(1))
[1]-nonprime (Prime-intro _ (n≢1) _) = (n≢1)([≡]-intro)

[2]-prime : Prime(2)
[2]-prime = Prime-intro ([𝐒]-not-0) ([𝐒]-not-0 ∘ [𝐒]-injectivity) (divisor-proof) where
  divisor-proof : ∀{x} → (x divides 2) → (x ≡ 1)∨(x ≡ 2)
  divisor-proof{0} (0div2) = [⊥]-elim([0]-divides-not(0div2))
  divisor-proof{1} (1div2) = [∨]-introₗ ([≡]-intro)
  divisor-proof{2} (2div2) = [∨]-introᵣ ([≡]-intro)
  divisor-proof{𝐒(𝐒(𝐒(n)))} (xdiv2) = [⊥]-elim(divides-not-lower-limit([∃]-intro(n) ([+]-commutativity{3}{n})) (xdiv2))

-- TODO: Related to below: How to prove this?
-- test22 : ¬(2 divides 3)
-- test22 (Div𝐒 ())
-- test22 (Div𝐒 (div)) = [⊥]-elim(divides-not-lower-limit([∃]-intro(1) ([+]-commutativity{2}{1})) (div))

-- TODO: Is this a bug? Cannot deconstruct (2 divides 3) to (2 divides 1) using Div𝐒?
-- [3]-prime : Prime(3)
-- [3]-prime = Prime-intro ([𝐒]-not-0) ([𝐒]-not-0 ∘ [𝐒]-injectivity) (divisor-proof) where
--   divisor-proof : ∀{x} → (x divides 3) → (x ≡ 1)∨(x ≡ 3)
--   divisor-proof{0} (0div3) = [⊥]-elim([0]-divides-not(0div3))
--   divisor-proof{1} (1div3) = [∨]-introₗ ([≡]-intro)
--   divisor-proof{3} (3div3) = [∨]-introᵣ ([≡]-intro)
--   divisor-proof{𝐒(𝐒(𝐒(𝐒(n))))} (xdiv3) = [⊥]-elim(divides-not-lower-limit([∃]-intro(n) ([+]-commutativity{4}{n})) (xdiv3))
