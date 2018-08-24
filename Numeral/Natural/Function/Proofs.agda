module Numeral.Natural.Function.Proofs{ℓ} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Propositional.Theorems{ℓ}
open import Numeral.Natural
open import Numeral.Natural.Function
open import Numeral.Natural.Relation.Order{ℓ}
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Relation.Order.Proofs{ℓ}
open import Relator.Equals{ℓ}
open import Relator.Equals.Proofs{ℓ}
open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}

max-elementary : ∀{a b} → (max(a)(b) ≡ a + (b −₀ a))
max-elementary {𝟎}    {𝟎}    = [≡]-intro
max-elementary {𝟎}    {𝐒(b)} = [≡]-intro
max-elementary {𝐒(a)} {𝟎}    = [≡]-intro
max-elementary {𝐒(a)} {𝐒(b)} = [≡]-with(𝐒) (max-elementary {a} {b})

min-elementary : ∀{a b} → (min(a)(b) ≡ b −₀ (b −₀ a))
min-elementary {𝟎}    {𝟎}    = [≡]-intro
min-elementary {𝟎}    {𝐒(b)} = [≡]-intro
min-elementary {𝐒(a)} {𝟎}    = [≡]-intro
min-elementary {𝐒(a)} {𝐒(b)} = ([≡]-with(𝐒) (min-elementary {a} {b})) 🝖 (symmetry([−₀]-move-[𝐒] ⦃ [−₀]-lesser {b}{a} ⦄))

-- 𝐒(b) −₀ (𝐒(b) −₀ 𝐒(a))
-- 𝐒(b) −₀ (b −₀ a)

min-with-max : ∀{a b} → (min(a)(b) ≡ (a + b) −₀ max(a)(b))
min-with-max {a}{b} =
  min-elementary{a}{b}
  🝖 [−₀][+]ₗ-nullify {a}{b}{b −₀ a}
  🝖 symmetry([≡]-with((a + b) −₀_) (max-elementary{a}{b}))
  -- [≡]-elimᵣ (max-elementary{a}{b}) {expr ↦ (min(a)(b) ≡ (a + b) −₀ expr)} (min-elementary{a}{b})
  -- (a + b) −₀ max(a)(b)
  -- (a + b) −₀ (a + (b −₀ a))
  -- b −₀ (b −₀ a)

-- max-with-min : ∀{a b} → (max(a)(b) ≡ (a + b) −₀ min(a)(b))
-- max-with-min
  -- max(a)(b)
  -- a + (b −₀ a)
  -- (b + a) −₀ (b −₀ (b −₀ a))
  -- (a + b) −₀ (b −₀ (b −₀ a))
  -- (a + b) −₀ min(a)(b)



min-commutativity : Commutativity(min)
min-commutativity{𝟎}   {𝟎}    = [≡]-intro
min-commutativity{𝟎}   {𝐒(b)} = [≡]-intro
min-commutativity{𝐒(a)}{𝟎}    = [≡]-intro
min-commutativity{𝐒(a)}{𝐒(b)} = [≡]-with(𝐒) (min-commutativity{a}{b})

-- {x y z : ℕ} → min(min(x)(y))(z) ≡ min(x)((min(y)(z))
min-associativity : Associativity(min)
min-associativity{𝟎}   {𝟎}   {𝟎}    = [≡]-intro
min-associativity{𝟎}   {𝟎}   {𝐒(c)} = [≡]-intro
min-associativity{𝟎}   {𝐒(b)}{𝟎}    = [≡]-intro
min-associativity{𝐒(a)}{𝟎}   {𝟎}    = [≡]-intro
min-associativity{𝟎}   {𝐒(b)}{𝐒(c)} = [≡]-intro
min-associativity{𝐒(a)}{𝟎}   {𝐒(c)} = [≡]-intro
min-associativity{𝐒(a)}{𝐒(b)}{𝟎}    = [≡]-intro
min-associativity{𝐒(a)}{𝐒(b)}{𝐒(c)} = [≡]-with(𝐒) (min-associativity{a}{b}{c})
  -- min(min(𝐒x)(𝐒y))(𝐒z)
  -- = min(𝐒min(x)(y))(𝐒z)
  -- = 𝐒(min(min(x)(y))(z))
  -- = 𝐒(min(x)(min(y)(z)))
  -- = min(𝐒x)(𝐒min(y)(z))
  -- = min(𝐒x)(min(𝐒y)(𝐒z)

postulate min-orderₗ : ∀{a b} → (min(a)(b) ≤ a)
postulate min-orderᵣ : ∀{a b} → (min(a)(b) ≤ b)

min-arg : ∀{a b} → (min(a)(b) ≡ a) ∨ (min(a)(b) ≡ b)
min-arg {𝟎}   {𝟎}    = [∨]-introₗ([≡]-intro)
min-arg {𝟎}   {𝐒(b)} = [∨]-introₗ([≡]-intro)
min-arg {𝐒(a)}{𝟎}    = [∨]-introᵣ([≡]-intro)
min-arg {𝐒(a)}{𝐒(b)} = constructive-dilemma ([≡]-with(𝐒)) ([≡]-with(𝐒)) (min-arg {a}{b})

postulate min-defₗ : ∀{a b} → (a ≤ b) ↔ (min(a)(b) ≡ a)
postulate min-defᵣ : ∀{a b} → (b ≤ a) ↔ (min(a)(b) ≡ b)



max-commutativity : Commutativity(max)
max-commutativity{𝟎}   {𝟎}    = [≡]-intro
max-commutativity{𝟎}   {𝐒(b)} = [≡]-intro
max-commutativity{𝐒(a)}{𝟎}    = [≡]-intro
max-commutativity{𝐒(a)}{𝐒(b)} = [≡]-with(𝐒) (max-commutativity{a}{b})

max-associativity : Associativity(max)
max-associativity{𝟎}   {𝟎}   {𝟎}    = [≡]-intro
max-associativity{𝟎}   {𝟎}   {𝐒(c)} = [≡]-intro
max-associativity{𝟎}   {𝐒(b)}{𝟎}    = [≡]-intro
max-associativity{𝐒(a)}{𝟎}   {𝟎}    = [≡]-intro
max-associativity{𝟎}   {𝐒(b)}{𝐒(c)} = [≡]-intro
max-associativity{𝐒(a)}{𝟎}   {𝐒(c)} = [≡]-intro
max-associativity{𝐒(a)}{𝐒(b)}{𝟎}    = [≡]-intro
max-associativity{𝐒(a)}{𝐒(b)}{𝐒(c)} = [≡]-with(𝐒) (max-associativity{a}{b}{c})

-- max-[+]-distributivityₗ : Distributivityₗ(max)
-- max-[+]-distributivityᵣ : Distributivityᵣ(max)

postulate max-orderₗ : ∀{a b} → (max(a)(b) ≥ a)
postulate max-orderᵣ : ∀{a b} → (max(a)(b) ≥ b)

max-arg : ∀{a b} → (max(a)(b) ≡ a)∨(max(a)(b) ≡ b)
max-arg {𝟎}   {𝟎}    = [∨]-introₗ([≡]-intro)
max-arg {𝟎}   {𝐒(b)} = [∨]-introᵣ([≡]-intro)
max-arg {𝐒(a)}{𝟎}    = [∨]-introₗ([≡]-intro)
max-arg {𝐒(a)}{𝐒(b)} = constructive-dilemma ([≡]-with(𝐒)) ([≡]-with(𝐒)) (max-arg {a}{b})

postulate max-defₗ : ∀{a b} → (a ≥ b) ↔ (max(a)(b) ≡ b)
postulate max-defᵣ : ∀{a b} → (b ≥ a) ↔ (max(a)(b) ≡ a)
