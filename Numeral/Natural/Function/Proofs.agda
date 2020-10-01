module Numeral.Natural.Function.Proofs where

import      Lvl
open import Data.Tuple
open import Functional
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Numeral.Natural
open import Numeral.Natural.Function
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function.Domain
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity

max-0ₗ : ∀{b} → (max 𝟎 b ≡ b)
max-0ₗ {𝟎}   = [≡]-intro
max-0ₗ {𝐒 b} = [≡]-intro
{-# REWRITE max-0ₗ #-}

max-0ᵣ : ∀{a} → (max a 𝟎 ≡ a)
max-0ᵣ {𝟎}   = [≡]-intro
max-0ᵣ {𝐒 a} = [≡]-intro
{-# REWRITE max-0ᵣ #-}

min-0ₗ : ∀{b} → (min 𝟎 b ≡ 𝟎)
min-0ₗ {𝟎}   = [≡]-intro
min-0ₗ {𝐒 b} = [≡]-intro
{-# REWRITE min-0ₗ #-}

min-0ᵣ : ∀{a} → (min a 𝟎 ≡ 𝟎)
min-0ᵣ {𝟎}   = [≡]-intro
min-0ᵣ {𝐒 a} = [≡]-intro
{-# REWRITE min-0ᵣ #-}

instance
  min-idempotence : Idempotence(min)
  min-idempotence = intro proof where
    proof : Names.Idempotence(min)
    proof{𝟎}   = [≡]-intro
    proof{𝐒 x} = [≡]-with(𝐒) (proof{x})

instance
  max-idempotence : Idempotence(max)
  max-idempotence = intro proof where
    proof : Names.Idempotence(max)
    proof{𝟎}   = [≡]-intro
    proof{𝐒 x} = [≡]-with(𝐒) (proof{x})

max-elementary : ∀{a b} → (max(a)(b) ≡ a + (b −₀ a))
max-elementary {𝟎}    {𝟎}    = [≡]-intro
max-elementary {𝟎}    {𝐒(b)} = [≡]-intro
max-elementary {𝐒(a)} {𝟎}    = [≡]-intro
max-elementary {𝐒(a)} {𝐒(b)} = [≡]-with(𝐒) (max-elementary {a} {b})

min-elementary : ∀{a b} → (min(a)(b) ≡ b −₀ (b −₀ a))
min-elementary {𝟎}    {𝟎}    = [≡]-intro
min-elementary {𝟎}    {𝐒(b)} = [≡]-intro
min-elementary {𝐒(a)} {𝟎}    = [≡]-intro
min-elementary {𝐒(a)} {𝐒(b)} = ([≡]-with(𝐒) (min-elementary {a} {b})) 🝖 (symmetry(_≡_) ([↔]-to-[→] [−₀][𝐒]ₗ-equality ([−₀]-lesser {b}{a})))

instance
  min-commutativity : Commutativity(min)
  Commutativity.proof(min-commutativity) = proof where
    proof : Names.Commutativity(min)
    proof{𝟎}   {𝟎}    = [≡]-intro
    proof{𝟎}   {𝐒(b)} = [≡]-intro
    proof{𝐒(a)}{𝟎}    = [≡]-intro
    proof{𝐒(a)}{𝐒(b)} = [≡]-with(𝐒) (proof{a}{b})

instance
  min-associativity : Associativity(min)
  Associativity.proof(min-associativity) = proof where
    proof : Names.Associativity(min)
    proof{𝟎}   {𝟎}   {𝟎}    = [≡]-intro
    proof{𝟎}   {𝟎}   {𝐒(c)} = [≡]-intro
    proof{𝟎}   {𝐒(b)}{𝟎}    = [≡]-intro
    proof{𝐒(a)}{𝟎}   {𝟎}    = [≡]-intro
    proof{𝟎}   {𝐒(b)}{𝐒(c)} = [≡]-intro
    proof{𝐒(a)}{𝟎}   {𝐒(c)} = [≡]-intro
    proof{𝐒(a)}{𝐒(b)}{𝟎}    = [≡]-intro
    proof{𝐒(a)}{𝐒(b)}{𝐒(c)} = [≡]-with(𝐒) (proof{a}{b}{c})
    -- min(min(𝐒x)(𝐒y))(𝐒z)
    -- = min(𝐒min(x)(y))(𝐒z)
    -- = 𝐒(min(min(x)(y))(z))
    -- = 𝐒(min(x)(min(y)(z)))
    -- = min(𝐒x)(𝐒min(y)(z))
    -- = min(𝐒x)(min(𝐒y)(𝐒z)

instance
  min-orderₗ : ∀{a b} → (min(a)(b) ≤ a)
  min-orderₗ {𝟎}   {𝟎}    = [≤]-minimum {𝟎}
  min-orderₗ {𝐒(a)}{𝟎}    = [≤]-minimum {𝐒(a)}
  min-orderₗ {𝟎}   {𝐒(b)} = [≤]-minimum {𝟎}
  min-orderₗ {𝐒(a)}{𝐒(b)} = [≤]-with-[𝐒] ⦃ min-orderₗ {a}{b} ⦄

instance
  min-orderᵣ : ∀{a b} → (min(a)(b) ≤ b)
  min-orderᵣ {𝟎}   {𝟎}    = [≤]-minimum {𝟎}
  min-orderᵣ {𝐒(a)}{𝟎}    = [≤]-minimum {𝟎}
  min-orderᵣ {𝟎}   {𝐒(b)} = [≤]-minimum {𝐒(b)}
  min-orderᵣ {𝐒(a)}{𝐒(b)} = [≤]-with-[𝐒] ⦃ min-orderᵣ {a}{b} ⦄

min-arg : ∀{a b} → (min(a)(b) ≡ a) ∨ (min(a)(b) ≡ b)
min-arg {𝟎}   {𝟎}    = [∨]-introₗ([≡]-intro)
min-arg {𝟎}   {𝐒(b)} = [∨]-introₗ([≡]-intro)
min-arg {𝐒(a)}{𝟎}    = [∨]-introᵣ([≡]-intro)
min-arg {𝐒(a)}{𝐒(b)} = constructive-dilemma ([≡]-with(𝐒)) ([≡]-with(𝐒)) (min-arg {a}{b})

min-defₗ : ∀{a b} → (a ≤ b) ↔ (min(a)(b) ≡ a)
min-defₗ {a}{b} = [↔]-intro (l{a}{b}) (r{a}{b}) where
  l : ∀{a b} → (a ≤ b) ← (min(a)(b) ≡ a)
  l {𝟎}   {𝟎}    _      = [≤]-minimum {𝟎}
  l {𝟎}   {𝐒(b)} _      = [≤]-minimum {𝐒(b)}
  l {𝐒(_)}{𝟎}    ()
  l {𝐒(a)}{𝐒(b)} minaba = [≤]-with-[𝐒] ⦃ l{a}{b} (injective(𝐒) (minaba)) ⦄

  r : ∀{a b} → (a ≤ b) → (min(a)(b) ≡ a)
  r {𝟎}   {𝟎}    _                     = [≡]-intro
  r {𝟎}   {𝐒(b)} _                     = [≡]-intro
  r {𝐒(_)}{𝟎}    ()
  r {𝐒(a)}{𝐒(b)} ([≤]-with-[𝐒] ⦃ ab ⦄) = [≡]-with(𝐒) (r{a}{b} (ab))

min-defᵣ : ∀{a b} → (b ≤ a) ↔ (min(a)(b) ≡ b)
min-defᵣ {a}{b} = [≡]-substitutionᵣ (commutativity(min)) {expr ↦ (b ≤ a) ↔ (expr ≡ b)} (min-defₗ{b}{a})


instance
  max-commutativity : Commutativity(max)
  Commutativity.proof(max-commutativity) = proof where
    proof : Names.Commutativity(max)
    proof{𝟎}   {𝟎}    = [≡]-intro
    proof{𝟎}   {𝐒(b)} = [≡]-intro
    proof{𝐒(a)}{𝟎}    = [≡]-intro
    proof{𝐒(a)}{𝐒(b)} = [≡]-with(𝐒) (proof{a}{b})

instance
  max-associativity : Associativity(max)
  Associativity.proof(max-associativity) = proof where
    proof : Names.Associativity(max)
    proof{𝟎}   {𝟎}   {𝟎}    = [≡]-intro
    proof{𝟎}   {𝟎}   {𝐒(c)} = [≡]-intro
    proof{𝟎}   {𝐒(b)}{𝟎}    = [≡]-intro
    proof{𝐒(a)}{𝟎}   {𝟎}    = [≡]-intro
    proof{𝟎}   {𝐒(b)}{𝐒(c)} = [≡]-intro
    proof{𝐒(a)}{𝟎}   {𝐒(c)} = [≡]-intro
    proof{𝐒(a)}{𝐒(b)}{𝟎}    = [≡]-intro
    proof{𝐒(a)}{𝐒(b)}{𝐒(c)} = [≡]-with(𝐒) (proof{a}{b}{c})

-- max-[+]-distributivityₗ : Distributivityₗ(max)
-- max-[+]-distributivityᵣ : Distributivityᵣ(max)

instance
  max-orderₗ : ∀{a b} → (max(a)(b) ≥ a)
  max-orderₗ {𝟎}   {𝟎}    = [≤]-minimum {max(𝟎)(𝟎)}
  max-orderₗ {𝐒(a)}{𝟎}    = reflexivity(_≥_)
  max-orderₗ {𝟎}   {𝐒(b)} = [≤]-minimum {max(𝟎)(𝐒(b))}
  max-orderₗ {𝐒(a)}{𝐒(b)} = [≤]-with-[𝐒] ⦃ max-orderₗ {a}{b} ⦄

instance
  max-orderᵣ : ∀{a b} → (max(a)(b) ≥ b)
  max-orderᵣ {𝟎}   {𝟎}    = [≤]-minimum {max(𝟎)(𝟎)}
  max-orderᵣ {𝐒(a)}{𝟎}    = [≤]-minimum {max(𝐒(a))(𝟎)}
  max-orderᵣ {𝟎}   {𝐒(b)} = reflexivity(_≥_)
  max-orderᵣ {𝐒(a)}{𝐒(b)} = [≤]-with-[𝐒] ⦃ max-orderᵣ {a}{b} ⦄

max-arg : ∀{a b} → (max(a)(b) ≡ a)∨(max(a)(b) ≡ b)
max-arg {𝟎}   {𝟎}    = [∨]-introₗ([≡]-intro)
max-arg {𝟎}   {𝐒(b)} = [∨]-introᵣ([≡]-intro)
max-arg {𝐒(a)}{𝟎}    = [∨]-introₗ([≡]-intro)
max-arg {𝐒(a)}{𝐒(b)} = constructive-dilemma ([≡]-with(𝐒)) ([≡]-with(𝐒)) (max-arg {a}{b})

max-defₗ : ∀{a b} → (a ≥ b) ↔ (max(a)(b) ≡ a)
max-defₗ {a}{b} = [↔]-intro (l{a}{b}) (r{a}{b}) where
  l : ∀{a b} → (a ≥ b) ← (max(a)(b) ≡ a)
  l {𝟎}   {𝟎}    _      = [≤]-minimum {𝟎}
  l {𝟎}   {𝐒(_)} ()
  l {𝐒(a)}{𝟎}    _      = [≤]-minimum {𝐒(a)}
  l {𝐒(a)}{𝐒(b)} maxaba = [≤]-with-[𝐒] ⦃ l{a}{b}(injective(𝐒) (maxaba)) ⦄

  r : ∀{a b} → (a ≥ b) → (max(a)(b) ≡ a)
  r {𝟎}   {𝟎}    _                     = [≡]-intro
  r {𝟎}   {𝐒(_)} ()
  r {𝐒(_)}{𝟎}    _                     = [≡]-intro
  r {𝐒(a)}{𝐒(b)} ([≤]-with-[𝐒] ⦃ ab ⦄) = [≡]-with(𝐒) (r{a}{b} (ab))

max-defᵣ : ∀{a b} → (b ≥ a) ↔ (max(a)(b) ≡ b)
max-defᵣ {a}{b} = [≡]-substitutionᵣ (commutativity(max)) {expr ↦ (b ≥ a) ↔ (expr ≡ b)} (max-defₗ{b}{a})

min-with-max : ∀{a b} → (min(a)(b) ≡ (a + b) −₀ max(a)(b))
min-with-max {a}{b} =
  min(a)(b)                 🝖-[ min-elementary{a}{b} ]
  b −₀ (b −₀ a)             🝖-[ [−₀][+]ₗ-nullify {a}{b}{b −₀ a} ]-sym
  (a + b) −₀ (a + (b −₀ a)) 🝖-[ [≡]-with((a + b) −₀_) (max-elementary{a}{b}) ]-sym
  (a + b) −₀ max(a)(b)      🝖-end

max-with-min : ∀{a b} → (max(a)(b) ≡ (a + b) −₀ min(a)(b))
max-with-min {a}{b} with [≤][>]-dichotomy {a}{b}
... | [∨]-introₗ ab =
  max(a)(b)            🝖-[ [↔]-to-[→] max-defᵣ ab ]
  b                    🝖-[ [−₀]ₗ[+]ₗ-nullify {a}{b} ]-sym
  (a + b) −₀ a         🝖-[ [≡]-with((a + b) −₀_) ([↔]-to-[→] min-defₗ ab) ]-sym
  (a + b) −₀ min(a)(b) 🝖-end
... | [∨]-introᵣ 𝐒ba with ba ← [≤]-predecessor 𝐒ba =
  max(a)(b)            🝖-[ [↔]-to-[→] max-defₗ ba ]
  a                    🝖-[ [−₀]ₗ[+]ᵣ-nullify {a}{b} ]-sym
  (a + b) −₀ b         🝖-[ [≡]-with((a + b) −₀_) ([↔]-to-[→] min-defᵣ ba) ]-sym
  (a + b) −₀ min(a)(b) 🝖-end

[≤]-conjunction-min : ∀{a b c} → ((a ≤ b) ∧ (a ≤ c)) ↔ (a ≤ min b c)
[≤]-conjunction-min {a}{b}{c} = [↔]-intro (a≤bc ↦ [∧]-intro (a≤bc 🝖 min-orderₗ) (a≤bc 🝖 min-orderᵣ)) (uncurry r) where
  r : ∀{a b c} → (a ≤ b) → (a ≤ c) → (a ≤ min b c)
  r {.0}     {b}      {c}     [≤]-minimum  [≤]-minimum = [≤]-minimum
  r {.(𝐒 a)} {.(𝐒 b)} {.(𝐒 c)} ([≤]-with-[𝐒] {a} {b} ⦃ ab ⦄) ([≤]-with-[𝐒] {y = c} ⦃ ac ⦄) = [≤]-with-[𝐒] ⦃ r {a}{b}{c} ab ac ⦄

[≤]-conjunction-max : ∀{a b c} → ((a ≤ c) ∧ (b ≤ c)) ↔ (max a b ≤ c)
[≤]-conjunction-max {a}{b}{c} = [↔]-intro (ab≤c ↦ [∧]-intro (max-orderₗ 🝖 ab≤c) ((max-orderᵣ 🝖 ab≤c))) (uncurry r) where
  r : ∀{a b c} → (a ≤ c) → (b ≤ c) → (max a b ≤ c)
  r {.0}     {b@(𝐒 _)}{c}      [≤]-minimum  bc           = bc
  r {a}      {.0}     {c}      ac           [≤]-minimum  = ac
  r {𝐒 a} {𝐒 b} {𝐒 c} ([≤]-with-[𝐒] ⦃ ac ⦄) ([≤]-with-[𝐒] ⦃ bc ⦄) = [≤]-with-[𝐒] ⦃ r {a}{b}{c} ac bc ⦄

[≤]-disjunction-min : ∀{a b c} → ((a ≤ c) ∨ (b ≤ c)) ↔ (min a b ≤ c)
[≤]-disjunction-min = [↔]-intro
  (ab≤c ↦ [∨]-elim2
    ((_🝖 ab≤c) ∘ [≡]-to-[≤] ∘ symmetry(_≡_))
    ((_🝖 ab≤c) ∘ [≡]-to-[≤] ∘ symmetry(_≡_))
    min-arg
  )
  ([∨]-elim
    (min-orderₗ 🝖_)
    (min-orderᵣ 🝖_)
  )

[≤]-disjunction-max : ∀{a b c} → ((a ≤ b) ∨ (a ≤ c)) ↔ (a ≤ max b c)
[≤]-disjunction-max = [↔]-intro
  (a≤bc ↦ [∨]-elim2
    ((_🝖 a≤bc) ∘ [≡]-to-[≤])
    ((_🝖 a≤bc) ∘ [≡]-to-[≤])
    max-arg
  )
  ([∨]-elim
    (_🝖 max-orderₗ)
    (_🝖 max-orderᵣ)
  )

min-order-max : ∀{a b} → (min(a)(b) ≤ max(a)(b))
min-order-max {𝟎}   {b}   = [≤]-minimum
min-order-max {𝐒 a} {𝟎}   = [≤]-minimum
min-order-max {𝐒 a} {𝐒 b} = [≤]-with-[𝐒] ⦃ min-order-max {a}{b} ⦄

max-order-[+] : ∀{a b} → (max(a)(b) ≤ a + b)
max-order-[+] {a}{b} = [↔]-to-[→] [≤]-conjunction-max ([∧]-intro [≤]-of-[+]ₗ ([≤]-of-[+]ᵣ {a}{b}))
