module Structure.Numeral.Natural where

import      Lvl
-- open import Logic
open import Logic.Predicate
open import Logic.Propositional
-- open import Relator.Ordering
open import Structure.Setoid
-- open import Structure.Relator.Ordering
-- open import Structure.Relator.Properties
open import Structure.Function.Domain
open import Structure.Function
open import Syntax.Function
open import Type

private variable ℓₒ ℓₗ ℓₑ ℓₗ₁ ℓₗ₂ : Lvl.Level
private variable N : Type{ℓₒ}

module _ ⦃ equiv : Equiv{ℓₑ}(N) ⦄ where
  private variable 𝟎 : N
  private variable 𝐒 : N → N
  private variable _+_ _⋅_ _^_ : N → N → N

  record Induction {ℓ} (𝟎 : N) (𝐒 : N → N) : Type{Lvl.of(N) Lvl.⊔ Lvl.𝐒(ℓ)} where
    constructor intro
    field proof : ∀{P : N → Type{ℓ}} → P(𝟎) → ((n : N) → P(n) → P(𝐒(n))) → ((n : N) → P(n))

  record Elemental (𝟎 : N) (𝐒 : N → N) : Type{ℓₑ Lvl.⊔ Lvl.of(N)} where
    constructor intro
    field
      ⦃ 𝐒-function  ⦄   : Function(𝐒)
      ⦃ 𝐒-injectivity ⦄ : Injective(𝐒)
      𝐒-positivity      : ∀{x} → (𝐒(x) ≢ 𝟎)

  record Addition ⦃ elemn : Elemental(𝟎)(𝐒) ⦄ (_+_ : N → N → N) : Type{ℓₑ Lvl.⊔ Lvl.of(N)} where
    constructor intro
    field
      base : ∀{a}   → (a + 𝟎    ≡ a)
      step : ∀{a b} → (a + 𝐒(b) ≡ 𝐒(a + b))

  record Multiplication ⦃ elemn : Elemental(𝟎)(𝐒) ⦄ ⦃ addi : Addition(_+_) ⦄ (_⋅_ : N → N → N) : Type{ℓₑ Lvl.⊔ Lvl.of(N)} where
    constructor intro
    field
      base : ∀{a}   → (a ⋅ 𝟎    ≡ 𝟎)
      step : ∀{a b} → (a ⋅ 𝐒(b) ≡ a + (a ⋅ b))

  record Exponentiation ⦃ elemn : Elemental(𝟎)(𝐒) ⦄ ⦃ addi : Addition(_+_) ⦄ ⦃ multi : Multiplication(_⋅_) ⦄ (_^_ : N → N → N) : Type{ℓₑ Lvl.⊔ Lvl.of(N)} where
    constructor intro
    field
      base : ∀{a}   → (a ^ 𝟎    ≡ 𝐒(𝟎))
      step : ∀{a b} → (a ^ 𝐒(b) ≡ a ⋅ (a ^ b))

  record WeakOrdering ⦃ elemn : Elemental(𝟎)(𝐒) ⦄ {_+_ : N → N → N} ⦃ addi : Addition(_+_) ⦄ (_≤_ : N → N → Type{ℓₗ}) : Type{ℓₑ Lvl.⊔ Lvl.of(N) Lvl.⊔ ℓₗ} where
    constructor intro
    field proof : ∀{a b} → (a ≤ b) ↔ ∃(c ↦ a + c ≡ b)

  -- TODO: Also include the definition of a "naturally ordered semigroup" here

{-
  module _ (_<_ : T → T → Stmt{ℓₗ}) where
    record Minimal : Type{Lvl.of(T) Lvl.⊔ ℓₗ} where
      open From-[<][≡] (_<_) (_≡_)

      field
        ⦃ elemental ⦄ : Elemental
        [<]ₗ-𝟎 : ∀{x} → (𝟎 < x) ↔ (x ≢ 𝟎)
        [<]ᵣ-𝟎 : ∀{x} → (𝟎 ≤ x) -- Minimum in the order (TODO: Is (∀x. x≥0) neccessary? Which means (0<x)∨(0=x))
        [<]ₗ-𝐒 : ∀{x y} → (𝐒(x) < y) ↔ ((x < y)∧(𝐒(x) ≢ y)) -- TODO: Also the definition of (_≤_)?
        [<]ᵣ-𝐒 : ∀{x y} → (x < 𝐒(y)) ↔ (x ≤ y)

      𝟎-or-𝐒 : ∀{x} → (x ≡ 𝟎) ∨ ∃(y ↦ x ≡ 𝐒(y))
      𝟎-or-𝐒 {x} = induction {P = x ↦ (x ≡ 𝟎) ∨ ∃(y ↦ x ≡ 𝐒(y))} ([∨]-introₗ (reflexivity(_≡_))) (\{x} → [∨]-elim (p ↦ [∨]-introᵣ([∃]-intro 𝟎 ⦃ congruence₁(𝐒) p ⦄)) (\{([∃]-intro y ⦃ p ⦄) → [∨]-introᵣ([∃]-intro (𝐒(y)) ⦃ congruence₁(𝐒) p ⦄)})) {x}
-}

{-
module _ ⦃ equiv : Equiv(T) ⦄ {𝟎}{𝐒}{_<_ : T → T → Stmt{ℓₗ}} ⦃ full : Full(𝟎)(𝐒)(_<_) ⦄ where
  open import Numeral.Natural as ℕ using (ℕ)
  open import Type.Properties.Empty

  -- TODO: This is a definition of an isomorphism between any of these and ℕ?

  from-ℕ : ℕ → T
  from-ℕ (ℕ.𝟎)    = 𝟎
  from-ℕ (ℕ.𝐒(n)) = 𝐒(from-ℕ n)

  to-ℕ : T → ℕ
  to-ℕ x = ◊.existence (Full.induction(full) zero succ {x}) where
    zero = intro ⦃ ℕ.𝟎 ⦄
    succ = \{(intro ⦃ n ⦄) → intro ⦃ ℕ.𝐒(n) ⦄}

  -}
