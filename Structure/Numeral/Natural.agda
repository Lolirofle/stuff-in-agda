module Structure.Numeral.Natural where

open import Lang.Instance
import      Lvl
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Setoid
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Operator
open import Structure.Relator
open import Structure.Setoid
open import Syntax.Function
open import Type

private variable ℓₒ ℓₗ ℓₑ ℓₗ₁ ℓₗ₂ : Lvl.Level
private variable N : Type{ℓₒ}

module _ ⦃ equiv : Equiv{ℓₑ}(N) ⦄ where
  private variable 𝟎 : N
  private variable 𝐒 : N → N
  private variable _+_ _⋅_ _^_ : N → N → N

  module _ {ℓ} (𝟎 : N) (𝐒 : N → N) where
    record Induction : Type{ℓₑ Lvl.⊔ Lvl.of(N) Lvl.⊔ Lvl.𝐒(ℓ)} where
      constructor intro
      field proof : (P : N → Type{ℓ}) ⦃ rel : UnaryRelator(P) ⦄ → P(𝟎) → ((n : N) → P(n) → P(𝐒(n))) → ((n : N) → P(n))
    induction = inst-fn Induction.proof

  record Elemental (𝟎 : N) (𝐒 : N → N) : Type{ℓₑ Lvl.⊔ Lvl.of(N)} where
    constructor intro
    field
      ⦃ 𝐒-function ⦄    : Function(𝐒)
      ⦃ 𝐒-injectivity ⦄ : Injective(𝐒)
      𝐒-positivity      : ∀{x} → (𝐒(x) ≢ 𝟎)

  record Addition ⦃ elemn : Elemental(𝟎)(𝐒) ⦄ (_+_ : N → N → N) : Type{ℓₑ Lvl.⊔ Lvl.of(N)} where
    constructor intro
    field
      ⦃ operator ⦄ : BinaryOperator(_+_)
      base : ∀{a}   → (a + 𝟎    ≡ a)
      step : ∀{a b} → (a + 𝐒(b) ≡ 𝐒(a + b))

  record Multiplication ⦃ elemn : Elemental(𝟎)(𝐒) ⦄ ⦃ addi : Addition(_+_) ⦄ (_⋅_ : N → N → N) : Type{ℓₑ Lvl.⊔ Lvl.of(N)} where
    constructor intro
    field
      ⦃ operator ⦄ : BinaryOperator(_⋅_)
      base : ∀{a}   → (a ⋅ 𝟎    ≡ 𝟎)
      step : ∀{a b} → (a ⋅ 𝐒(b) ≡ a + (a ⋅ b))

  record Exponentiation ⦃ elemn : Elemental(𝟎)(𝐒) ⦄ ⦃ addi : Addition(_+_) ⦄ ⦃ multi : Multiplication(_⋅_) ⦄ (_^_ : N → N → N) : Type{ℓₑ Lvl.⊔ Lvl.of(N)} where
    constructor intro
    field
      ⦃ operator ⦄ : BinaryOperator(_^_)
      base : ∀{a}   → (a ^ 𝟎    ≡ 𝐒(𝟎))
      step : ∀{a b} → (a ^ 𝐒(b) ≡ a ⋅ (a ^ b))

  record WeakOrdering ⦃ elemn : Elemental(𝟎)(𝐒) ⦄ {_+_ : N → N → N} ⦃ addi : Addition(_+_) ⦄ (_≤_ : N → N → Type{ℓₗ}) : Type{ℓₑ Lvl.⊔ Lvl.of(N) Lvl.⊔ ℓₗ} where
    constructor intro
    field
      ⦃ relator ⦄ : BinaryRelator(_≤_)
      proof : ∀{a b} → (a ≤ b) ↔ ∃(c ↦ a + c ≡ b)

  module _ ⦃ ind : Induction(𝟎)(𝐒) ⦄ ⦃ elem : Elemental(𝟎)(𝐒) ⦄ where
    open import Structure.Relator.Proofs
    open import Structure.Relator.Properties

    open Elemental(elem)
    open Induction(ind)

    𝟎-or-𝐒 : ∀{x} → (x ≡ 𝟎) ∨ ∃(y ↦ x ≡ 𝐒(y))
    𝟎-or-𝐒 {x} = induction(𝟎)(𝐒)
      (x ↦ (x ≡ 𝟎) ∨ ∃(y ↦ x ≡ 𝐒(y))) ⦃ [∨]-unaryRelator ⦃ rel-P = BinaryRelator.left [≡]-binaryRelator ⦄ ⦃ rel-Q = [∃]-unaryRelator ⦃ rel-P = BinaryRelator.left [≡]-binaryRelator ⦄ ⦄ ⦄
      ([∨]-introₗ (reflexivity(_≡_)))
      (x ↦ [∨]-elim
        (p ↦ [∨]-introᵣ([∃]-intro 𝟎 ⦃ congruence₁(𝐒) p ⦄))
        (\{([∃]-intro y ⦃ p ⦄) → [∨]-introᵣ([∃]-intro (𝐒(y)) ⦃ congruence₁(𝐒) p ⦄)})
      )
      x

{-
  module _ ⦃ ind : Induction(𝟎)(𝐒) ⦄ where
    import      Data.Either as Either
    open import Functional
    open import Numeral.Natural as ℕ using (ℕ)
    open import Relator.Equals renaming (_≡_ to _≡ₑ_)
    open import Structure.Relator.Proofs
    open import Syntax.Number

    from-ℕ : ℕ → N
    from-ℕ (ℕ.𝟎)    = 𝟎
    from-ℕ (ℕ.𝐒(n)) = 𝐒(from-ℕ n)
-}

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

-}
