module Structure.Function.Multi where

open import Data
open import Data.Boolean
open import Function.DomainRaise using (_→̂_)
open import Function.Multi
open import Functional
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Sets.Setoid.Uniqueness
open import Sets.Setoid hiding (Function)
open import Syntax.Number
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level

module Names where
  -- Function₊ : (f : )

  module _ {X : Type{ℓ₁}} {Y : Type{ℓ₂}} ⦃ _ : Equiv(Y) ⦄ where
    -- Definition of the relation between a function and an operation that says:
    -- The function preserves the operation.
    -- Often used when defining homomorphisms.
    -- Examples:
    --   Preserving(1) (f)(g₁)(g₂)
    --   = (∀{x} → (f ∘₂ g₁)(x) ≡ (g₂ on₃ f)(x))
    --   = (∀{x} → (f(g₁(x)) ≡ g₂(f(x)))
    --   Preserving(2) (f)(g₁)(g₂)
    --   = (∀{x y} → (f ∘₂ g₁)(x)(y) ≡ (g₂ on₃ f)(x)(y))
    --   = (∀{x y} → (f(g₁ x y) ≡ g₂ (f(x)) (f(y)))
    --   Preserving(3) (f)(g₁)(g₂)
    --   = (∀{x y z} → (f ∘₃ g₁)(x)(y)(z) ≡ (g₂ on₃ f)(x)(y)(z))
    --   = (∀{x y z} → (f(g₁ x y z) ≡ g₂ (f(x)) (f(y)) (f(z))))
    Preserving : (n : ℕ) → (f : X → Y) → (X →̂ X)(n) → (Y →̂ Y)(n) → Stmt{if positive?(n) then (ℓ₁ Lvl.⊔ ℓ₂) else ℓ₂}
    Preserving(𝟎)       (f)(g₁)(g₂) = (f(g₁) ≡ g₂)
    Preserving(𝐒(𝟎))    (f)(g₁)(g₂) = (∀{x} → f(g₁(x)) ≡ g₂(f(x)))
    Preserving(𝐒(𝐒(n))) (f)(g₁)(g₂) = (∀{x} → Preserving(𝐒(n)) (f) (g₁(x)) (g₂(f(x))))

    Preserving₀ = Preserving(0)
    Preserving₁ = Preserving(1)
    Preserving₂ = Preserving(2)
    Preserving₃ = Preserving(3)
    Preserving₄ = Preserving(4)
    Preserving₅ = Preserving(5)
    Preserving₆ = Preserving(6)
    Preserving₇ = Preserving(7)
    Preserving₈ = Preserving(8)
    Preserving₉ = Preserving(9)

  module _ {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ where
    -- Definition of the relation between a function and an operation that says:
    -- The function preserves the operation.
    -- This is a special case of the (_preserves_)-relation that has the same operator inside and outside.
    -- Special cases:
    --   Additive function (Operator is a conventional _+_)
    --   Multiplicative function (Operator is a conventional _*_)
    _preserves_ : (T → T) → (T → T → T) → Stmt{ℓ}
    f preserves (_▫_) = Preserving(2) f (_▫_)(_▫_) -- (∀{x y} → (f(x ▫ y) ≡ f(x) ▫ f(y)))

module _ {X : Type{ℓ₁}} {Y : Type{ℓ₂}} ⦃ _ : Equiv(Y) ⦄ where
  module _ (n : ℕ) (f : X → Y) (g₁ : (X →̂ X)(n)) (g₂ : (Y →̂ Y)(n)) where
    record Preserving : Stmt{if positive?(n) then (ℓ₁ Lvl.⊔ ℓ₂) else ℓ₂} where -- TODO: How to prove for levels that an if-expression is less if both are less?
      constructor intro
      field proof : Names.Preserving(n) (f)(g₁)(g₂)
    preserving = inst-fn Preserving.proof

  Preserving₀ = Preserving(0)
  Preserving₁ = Preserving(1)
  Preserving₂ = Preserving(2)
  Preserving₃ = Preserving(3)
  Preserving₄ = Preserving(4)
  Preserving₅ = Preserving(5)
  Preserving₆ = Preserving(6)
  Preserving₇ = Preserving(7)
  Preserving₈ = Preserving(8)
  Preserving₉ = Preserving(9)

  preserving₀ = preserving(0)
  preserving₁ = preserving(1)
  preserving₂ = preserving(2)
  preserving₃ = preserving(3)
  preserving₄ = preserving(4)
  preserving₅ = preserving(5)
  preserving₆ = preserving(6)
  preserving₇ = preserving(7)
  preserving₈ = preserving(8)
  preserving₉ = preserving(9)

module _ {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (n : ℕ) (f : T → T) (_▫_ : T → T → T) where
  _preserves_ = Preserving(2) (f)(_▫_)(_▫_)
