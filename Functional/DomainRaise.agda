module Functional.DomainRaise where

open import Functional
import      Lvl
open import Numeral.FiniteStrict
open import Numeral.FiniteStrict.Bound
open import Numeral.Natural
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Syntax.Number
open import Type

module _ {ℓ₁ ℓ₂} where
  -- Repeated function type like an n-ary operator.
  -- Examples:
  --   (a →̂ b)(0) = (b)
  --   (a →̂ b)(1) = (a → b)
  --   (a →̂ b)(2) = (a → a → b)
  --   (a →̂ b)(3) = (a → a → a → b)
  --   (a →̂ b)(4) = (a → a → a → a → b)
  _→̂_ : Type{ℓ₁} → Type{ℓ₁ Lvl.⊔ ℓ₂} → ℕ → Type{ℓ₁ Lvl.⊔ ℓ₂}
  (A →̂ B)(𝟎)    = B
  (A →̂ B)(𝐒(n)) = A → (A →̂ B)(n)

  -- Applies the same argument on all arguments.
  -- Examples:
  --   f : (a →̂ b)(5)
  --   applyRepeated{0} f(x) = f
  --   applyRepeated{1} f(x) = f(x)
  --   applyRepeated{2} f(x) = f(x)(x)
  --   applyRepeated{3} f(x) = f(x)(x)(x)
  --   applyRepeated{2}(applyRepeated{3} f(x)) (y) = f(x)(x)(y)(y)(y)
  applyRepeated : ∀{n}{T₁}{T₂} → (T₁ →̂ T₂)(n) → T₁ → T₂
  applyRepeated{𝟎}    f(x) = f
  applyRepeated{𝐒(n)} f(x) = applyRepeated{n} (f(x)) (x)

  -- Applies arguments from a function.
  -- Almost (not really) like a composition operation.
  -- Examples:
  --   f : (a →̂ b)(3)
  --   applyFn f g = f (g(2)) (g(1)) (g(0))
  applyFn : ∀{n}{T₁}{T₂} → (T₁ →̂ T₂)(n) → (𝕟(n) → T₁) → T₂
  applyFn{𝟎}    f g = f
  applyFn{𝐒(n)} f g = applyFn{n} (f(g([ℕ]-to-[𝕟] (n) {n} ⦃ lteq2-𝐒 {ℓ₁ Lvl.⊔ ℓ₂} {n} ⦄))) (g ∘ (bound-𝐒{ℓ₁ Lvl.⊔ ℓ₂}{n}))

  -- TODO: Examples:
  --   swapReverse {3} f (y₂) (y₁) (y₀)
  --   = swapReverse {2} (f(y₂)) (y₁) (y₀)
  --   = swapReverse {1} (f(y₂) (y₁)) (y₀)
  --   = swapReverse {0} (f(y₂) (y₁) (y₀))
  --   = f(y₂) (y₁) (y₀)
  -- swapReverse : ∀{n}{T₁}{T₂} → (T₁ →̂ T₂)(n) → (T₁ →̂ T₂)(n)
  -- swapReverse {𝟎}    y₀   = y₀
  -- swapReverse {𝐒(n)} f(yₙ) = (swapReverse {n} f) ∘ (f(yₙ))

  -- directOp : ∀{n}{X}{Y} → ((X → Y) →̂ ((X ^ n) → (Y ^ n)))(n)

module _ {ℓ₁ ℓ₂ ℓ₃ : Lvl.Level} where
  private _→̂₁₂_ = _→̂_ {ℓ₁}{ℓ₂}
  private _→̂₁₃_ = _→̂_ {ℓ₁}{ℓ₃}

  -- Function composition on a multi-argument function (Like PrimitiveRecursion.Composition).
  -- Examples:
  --   (f ∘₃ g)(x₂)(x₁)(x₀)
  --   (f ∘₂ (g(x₂)))(x₁)(x₀)
  --   (f ∘₁ (g(x₂)(x₁)))(x₁)(x₀)
  --   (f ∘₀ (g(x₂)(x₁)))(x₀)
  --   f(g(x₂)(x₁)(x₀))
  _[∘]_ : ∀{n}{X}{Y}{Z} → (Y → Z) → (X →̂₁₂ Y)(n) → (X →̂₁₃ Z)(n)
  _[∘]_ {𝟎}    f = f
  _[∘]_ {𝐒(n)} f g(xₙ) = _[∘]_ {n} f (g(xₙ))

module _ {ℓ₁ ℓ₂ ℓ₃ : Lvl.Level} where
  private _→̂₁₃_ = _→̂_ {ℓ₁}{ℓ₂ Lvl.⊔ ℓ₃}
  private _→̂₂₃_ = _→̂_ {ℓ₂}{ℓ₁ Lvl.⊔ ℓ₃}

  -- Single function composition on every argument.
  -- (f on g)(y₁)(y₂).. = g (f(y₁)) (f(y₂)) ..
  -- Examples:
  --   _on_ {3} f g (y₂) (y₁) (y₀)
  --   = _on_ {2} f (g (f(y₂))) (y₁) (y₀)
  --   = _on_ {1} f (g (f(y₂)) (f(y₁))) (y₀)
  --   = _on_ {0} f (g (f(y₂)) (f(y₁)) (f(y₀)))
  --   = g (f(y₂)) (f(y₁)) (f(y₀))
  _on_ : ∀{n}{X}{Y}{Z} → (X → Y) → (Y →̂₂₃ Z)(n) → (X →̂₁₃ Z)(n)
  _on_ {𝟎}    _ g  = g
  _on_ {𝐒(n)} f g(yₙ) = _on_ {n} f (g(f(yₙ)))

  -- applyOnFn : ∀{n}{X}{Y} → (Y →̂ Y)(n) → ((X → Y) →̂ (X → Y))(n)
  -- applyOnFn

{-
apply-repeat₂ : ∀{ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → T₁ → (T₁ → T₁ → T₂) → T₂
apply-repeat₂(x) = (apply(x)) ∘ (apply(x))
apply-repeat₂(x)(f) = f(x)(x)
-}

module _ {ℓ} where
  private _→̂₁_ = _→̂_ {ℓ}{ℓ}

  -- Examples: (TODO: This example is _slightly_ incorrect: Where is the arguments coming from?)
  --   (nary{3} (_▫_)) ∘ (_▫ x₄)
  --   ((nary{2} (_▫_)) ∘ (_▫ x₃)) ∘ (_▫ x₄)
  --   (((nary{1} (_▫_)) ∘ (_▫ x₂)) ∘ (_▫ x₃)) ∘ (_▫ x₄)
  --   ((((nary{0} (_▫_)) ∘ (_▫ x₁)) ∘ (_▫ x₂)) ∘ (_▫ x₃)) ∘ (_▫ x₄)
  --   ((((_▫ x₀) ∘ (_▫ x₁)) ∘ (_▫ x₂)) ∘ (_▫ x₃)) ∘ (_▫ x₄)
  --   (_▫ x₀) ∘ (_▫ x₁) ∘ (_▫ x₂) ∘ (_▫ x₃) ∘ (_▫ x₄)
  --   ((((_▫ x₄) ▫ x₃) ▫ x₂) ▫ x₁) ▫ x₀
  naryₗ : ∀{n}{X} → (X → X → X) → (X →̂₁ X)(𝐒(𝐒(n)))
  naryₗ{𝟎}    (_▫_) (x₀)   = (x₀ ▫_)
  naryₗ{𝐒(n)} (_▫_) (xₙ₊₁) = (naryₗ{n} (_▫_)) ∘ (xₙ₊₁ ▫_)

  -- Examples: (TODO: This example is incorrect)
  --   (naryᵣ{3} (_▫_)) (x₃) (x₂) (x₁) (x₀)
  --   ((x₃ ▫_) ∘₄ (naryᵣ{2} (_▫_))) (x₂) (x₁) (x₀)
  --   ((x₃ ▫_) ∘₄ ((x₂ ▫_) ∘₃ (naryᵣ{1} (_▫_)))) (x₁) (x₀)
  --   ((x₃ ▫_) ∘₄ ((x₂ ▫_) ∘₃ ((x₁ ▫_) ∘₂ (naryᵣ{0} (_▫_)))) (x₀)
  --   ((x₃ ▫_) ∘₄ ((x₂ ▫_) ∘₃ ((x₁ ▫_) ∘₂ (x₀ ▫_)))
  --   ...
  --   x₅ ▫ (x₄ ▫ (x₃ ▫ (x₂ ▫ (x₁ ▫ x₀))))
  naryᵣ : ∀{n}{X} → (X → X → X) → (X →̂₁ X)(𝐒(𝐒(n)))
  naryᵣ{𝟎}    (_▫_) (x₀)   = (x₀ ▫_)
  naryᵣ{𝐒(n)} (_▫_) (xₙ₊₁) = (xₙ₊₁ ▫_) ∘ₙ₊₂ (naryᵣ{n} (_▫_)) where
    _∘ₙ₊₂_ = _[∘]_ {ℓ}{ℓ}{ℓ}{𝐒(𝐒(n))}
