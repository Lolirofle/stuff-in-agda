module Function.DomainRaise where

open import Data
open import Data.Boolean
import      Functional as Fn
import      Lvl
-- open import Numeral.Finite
-- open import Numeral.Finite.Bound
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
-- open import Numeral.Natural.Oper.Comparisons.Proofs
-- open import Numeral.Natural.Relation.Order
-- open import Numeral.Natural.Relation.Order.Proofs
open import Syntax.Number
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T X Y Z : Type{ℓ}
private variable n : ℕ

-- Repeated function type like an n-ary operator.
-- Examples:
--   (a →̂ b)(0) = (b)
--   (a →̂ b)(1) = (a → b)
--   (a →̂ b)(2) = (a → a → b)
--   (a →̂ b)(3) = (a → a → a → b)
--   (a →̂ b)(4) = (a → a → a → a → b)
_→̂_ : Type{ℓ₁} → Type{ℓ₂} → (n : ℕ) → Type{if positive?(n) then (ℓ₁ Lvl.⊔ ℓ₂) else ℓ₂}
(A →̂ B)(𝟎)       = B
(A →̂ B)(𝐒(𝟎))    = A → B
(A →̂ B)(𝐒(𝐒(n))) = A → (A →̂ B)(𝐒(n))

-- Applies the same argument on all arguments.
-- Examples:
--   f : (a →̂ b)(5)
--   applyRepeated{0} f(x) = f
--   applyRepeated{1} f(x) = f(x)
--   applyRepeated{2} f(x) = f(x)(x)
--   applyRepeated{3} f(x) = f(x)(x)(x)
--   applyRepeated{2}(applyRepeated{3} f(x)) (y) = f(x)(x)(y)(y)(y)
applyRepeated : let _ = n in (X →̂ Y)(n) → (X → Y)
applyRepeated{𝟎}       f(x) = f
applyRepeated{𝐒(𝟎)}    f(x) = f(x)
applyRepeated{𝐒(𝐒(n))} f(x) = applyRepeated{𝐒(n)} (f(x)) (x)

{-
  -- Applies arguments from a function.
  -- Almost (not really) like a composition operation.
  -- Examples:
  --   f : (a →̂ b)(3)
  --   applyFn f g = f (g(2)) (g(1)) (g(0))
  applyFn : ∀{n}{T₁}{T₂} → (T₁ →̂ T₂)(n) → (𝕟(n) → T₁) → T₂
  applyFn{𝟎}    f g = f
  applyFn{𝐒(n)} f g = applyFn{n} (f(g(ℕ-to-𝕟 (n) {𝐒(n)} ⦃ [<?]-𝐒 {n} ⦄))) (g ∘ (bound-𝐒{n}))

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
-}

-- Function composition on a multi-argument function (Like PrimitiveRecursion.Composition).
-- Examples:
--   (f ∘₄ g) x₁ x₂ x₃ x₄
--   = (f ∘₃ g x₁) x₂ x₃ x₄
--   = (f ∘₂ g x₁ x₂) x₃ x₄
--   = (f ∘₁ g x₁ x₂ x₃) x₄
--   = (f ∘ g x₁ x₂ x₃) x₄
--   = f(g x₁ x₂ x₃ x₄)
_∘_ : let _ = n ; _ = X ; _ = Y ; _ = Z in (Y → Z) → (X →̂ Y)(n) → (X →̂ Z)(n)
_∘_ {𝟎}       = Fn.id
_∘_ {𝐒(𝟎)}    = Fn._∘_
_∘_ {𝐒(𝐒(n))} = Fn._∘_ Fn.∘ (_∘_) -- (f ∘ₙ₊₂ g)(x) = f ∘ₙ₊₁ g(x)

_∘[_]_ : let _ = X ; _ = Y ; _ = Z in (Y → Z) → (n : ℕ) → (X →̂ Y)(n) → (X →̂ Z)(n)
f ∘[ n ] g = _∘_ {n = n} f g

_∘₀_ = _∘_ {0}
_∘₁_ = _∘_ {1}
_∘₂_ = _∘_ {2}
_∘₃_ = _∘_ {3}
_∘₄_ = _∘_ {4}
_∘₅_ = _∘_ {5}
_∘₆_ = _∘_ {6}
_∘₇_ = _∘_ {7}
_∘₈_ = _∘_ {8}
_∘₉_ = _∘_ {9}

-- TODO: Flip the arguments and make n explicit
-- Single function composition on every argument.
-- (f on g)(y₁)(y₂).. = g (f(y₁)) (f(y₂)) ..
-- Examples:
--   _on_ {3} f g (y₂) (y₁) (y₀)
--   = _on_ {2} f (g (f(y₂))) (y₁) (y₀)
--   = _on_ {1} f (g (f(y₂)) (f(y₁))) (y₀)
--   = _on_ {0} f (g (f(y₂)) (f(y₁)) (f(y₀)))
--   = g (f(y₂)) (f(y₁)) (f(y₀))
_on_ : let _ = n ; _ = X ; _ = Y ; _ = Z in (Y →̂ Z)(n) → (X → Y) → (X →̂ Z)(n)
_on_ {n = 𝟎}               = Fn.const
_on_ {n = 𝐒(𝟎)}            = Fn._∘_
_on_ {n = 𝐒(𝐒(n))} f g(yₙ) = _on_ {n = 𝐒(n)} (f(g(yₙ))) g

-- applyOnFn : ∀{n}{X}{Y} → (Y →̂ Y)(n) → ((X → Y) →̂ (X → Y))(n)
-- applyOnFn

-- Constructs a left-associated n-ary operator from a binary operator.
-- Example:
--   naryₗ{3} (_▫_) x₁ x₂ x₃ x₄ x₅
--   = ((naryₗ{2} (_▫_)) Fn.∘ (x₁ ▫_)) x₂ x₃ x₄
--   = (naryₗ{2} (_▫_) (x₁ ▫ x₂)) x₃ x₄ x₅
--   = ((naryₗ{1} (_▫_)) Fn.∘ ((x₁ ▫ x₂) ▫_)) x₃ x₄ x₅
--   = (naryₗ{1} (_▫_) ((x₁ ▫ x₂) ▫ x₃)) x₄ x₅
--   = ((naryₗ{0} (_▫_)) Fn.∘ (((x₁ ▫ x₂) ▫ x₃) ▫_)) x₃ x₄ x₅
--   = (naryₗ{0} (_▫_) (((x₁ ▫ x₂) ▫ x₃) ▫ x₄)) x₅
--   = ((_▫_) (((x₁ ▫ x₂) ▫ x₃) ▫ x₄)) x₅
--   = ((((x₁ ▫ x₂) ▫ x₃) ▫ x₄) ▫_) x₅
--   = (((x₁ ▫ x₂) ▫ x₃) ▫ x₄) x₅
naryₗ : (n : ℕ) → (X → X → X) → (X →̂ X)(𝐒(𝐒(n)))
naryₗ(𝟎)    (_▫_)   = (_▫_)
naryₗ(𝐒(n)) (_▫_) x = (naryₗ(n) (_▫_)) Fn.∘ (x ▫_)

-- Constructs a right-associated n-ary operator from a binary operator.
-- Example:
--   naryᵣ{3} (_▫_) x₁ x₂ x₃ x₄ x₅
--   = ((x₁ ▫_) ∘[ 4 ] (naryᵣ{2} (_▫_))) x₂ x₃ x₄ x₅
--   = x₁ ▫ (naryᵣ{2} (_▫_) x₂ x₃ x₄ x₅)
--   = x₁ ▫ (((x₂ ▫_) ∘[ 3 ] (naryᵣ{1} (_▫_))) x₃ x₄ x₅)
--   = x₁ ▫ (x₂ ▫ (naryᵣ{1} (_▫_) x₃ x₄ x₅))
--   = x₁ ▫ (x₂ ▫ (((x₃ ▫_) ∘[ 2 ] (naryᵣ{0} (_▫_))) x₄ x₅))
--   = x₁ ▫ (x₂ ▫ (x₃ ▫ (naryᵣ{0} (_▫_) x₄ x₅)))
--   = x₁ ▫ (x₂ ▫ (x₃ ▫ ((_▫_) x₄ x₅)))
--   = x₁ ▫ (x₂ ▫ (x₃ ▫ (x₄ ▫ x₅)))
naryᵣ : (n : ℕ) → (X → X → X) → (X →̂ X)(𝐒(𝐒(n)))
naryᵣ(𝟎)    (_▫_)   = (_▫_)
naryᵣ(𝐒(n)) (_▫_) x = (x ▫_) ∘[ 𝐒(𝐒(n)) ] (naryᵣ(n) (_▫_))
