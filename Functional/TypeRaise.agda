module Functional.TypeRaise where

open import Data
open import Functional
import      Lvl
open import Numeral.FiniteStrict
open        Numeral.FiniteStrict.Theorems
open import Numeral.Natural
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Properties
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
  --   applyFn f g = f (g(0)) (g(1)) (g(2))
  applyFn : ∀{n}{T₁}{T₂} → (T₁ →̂ T₂)(n) → (𝕟(n) → T₁) → T₂
  applyFn{𝟎}    f g = f
  applyFn{𝐒(n)} f g = applyFn{n} (f(g([ℕ]-to-[𝕟] (n) {n} ⦃ lteq2-𝐒 {ℓ₁ Lvl.⊔ ℓ₂} {n} ⦄))) (g ∘ (upscale-𝐒{ℓ₁ Lvl.⊔ ℓ₂}{n}))
