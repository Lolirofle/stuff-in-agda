module Functional.Domains where

import      Lvl
open import Functional
import      Lang.Irrelevance
open import Logic.Predicate
open import Relator.Equals
open import Relator.Equals.Proofs
open import Type


module _ {ℓₒ₁ ℓₒ₂ : Lvl.Level} {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} where
  -- The partial domain of a function
  -- Note: This is the same as the domain because all functions are total (or at least supposed to be)
  ⊷_ : (X → Y) → Type{ℓₒ₁}
  ⊷_ _ = X

  -- The image/range of a function.
  -- Represents the "set" of values of a function.
  -- Note: An element of Y and a proof that this element is the value of the function f is included so that (⊶ f) does not become injective when f is not.
  -- Note: A construction of this implies that X is non-empty.
  record ⊶_ (f : X → Y) : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    constructor intro
    field
      obj : Y
      ⦃ proof ⦄ : ∃(x ↦ f(x) ≡ obj)

  -- instance
  --   [⊶]-equality : ∀{f : X → Y}{y₁ y₂ : (⊶ f)} → ⦃ _ : (⊶_.obj y₁ ≡ ⊶_.obj y₂) ⦄ → (y₁ ≡ y₂)
  --   [⊶]-equality ⦃ [≡]-intro ⦄ = [≡]-intro

    -- [⊶]-equalityₗ : ∀{f : X → Y}{y₁ y₂ : Y} → ⦃ _ : (intro y₁ ≡ intro y₂)⦄ → (⊶ y₁ ≡ ⊶_.obj y₂ )
    -- [⊶]-equalityₗ ⦃ [≡]-intro ⦄ = [≡]-intro

  -- Applies an argument of type X to a function of type ((⊶ f) → Y) according to the bijection of {X,(⊶ f)} by f.
  [⊶]-apply : ∀{f : X → Y} → X → ((⊶ f) → Y) → Y
  [⊶]-apply{f} (x) (fimg) = fimg(intro (f(x)) ⦃ [∃]-intro (x) ⦃ [≡]-intro ⦄ ⦄)

  [⊶]-arg : ∀{f : X → Y} → (⊶ f) → X
  [⊶]-arg{f} (intro _ ⦃ proof ⦄) = [∃]-witness (proof)

  -- Could be interpreted as an identity function with an enlarged codomain.
  -- The value of (⊶ f) interpreted as contained in the "set" Y.
  [⊶]-value : ∀{f : X → Y} → (⊶ f) → Y
  [⊶]-value{f} (intro y) = y

  -- TODO: Why is this useful to prove?
  -- TODO: https://www.iis.sinica.edu.tw/~scm/2009/no-inverses-for-injective-but-non-surjective-functions/
  [⊶]-value-identity : (f : X → Y) → ∀{x} → (f(x) ≡ [⊶]-apply(x) ([⊶]-value{f}))
  [⊶]-value-identity(f) = [≡]-intro

  -- The function which shrinks the given function's codomain to its image.
  [⊶]-fn : (f : X → Y) → (X → (⊶ f))
  [⊶]-fn f(x) = intro(f(x)) ⦃ [∃]-intro(x) ⦄

  -- TODO: Problem with levels
  -- TODO: [⊶]-function-surjective : ∀{f : X → Y} → Surjective([⊶]-function(f))
  -- .[⊶]-function-surjective : ∀{f : X → Y}{y : (⊶ f)} → ∃(x ↦ [⊶]-arg(([⊶]-fn f)(x)) ≡ [⊶]-arg(y))
  -- [⊶]-function-surjective {f} {intro(y-value) ⦃ [∃]-intro (x) ⦃ proof ⦄ ⦄} =
  --   Lang.Irrelevance.axiom(
  --     ([∃]-intro (x)
  --       ⦃ [≡]-with-specific {_}{_} {_}{_} {f(x)} {y-value}
  --         (expr ↦ \ ⦃ [≡]-intro ⦄ → \ ⦃ [≡]-intro ⦄ →
  --           (intro
  --             (expr)
  --             ⦃ [∃]-intro (x) ⦃ [≡]-intro :of: (f(x) ≡ y-value) ⦄ ⦄
  --           )
  --         )
  --         (proof :of: (f(x) ≡ y-value))
  --       ⦄
  --     )
  --   )
    -- ∃(x: X). f(x) ≡ obj(y) //proof:
    -- Take x: X
    --   f(x) ≡ obj(y)
    --   ⇒ intro(f(x)) ⦃ [∃]-intro(x) ⦃ e ⦄ ⦄ ≡ intro(obj(y)) ⦃ [∃]-intro(x) ⦃ e ⦄ ⦄

  -- [⊶]-function-injective : ∀{X}{Y}{f : X → Y} → Injective(f) → Injective([⊶]-function(f))
  -- [⊶]-function-injective{_}{_}{f} {x₁}{x₂} [≡]-intro = [≡]-intro

  {-
  -- Image-in(f)(y) means whether the image of `f` contains `y`.
  Image-in : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → Y → Stmt{ℓ₂ Lvl.⊔ ℓ₃}
  Image-in f y = ∃(x ↦ (f(x) ≡ y))
  -}

  -- Represents the "set" of objects pointing to the value y of the function f.
  -- (Unapply f(y)) is also called "the fiber of the element y under the map f".
  -- Unapply(f) is similar to the inverse image or the preimage of f when their argument is a singleton set.
  record Unapply (f : X → Y) (y : Y) : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    constructor intro
    field
      obj : X
      ⦃ proof ⦄ : (f(obj) ≡ y)
