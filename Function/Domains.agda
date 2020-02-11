module Function.Domains where

import      Lvl
open import Functional hiding (apply)
import      Lang.Irrelevance
open import Logic.Predicate
open import Relator.Equals
open import Relator.Equals.Proofs
open import Type
open import Type.Dependent

module _ {ℓₒ₁ ℓₒ₂ : Lvl.Level} {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} where
  -- The partial domain of a function
  -- Note: This is the same as the domain because all functions are total (or at least supposed to be)
  ⊷ : (X → Y) → Type{ℓₒ₁}
  ⊷ _ = X

  data Image-in (f : X → Y) : Y → Type{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    intro : (x : X) → Image-in(f) (f(x))

  -- The image/range of a function.
  -- Represents the "set" of values of a function.
  -- Note: An element of Y and a proof that this element is the value of the function f is included so that (⊶ f) does not become injective when f is not.
  -- Note: A construction of this implies that X is non-empty.
  ⊶ : (X → Y) → Type{ℓₒ₁ Lvl.⊔ ℓₒ₂}
  ⊶ = Σ(Y) ∘ Image-in

  module ⊶ where
    private variable f : X → Y

    -- The function which shrinks the given function's codomain to its image.
    shrink : (f : X → Y) → (X → (⊶ f))
    shrink f(x) = intro (f(x)) (intro x)

    -- Applies an argument of type X to a function of type ((⊶ f) → Y) according to the bijection of {X,(⊶ f)} by f.
    apply : X → ((⊶ f) → Y) → Y
    apply{f} x imgfn = imgfn (shrink f(x))

    fn : (⊶ f) → (X → Y)
    fn{f} _ = f

    arg : (⊶ f) → X
    arg (intro _ (intro x)) = x

    -- Could be interpreted as an identity function with an enlarged codomain.
    -- The value of (⊶ f) interpreted as contained in the "set" Y.
    value : (⊶ f) → Y
    value (intro y _) = y

    -- TODO: Why is this useful to prove?
    -- TODO: https://www.iis.sinica.edu.tw/~scm/2009/no-inverses-for-injective-but-non-surjective-functions/
    value-proof : ∀{x} → (value(intro (f(x)) (intro{f} x)) ≡ f(x))
    value-proof = [≡]-intro

    arg-proof : ∀{x} → (arg(intro (f(x)) (intro{f} x)) ≡ x)
    arg-proof = [≡]-intro

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

  -- Represents the "set" of objects pointing to the value y of the function f.
  -- (Unapply f(y)) is also called "the fiber of the element y under the map f".
  -- Unapply(f) is similar to the inverse image or the preimage of f when their argument is a singleton set.
  record Unapply (f : X → Y) (y : Y) : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    constructor intro
    field
      obj : X
      ⦃ proof ⦄ : (f(obj) ≡ y)

  -- TODO: Temporary name. Use this instead and Unapply is Σ Unapply2
  record Unapply2 (f : X → Y) (y : Y) (x : X) : Type{ℓₒ₂} where
    constructor intro
    field ⦃ proof ⦄ : (f(x) ≡ y)
