module Function.Domains.Functions where

import      Lvl
open import Function.Domains
open import Function.Domains.Id
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type
open import Type.Dependent

private variable ℓₒ₁ ℓₒ₂ ℓₑ₁ ℓₑ₂ : Lvl.Level

module _ {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} where
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

    value-proof : ⦃ equiv-Y : Equiv{ℓₑ₂}(Y) ⦄ → ∀{x} → (value(intro (f(x)) (intro{f = f} x)) ≡ f(x))
    value-proof = reflexivity(_≡_)

    arg-proof : ⦃ equiv-X : Equiv{ℓₑ₁}(X) ⦄ → ∀{x} → (arg(intro (f(x)) (intro{f = f} x)) ≡ x)
    arg-proof = reflexivity(_≡_)

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
