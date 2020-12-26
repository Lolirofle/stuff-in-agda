module Function.Inverseₗ where

import      Lvl
import      Data.Either as Either
open import Data.Either.Proofs
open import Lang.Inspect
open import Logic
open import Logic.Classical
open import Logic.Propositional
open import Logic.Predicate
open import Functional
open import Function.Domains
open import Function.Names using (_⊜_)
import      Function.Equals as FunctionEq
open import Function.Proofs
open import Structure.Setoid
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level

module _
  {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  where

  -- An inverse function of an injective function f.
  -- This is definable when the proposition "y is a value in f" for any y is decidable.
  -- Because f is not guaranteed to be surjective, all non-values in the codomain B use the fallback function to make the inverse a total (B → A).
  invₗ-construction : (B → A) → (f : A → B) → ⦃ _ : ∀{y} → Classical(∃(Fiber f(y))) ⦄ → (B → A)
  invₗ-construction(fallback) f(y) = Either.map1 [∃]-witness (const(fallback(y))) (excluded-middle(∃(Fiber f(y))))

  module _ {fallback : B → A} {f : A → B} ⦃ classical-unapply : ∀{y} → Classical(∃(Fiber f(y))) ⦄ where
    module _ ⦃ inj : Injective(f) ⦄ ⦃ func-fallback : Function(fallback) ⦄ where
      invₗ-construction-inverseₗ : Inverseₗ(f)(invₗ-construction(fallback) f)
      Inverseₗ.proof invₗ-construction-inverseₗ{x} with excluded-middle(∃(Fiber f(f(x)))) | inspect(invₗ-construction(fallback) f) (f(x))
      ... | [∨]-introₗ ([∃]-intro _ ⦃ p ⦄) | _ = injective(f) p
      ... | [∨]-introᵣ p | _ = [⊥]-elim(p ([∃]-intro x ⦃ reflexivity(_≡_) ⦄))

      invₗ-construction-function : Function(invₗ-construction(fallback) f)
      Function.congruence invₗ-construction-function {y₁} {y₂} y₁y₂ with Classical.excluded-middle (classical-unapply {y₁}) | Classical.excluded-middle (classical-unapply {y₂})
      ... | [∨]-introₗ ([∃]-intro x₁ ⦃ fxy1 ⦄) | [∨]-introₗ ([∃]-intro x₂ ⦃ fxy2 ⦄) =
        injective(f) $
          f(x₁)                        🝖-[ fxy1 ]
          y₁                           🝖-[ y₁y₂ ]
          y₂                           🝖-[ fxy2 ]-sym
          f(x₂)                        🝖-end
      ... | [∨]-introₗ ([∃]-intro x₁ ⦃ fxy1 ⦄) | [∨]-introᵣ nfxy2                   = [⊥]-elim (nfxy2 ([∃]-intro x₁ ⦃ fxy1 🝖 y₁y₂ ⦄))
      ... | [∨]-introᵣ nfxy1                   | [∨]-introₗ ([∃]-intro x₂ ⦃ fxy2 ⦄) = [⊥]-elim (nfxy1 ([∃]-intro x₂ ⦃ fxy2 🝖 symmetry(_≡_) y₁y₂ ⦄))
      ... | [∨]-introᵣ nfxy1                   | [∨]-introᵣ nfxy2                   = congruence₁(fallback) y₁y₂

      injective-to-invertibleₗ-construction : Invertibleₗ(f)
      ∃.witness injective-to-invertibleₗ-construction = invₗ-construction(fallback) f
      ∃.proof   injective-to-invertibleₗ-construction = [∧]-intro invₗ-construction-function invₗ-construction-inverseₗ

module _
  {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  where

  -- An inverse function of an invertible function f.
  invₗ : (f : A → B) → ⦃ inverₗ : Invertibleₗ(f) ⦄ → (B → A)
  invₗ _ ⦃ inverₗ ⦄ = [∃]-witness inverₗ

  module _ {f : A → B} where
    invₗ-inverseₗ : ⦃ inverₗ : Invertibleₗ(f) ⦄ → Inverseₗ(f)(invₗ f)
    invₗ-inverseₗ ⦃ inverₗ ⦄ = [∧]-elimᵣ([∃]-proof inverₗ)

  module _ {f : A → B} ⦃ classical-unapply : ∀{y} → Classical(∃(Fiber f(y))) ⦄ where
    -- All left inverse functions are functionally equal to one of `invₗ-construction`.
    inverseₗ-is-construction : ⦃ inverₗ : Invertibleₗ(f) ⦄ ⦃ invₗ-func : Function(invₗ f) ⦄ → (invₗ f ⊜ invₗ-construction(invₗ f) f)
    inverseₗ-is-construction {y} with Classical.excluded-middle (classical-unapply {y})
    ... | [∨]-introₗ ([∃]-intro x ⦃ p ⦄) =
      invₗ f(y)    🝖-[ congruence₁(invₗ f) p ]-sym
      invₗ f(f(x)) 🝖-[ inverseₗ _ _ ⦃ invₗ-inverseₗ ⦄ ]
      x            🝖-end
    ... | [∨]-introᵣ nfxy = reflexivity(_≡_)
