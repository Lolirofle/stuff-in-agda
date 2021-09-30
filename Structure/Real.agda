open import Logic
open import Logic.Classical

module Structure.Real ⦃ classical : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ where

open import Functional
import      Lvl
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural using (ℕ)
import      Numeral.Natural.Relation.Order as ℕ
open import Structure.Function.Ordering
open import Structure.OrderedField
import      Structure.OrderedField.AbsoluteValue
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Function
open import Type

private variable ℓ ℓₗₑ ℓₑ : Lvl.Level
private variable R : Type{ℓ}

-- One way of defining the axioms of ℝ in classical logic.
-- The axioms are the following:
-- • An ordered field.
-- • Monotone convergence.
record RealTheory ⦃ equiv-R : Equiv{ℓₑ}(R) ⦄ (_+_ _⋅_ : R → R → R) (_≤_ : R → R → Stmt{ℓₗₑ}) : Type{Lvl.of(R) Lvl.⊔ ℓₗₑ Lvl.⊔ ℓₑ} where
  field
    ⦃ orderedField ⦄ : OrderedField(_+_)(_⋅_)(_≤_)

  open OrderedField(orderedField) public
  open Structure.OrderedField.AbsoluteValue(_+_)(_⋅_)(_≤_)

  _≡ₗᵢₘ_ : (ℕ → R) → (ℕ → R) → Stmt
  _≡ₗᵢₘ_ f g = ∃{Obj = R → ℕ}(N ↦ ∀{ε} → (ε > 𝟎) → ∀{n} → (n ℕ.> N(ε)) → (‖ f(n) − g(n) ‖ < ε))

  -- Completeness.
  -- TODO: Is this equivalent to the usual formalization using Dedekind completeness or Cauchy sequences?
  field
    supFn : (f : ℕ → R) → ⦃ Increasing(ℕ._≤_)(_≤_)(f) ⦄ → ⦃ UpperBounded(ℕ._≤_)(_≤_)(f) ⦄ → R
    supFn-convergence : ∀{f} → ⦃ inc : Increasing(ℕ._≤_)(_≤_)(f) ⦄ → ⦃ bound : UpperBounded(ℕ._≤_)(_≤_)(f) ⦄
                      → (f ≡ₗᵢₘ const(supFn(f)))
    supFn-extensionality : ∀{f} ⦃ inc-f : Increasing(ℕ._≤_)(_≤_)(f) ⦄ ⦃ bound-f : UpperBounded(ℕ._≤_)(_≤_)(f) ⦄
                         → ∀{g} ⦃ inc-g : Increasing(ℕ._≤_)(_≤_)(g) ⦄ ⦃ bound-g : UpperBounded(ℕ._≤_)(_≤_)(g) ⦄
                         → (supFn(f) ≡ supFn(g)) ↔ (f ≡ₗᵢₘ g)

  {-
  infFn : (f : ℕ → R) → ⦃ Decreasing(ℕ._≤_)(_≤_)(f) ⦄ → ⦃ LowerBounded(ℕ._≤_)(_≤_)(f) ⦄ → R
  infFn(f) = − supFn((−_) ∘ f) ⦃ {!!} ⦄ ⦃ {!!} ⦄
  -}
