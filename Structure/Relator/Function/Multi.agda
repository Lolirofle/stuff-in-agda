module Structure.Relator.Function.Multi where

open import Data.Tuple.RaiseTypeᵣ
import      Data.Tuple.RaiseTypeᵣ.Functions as RaiseType
open import Function.Multi
import      Function.Multi.Functions as Multi
import      Lvl
import      Lvl.MultiFunctions as Lvl
open import Logic
open import Logic.Predicate
open import Logic.Predicate.Multi
open import Functional
open import Numeral.Natural
import      Structure.Function.Multi as Multi
open import Structure.Setoid.WithLvl
open import Type

private variable ℓ ℓₑ : Lvl.Level

module _ (n : ℕ) {ℓ𝓈}{ℓ₁ ℓ₂} {Xs : Types{n}(ℓ𝓈)}{Y : Type{ℓ₁}} where
  module Names where
    -- A relator is total when every LHS have at least one RHS in which the relation holds.
    Total : (Xs ⇉ (Y → Stmt{ℓ₂})) → Stmt
    Total(φ) = ∀₊(n)(Multi.compose(n) ∃ φ)

    module _ ⦃ equiv-Y : Equiv{ℓₑ}(Y) ⦄ where
      -- A relator is a function when every LHS have at least one RHS in which the relation holds.
      Function : ∀{ℓ𝓈ₑ} → (RaiseType.mapWithLvls(\X ℓₑ → Equiv{ℓₑ}(X)) Xs ℓ𝓈ₑ) ⇉ᵢₙₛₜ ((Xs ⇉ (Y → Type{ℓ₂})) → Stmt)
      Function = Multi.expl-to-inst(n) (Multi.compose(n) (_$₂_) (Multi.inst-to-expl(n) (Multi.Names.FunctionReplacement(f ↦ g ↦ ∀{y₁ y₂} → f(y₁) → g(y₂) → (y₁ ≡ y₂))(n))))


  record Total(φ : Xs ⇉ (Y → Stmt{ℓ₂})) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ (Lvl.⨆ ℓ𝓈)} where
    constructor intro
    field proof : Names.Total(φ)
