module Logic.DiagonalMethod where

open import Functional
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Function
open import Type.Size
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}

-- Also called: Diagonal method, Cantor's diagonal argument.
function-type-surjectivity-fixpoint : (A ≽ (A → B)) → ∀{f : B → B} → ∃(Fixpoint f)
function-type-surjectivity-fixpoint ([∃]-intro s) {f}
  with [∃]-intro i ⦃ p ⦄ ← surjective(s) {f ∘ (s $₂_)}
  = [∃]-intro(s i i) ⦃ intro(symmetry(_≡_) (congruence₂ₗ(_$_)(i) p)) ⦄

module _ where
  open import Data.Boolean
  open import Data.Boolean.Proofs

  decidable-power-set-no-surjection : ¬(T ≽ (T → Bool))
  decidable-power-set-no-surjection = (p ↦ [!]-no-fixpoints(Fixpoint.proof([∃]-proof(p{not})))) ∘ function-type-surjectivity-fixpoint

module _ where
  open import Data.Boolean
  open import Data.Boolean.Proofs
  open import Function.Inverseᵣ
  open import Structure.Function.Domain.Proofs
  open import Structure.Function
  open import Syntax.Transitivity

  function-type-no-surjection : (B ≽ Bool) → ¬(A ≽ (A → B))
  function-type-no-surjection ([∃]-intro r-bool) surj
    with [∃]-intro i ⦃ fix ⦄ ← function-type-surjectivity-fixpoint surj {invᵣ r-bool ⦃ surjective-to-invertibleᵣ ⦄ ∘ not ∘ r-bool}
    = [!]-no-fixpoints(symmetry(_≡_) (Inverseᵣ.proof surjective-to-inverseᵣ) 🝖 congruence₁(r-bool) (Fixpoint.proof fix))

module _ where
  open import Numeral.Natural
  open import Numeral.Natural.Oper.Proofs

  ℕ-function-non-surjectivity : ¬(ℕ ≽ (ℕ → ℕ))
  ℕ-function-non-surjectivity = (p ↦ 𝐒-not-self(Fixpoint.proof([∃]-proof(p{𝐒})))) ∘ function-type-surjectivity-fixpoint
