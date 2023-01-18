module Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Tuple where

open import Data
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Combinators using (K ; 𝈲)
open import Formalization.LambdaCalculus.ByVarCount.Functions using () renaming (varShift𝐒₀ to _↑₀)
open import Formalization.LambdaCalculus.ByVarCount.Syntax.ExplicitLambda
open import Numeral.Natural
open import Syntax.Number

module _ where
  Pair = 𝜆 0 (𝜆 1 (𝜆 2 (2 ← 0 ← 1)))
  Projₗ = 𝜆 0 (0 ← (K ↑₀))
  Projᵣ = 𝜆 0 (0 ← (𝈲 ↑₀))

module Proofs where
  open        Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Combinators.Proofs
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction.Proofs
  open        Formalization.LambdaCalculus.ByVarCount.Functions using () renaming (varShift𝐒ᵢ to _↑)
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  private variable n : ℕ
  private variable x y : Term(n)

  module _ where
    Pair-projₗ-reduction : (Projₗ ← (Pair ← x ← y)) β⇴* x
    Pair-projₗ-reduction {x}{y} =
      Projₗ ← (Pair ← x ← y)                🝖-[ β ]-sub
      (Pair ← x ← y) ← K                    🝖-[ cong-applyₗ(cong-applyₗ β) ]-sub
      (𝜆 0 (𝜆 1 (1 ← (x ↑ ↑) ← 0))) ← y ← K 🝖-[ cong-applyₗ β ]-sub
      (𝜆 0 (0 ← (x ↑) ← (y ↑))) ← K         🝖-[ β ]-sub
      K ← x ← y                             🝖-[ K-reduction ]
      x                                     🝖-end

    Pair-projᵣ-reduction : (Projᵣ ← (Pair ← x ← y)) β⇴* y
    Pair-projᵣ-reduction {x}{y} =
      Projᵣ ← (Pair ← x ← y)                🝖-[ β ]-sub
      (Pair ← x ← y) ← 𝈲                    🝖-[ cong-applyₗ(cong-applyₗ β) ]-sub
      (𝜆 0 (𝜆 1 (1 ← (x ↑ ↑) ← 0))) ← y ← 𝈲 🝖-[ cong-applyₗ β ]-sub
      (𝜆 0 (0 ← (x ↑) ← (y ↑))) ← 𝈲         🝖-[ β ]-sub
      𝈲 ← x ← y                             🝖-[ 𝈲-reduction ]
      y                                     🝖-end
