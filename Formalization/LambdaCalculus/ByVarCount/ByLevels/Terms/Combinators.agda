module Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Combinators where

import      Lvl
open import Data
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.Syntax.ExplicitLambda
open import Numeral.Natural
open import Numeral.Finite
open import Syntax.Number
open import Type

module _ where
  I = 𝜆 0 0                               -- Identity
  K = 𝜆 0 (𝜆 1 0)                         -- Constant / Left of pair
  𝈲 = 𝜆 0 (𝜆 1 1)                         -- Right of pair
  S = 𝜆 0 (𝜆 1 (𝜆 2 ((0 ← 2) ← (1 ← 2)))) -- General composition
  B = 𝜆 0 (𝜆 1 (𝜆 2 (0 ← (1 ← 2))))       -- Composition
  C = 𝜆 0 (𝜆 1 (𝜆 2 ((0 ← 2) ← 1)))
  W = 𝜆 0 (𝜆 1 ((0 ← 1) ← 1))
  U = 𝜆 0 (0 ← 0)                         -- Self application
  ω = U
  Ω = ω ← ω
  Y = 𝜆 0 ((𝜆 1 (0 ← (1 ← 1))) ← (𝜆 1 (0 ← (1 ← 1))))

module Proofs where
  open import Data.Either using (Left ; Right)
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction.Proofs
  open import Formalization.LambdaCalculus.ByVarCount.Functions using () renaming (varShift𝐒ᵢ to _↑ ; varShift𝐒₀ to _↑₀)
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  private variable n : ℕ
  private variable f g h x y z : Term(n)

  Ω-self-reduces : Ω β⇴ Ω
  Ω-self-reduces = β

  I-reduction : ((I ← x) β⇴ x)
  I-reduction = β

  K-reduction : ((K ← x ← y) β⇴* x)
  K-reduction {x}{y} =
    K ← x ← y       🝖-[ cong-applyₗ β ]-sub
    (𝜆 0 (x ↑)) ← y 🝖-[ β ]-sub
    x               🝖-end
    -- 🝖 substitute₂-₁ₗ(_β⇴_)(_) (substituteVar-varShift𝐒 {n = maximum}{y = y}{x = x}) ?
    -- 🝖 substitute₂ₗ(_β⇴*_) (symmetry(_≡_) (substitute-var-𝐒 {0}{x}{y})) refl

  𝈲-reduction : ((𝈲 ← x ← y) β⇴* y)
  𝈲-reduction {x}{y} =
    𝈲 ← x ← y   🝖-[ cong-applyₗ β ]-sub
    (𝜆 0 0) ← y 🝖-[ β ]-sub
    y           🝖-end

  B-reduction : ((B ← f ← g ← x) β⇴* (f ← (g ← x)))
  B-reduction {f}{g}{x} =
    B ← f ← g ← x                           🝖-[ cong-applyₗ(cong-applyₗ β) ]-sub
    (𝜆 0 (𝜆 1 ((f ↑ ↑) ← (0 ← 1)))) ← g ← x 🝖-[ cong-applyₗ β ]-sub
    (𝜆 0 ((f ↑) ← ((g ↑) ← 0))) ← x         🝖-[ β ]-sub
    f ← (g ← x)                             🝖-end

  C-reduction : ((C ← f ← g ← x) β⇴* ((f ← x) ← g))
  C-reduction {f}{g}{x} =
    C ← f ← g ← x                            🝖-[ cong-applyₗ(cong-applyₗ β) ]-sub
    (𝜆 0 (𝜆 1 (((f ↑ ↑) ← 1) ← 0))) ← g ← x  🝖-[ cong-applyₗ β ]-sub
    (𝜆 0 (((f ↑) ← 0) ← (g ↑))) ← x          🝖-[ β ]-sub
    f ← x ← g                                🝖-end

  S-reduction : ((S ← f ← g ← x) β⇴* ((f ← x) ← (g ← x)))
  S-reduction {f}{g}{x} =
    S ← f ← g ← x                                 🝖-[ cong-applyₗ(cong-applyₗ β) ]-sub
    (𝜆 0 (𝜆 1 (((f ↑ ↑) ← 1) ← (0 ← 1)))) ← g ← x 🝖-[ cong-applyₗ β ]-sub
    (𝜆 0 (((f ↑) ← 0) ← ((g ↑) ← 0))) ← x         🝖-[ β ]-sub
    f ← x ← (g ← x)                               🝖-end

  Y-reduction : ((Y ← f) β⥈* (f ← (Y ← f)))
  Y-reduction {f} =
    Y ← f                                                   🝖-[ Right β ]-sub
    (𝜆 0 ((f ↑) ← (0 ← 0))) ← (𝜆 0 ((f ↑) ← (0 ← 0)))       🝖-[ Right β ]-sub
    f ← ((𝜆 0 ((f ↑) ← (0 ← 0))) ← (𝜆 0 ((f ↑) ← (0 ← 0)))) 🝖-[ Left(cong-applyᵣ β) ]-sub
    f ← (Y ← f)                                             🝖-end
