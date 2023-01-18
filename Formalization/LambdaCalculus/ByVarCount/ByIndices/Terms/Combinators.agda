module Formalization.LambdaCalculus.ByVarCount.ByIndices.Terms.Combinators where

import      Lvl
open import Data
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.Syntax.ImplicitLambda
open import Numeral.Natural
open import Numeral.Finite
open import Syntax.Number
open import Type

module _ where
  I K 𝈲 S B C W U ω Ω Y : Expression

  I = 𝜆 0                                 -- Identity
  K = 𝜆 𝜆 1                               -- Constant / Left of pair
  𝈲 = 𝜆 𝜆 0                               -- Right of pair
  S = 𝜆 𝜆 𝜆 (2 ← 0) ← (1 ← 0)             -- General composition
  B = 𝜆 𝜆 𝜆 2 ← (1 ← 0)                   -- Composition
  C = 𝜆 𝜆 𝜆 (2 ← 0) ← 1
  W = 𝜆 𝜆 (1 ← 0) ← 0
  U = 𝜆 0 ← 0                             -- Self application
  ω = U
  Ω = ω ← ω
  Y = 𝜆 (𝜆 1 ← (0 ← 0)) ← (𝜆 1 ← (0 ← 0))

module Proofs where
  open import Formalization.LambdaCalculus.ByVarCount.ByIndices.Semantics.Reduction
  open import Formalization.LambdaCalculus.ByVarCount.Functions  
  open import Logic.Propositional hiding (_←_)
  open import Logic.Propositional.Equiv
  open import Logic.Predicate
  open import ReductionSystem
  open import Relator.Equals.Proofs.Equiv
  open import Relator.ReflexiveTransitiveClosure renaming (trans to _🝖_)
  open import Structure.Relator
  open import Structure.Relator.Properties
  open import Type.Dependent.Sigma

  private variable n : ℕ
  private variable f g h x y z : Term(n)

  Ω-self-reduces : Ω β⇴ Ω
  Ω-self-reduces = β

  Ω-no-normal-form : ¬ NormalForm(_β⇴_)(Ω)
  Ω-no-normal-form (intro p) = p(Ω-self-reduces)

  I-reduction : ((I ← x) β⇴ x)
  I-reduction = β

  -- K-reduction : ((K ← x ← y) β⇴* x)
  -- K-reduction {x}{y} = super(cong-applyₗ β) 🝖 super β 🝖 substitute₂-₁ₗ(_β⇴*_)(_) substituteVarMax-depth-𝐒 refl

  -- 𝈲-reduction : ((𝈲 ← x ← y) β⇴* y)
  -- 𝈲-reduction {x}{y} = super(cong-applyₗ β) 🝖 super β
{-
  B-reduction : ((B ← f ← g ← x) β⇴* (f ← (g ← x)))
  B-reduction = super(cong-applyₗ(cong-applyₗ β)) 🝖 super(cong-applyₗ β) 🝖 super β 🝖 {!!}

  C-reduction : ((C ← f ← g ← x) β⇴* ((f ← x) ← g))
  C-reduction = super(cong-applyₗ(cong-applyₗ β)) 🝖 super(cong-applyₗ β) 🝖 super β

  S-reduction : ((S ← f ← g ← x) β⇴* ((f ← x) ← (g ← x)))
  S-reduction = super(cong-applyₗ(cong-applyₗ β)) 🝖 super(cong-applyₗ β) 🝖 super β

  Y-reduction : ∀{f} → ((Y ← f) β⥈* (f ← (Y ← f)))
  Y-reduction = super([∨]-introᵣ β) 🝖 super([∨]-introᵣ β) 🝖 super([∨]-introₗ(cong-applyᵣ β))
-}
-- TODO: Move everything below

{-
-- Also called: Church-Rosser's theorem.
-- TODO: Seems like the proof can be a bit complicated?
postulate β-star-confluence : ∀{d} → Confluence(_β⇴*_ {d})

open import Formalization.LambdaCalculus.ByVarCount.Functions

module Tuple where
  open Boolean
  open ExplicitLambdaSyntax

  Pair = 𝜆 0 (𝜆 1 (𝜆 2 (2 ← 0 ← 1)))
  Projₗ = 𝜆 0 (0 ← var-𝐒 K)
  Projᵣ = 𝜆 0 (0 ← var-𝐒 𝈲)

module β-proofs where
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction
  open import Logic.Propositional hiding (_←_)
  open import Logic.Predicate
  open import ReductionSystem
  open import Relator.ReflexiveTransitiveClosure renaming (trans to _🝖_)
  open import Structure.Relator
  open import Structure.Relator.Properties
  open import Type.Dependent.Sigma

  open ExplicitLambdaSyntax

  private variable n : ℕ
  private variable f g h x y z : Term(n)

  module _ where
    open Tuple

    Pair-projₗ-reduction : (Projₗ ← (Pair ← x ← y)) β⇴* x
    Pair-projₗ-reduction = super β 🝖 super(cong-applyₗ(cong-applyₗ β)) 🝖 super(cong-applyₗ β) 🝖 super β 🝖 super(cong-applyₗ β) 🝖 super β

    Pair-projᵣ-reduction : (Projᵣ ← (Pair ← x ← y)) β⇴* y
    Pair-projᵣ-reduction = super β 🝖 super(cong-applyₗ(cong-applyₗ β)) 🝖 super(cong-applyₗ β) 🝖 super β 🝖 super(cong-applyₗ β) 🝖 super β

-}
