module Formalization.LambdaCalculus.Terms.Combinators where

import      Lvl
open import Data
open import Formalization.LambdaCalculus
open import Numeral.Natural
open import Numeral.Finite
open import Syntax.Number
open import Type

module _ where
  open ExplicitLambdaSyntax

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

-- TODO: Move everything below

open import Formalization.LambdaCalculus.SyntaxTransformation

module Boolean where
  open ExplicitLambdaSyntax

  𝑇 = K
  𝐹 = 𝈲
  If = 𝜆 0 (𝜆 1 (𝜆 2 (0 ← 1 ← 2)))

module Tuple where
  open Boolean
  open ExplicitLambdaSyntax

  Pair = 𝜆 0 (𝜆 1 (𝜆 2 (2 ← 0 ← 1)))
  Projₗ = 𝜆 0 (0 ← var-𝐒 K)
  Projᵣ = 𝜆 0 (0 ← var-𝐒 𝈲)

-- Natural numbers (Church numerals).
module Natural where
  open ExplicitLambdaSyntax

  λ𝟎 = 𝈲
  λ𝐒 = 𝜆 0 (𝜆 1 (𝜆 2 (1 ← (0 ← 1 ← 2))))

  ℕrepr₂ : ℕ → Term(2)
  ℕrepr₂ 𝟎      = 1
  ℕrepr₂ (𝐒(n)) = 0 ← ℕrepr₂ n

  ℕrepr = \n → 𝜆 0 (𝜆 1 (ℕrepr₂ n))

  -- TODO: Prove (λ𝐒 ←ⁿ λ𝟎) β-reduces to (ℕrepr n)

module β-proofs where
  open import Formalization.LambdaCalculus.Semantics.Reduction
  open import Logic.Propositional hiding (_←_)
  open import Logic.Predicate
  open import ReductionSystem
  open import Relator.ReflexiveTransitiveClosure renaming (trans to _🝖_)
  open import Structure.Relator
  open import Structure.Relator.Properties
  open import Type.Dependent

  open ExplicitLambdaSyntax

  private variable n : ℕ
  private variable f g h x y z : Term(n)

  Ω-self-reduces : Ω β⇴ Ω
  Ω-self-reduces = β

  Ω-no-normal-form : ¬ NormalForm(_β⇴_)(Ω)
  Ω-no-normal-form (intro p) = p(Ω-self-reduces)

  -- Also called: Church-Rosser's theorem.
  -- TODO: Seems like the proof can be a bit complicated?
  postulate β-star-confluence : ∀{d} → Confluence(_β⇴*_ {d})

  I-reduction : ((I ← x) β⇴ x)
  I-reduction = β

  K-reduction : ((K ← x ← y) β⇴* x)
  K-reduction {x}{y} = super(cong-applyₗ β) 🝖 super β -- 🝖 substitute₂ₗ(_β⇴*_) (symmetry(_≡_) (substitute-var-𝐒 {0}{x}{y})) refl

  𝈲-reduction : ((𝈲 ← x ← y) β⇴* y)
  𝈲-reduction {x}{y} = super(cong-applyₗ β) 🝖 super β

  B-reduction : ((B ← f ← g ← x) β⇴* (f ← (g ← x)))
  B-reduction = super(cong-applyₗ(cong-applyₗ β)) 🝖 super(cong-applyₗ β) 🝖 super β

  C-reduction : ((C ← f ← g ← x) β⇴* ((f ← x) ← g))
  C-reduction = super(cong-applyₗ(cong-applyₗ β)) 🝖 super(cong-applyₗ β) 🝖 super β

  S-reduction : ((S ← f ← g ← x) β⇴* ((f ← x) ← (g ← x)))
  S-reduction = super(cong-applyₗ(cong-applyₗ β)) 🝖 super(cong-applyₗ β) 🝖 super β

  Y-reduction : ∀{f} → ((Y ← f) β⥈* (f ← (Y ← f)))
  Y-reduction = super([∨]-introᵣ β) 🝖 super([∨]-introᵣ β) 🝖 super([∨]-introₗ(cong-applyᵣ β))

  module _ where
    open Boolean

    If-𝑇-reduction : ((If ← 𝑇 ← x ← y) β⇴* x)
    If-𝑇-reduction = super(cong-applyₗ(cong-applyₗ β)) 🝖 super(cong-applyₗ β) 🝖 super β 🝖 K-reduction

    If-𝐹-reduction : ((If ← 𝐹 ← x ← y) β⇴* y)
    If-𝐹-reduction = super(cong-applyₗ(cong-applyₗ β)) 🝖 super(cong-applyₗ β) 🝖 super β 🝖 𝈲-reduction

  module _ where
    open Tuple

    Pair-projₗ-reduction : (Projₗ ← (Pair ← x ← y)) β⇴* x
    Pair-projₗ-reduction = super β 🝖 super(cong-applyₗ(cong-applyₗ β)) 🝖 super(cong-applyₗ β) 🝖 super β 🝖 super(cong-applyₗ β) 🝖 super β

    Pair-projᵣ-reduction : (Projᵣ ← (Pair ← x ← y)) β⇴* y
    Pair-projᵣ-reduction = super β 🝖 super(cong-applyₗ(cong-applyₗ β)) 🝖 super(cong-applyₗ β) 🝖 super β 🝖 super(cong-applyₗ β) 🝖 super β

  module _ where
    open import Function.Iteration

    open Natural

    {-
    -- λ𝟎 β⇴* ℕrepr 𝟎
    λ𝐒-of-ℕrepr : (λ𝐒 ← ℕrepr(n)) β⇴* ℕrepr(𝐒(n))
    λ𝐒-of-ℕrepr = super {!cong-applyₗ ?!}

    ℕrepr-correctness : (((λ𝐒 ←_) ^ n) λ𝟎) β⇴* (ℕrepr n)
    ℕrepr-correctness {𝟎} = refl
    ℕrepr-correctness {𝐒 n} = super {!!} 🝖 super {!ℕrepr-correctness {n}!}
    -}
