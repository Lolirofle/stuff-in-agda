module Lang.Irrelevance.Convertable where

open import Lang.Instance
import      Lvl
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₚ : Lvl.Level
private variable A B C P Q R T : Type{ℓ}
private variable f g : A → B

module _ (T : Type{ℓ}) where
  -- The property of being able to convert the existence of an irrelevant witness to the existence of a relevant one.
  -- TODO: Is this neccessary? Are there any convertable but undecidable types?
  record Convertable : Type{ℓ} where
    constructor intro
    field proof : .T → T
  convert = inst-fn Convertable.proof

module _ where
  open import Data

  Unit-convertable-raw : .(Unit{ℓ₁}) → Unit{ℓ₂}
  Unit-convertable-raw _ = <>

  Empty-convertable-raw : .(Empty{ℓ₁}) → Empty{ℓ₂}
  Empty-convertable-raw ()

  instance
    Unit-convertable : Convertable(Unit{ℓ})
    Unit-convertable = intro Unit-convertable-raw

  instance
    Empty-convertable : Convertable(Empty{ℓ})
    Empty-convertable = intro Empty-convertable-raw

module _ where
  open import Data
  open import Data.Boolean
  open import Functional.Irrelevant
  open import Logic.Classical
  open import Logic.Propositional
  open import Type.Properties.Decidable
  open import Type.Properties.Decidable.Proofs
  open import Type.Properties.Inhabited

  private variable b b₁ b₂ d : Bool

  Inhabited-convertable : ⦃ pos : (◊ T) ⦄ → Convertable(T)
  Inhabited-convertable = intro(constᵢᵣᵣ [◊]-existence)

  classical-convertable : ⦃ classical : Classical(P) ⦄ → Convertable(P)
  classical-convertable{P = P} with excluded-middle(P)
  ... | [∨]-introₗ p  = intro(constᵢᵣᵣ p)
  ... | [∨]-introᵣ np = intro([⊥]-elim ∘ᵢᵣᵣ₀ (convert(⊥) ∘ᵢᵣᵣ₋ np))

  decider-convertable : ⦃ dec : Decider₀(P)(b) ⦄ → Convertable(P)
  decider-convertable{P = P} = classical-convertable ⦃ decider-classical(P) ⦄
