module Logic.Computability.Binary where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Stmt using (IsTrue)
import      Data.Boolean.Stmt.Proofs as BooleanStmt
open import Data.Tuple
open import Functional
open import Logic
import      Logic.Computability as C
open import Logic.Classical
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Relator.Equals
open import Type

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} where
  ComputablyDecidable : (X → Y → Stmt{ℓ₃}) → Stmt
  ComputablyDecidable = C.ComputablyDecidable ∘ uncurry

  ComputablyDecidable-intro : {_▫_ : X → Y → Stmt} → (decide : X → Y → Bool) → ⦃ _ : ∀{x}{y} → (x ▫ y) ↔ (decide(x)(y) ≡ 𝑇) ⦄ → ComputablyDecidable(_▫_)
  ComputablyDecidable-intro {_▫_} (decide) ⦃ proof ⦄ = C.intro(uncurry decide) ⦃ lr ⦄ where
     l : ∀{arg} → ((uncurry _▫_)(arg)) ← ((uncurry decide)(arg) ≡ 𝑇)
     l{x , y} = [↔]-to-[←] (proof{x}{y})

     r : ∀{arg} → ((uncurry _▫_)(arg)) → ((uncurry decide)(arg) ≡ 𝑇)
     r{x , y} = [↔]-to-[→] (proof{x}{y})

     lr : ∀{arg} → ((uncurry _▫_)(arg)) ↔ ((uncurry decide)(arg) ≡ 𝑇)
     lr{x , y} = [↔]-intro (l{x , y}) (r{x , y})

  -- TODO: The other functions in Logic.Computability.ComputablyDecidable

  module ComputablyDecidable (_▫_ : X → Y → Stmt{ℓ₃}) ⦃ decidable : ComputablyDecidable(_▫_) ⦄ where
    decide : X → Y → Bool
    decide(x)(y) = C.ComputablyDecidable.decide (decidable) (x , y)

    proof : ∀{x y} → (x ▫ y) ↔ (decide(x)(y) ≡ 𝑇)
    proof{x}{y} = C.ComputablyDecidable.proof (decidable) {x , y}

    proof-istrue : ∀{x y} → (x ▫ y) ↔ IsTrue(decide(x)(y))
    proof-istrue = C.ComputablyDecidable.proof-istrue (decidable)

    negation : ComputablyDecidable(a ↦ b ↦ ¬(a ▫ b))
    negation = C.ComputablyDecidable.negation (decidable)

    classical : ∀{x}{y} → Classical(x ▫ y)
    classical = C.ComputablyDecidable.classical (decidable)

    module BinaryConnectives (_▫₂_ : X → Y → Stmt) ⦃ decidable₂ : ComputablyDecidable(_▫₂_) ⦄ where
      conjunction : ComputablyDecidable(a ↦ b ↦ (a ▫ b) ∧ (a ▫₂ b))
      conjunction = C.ComputablyDecidable-conjunction

      disjunction : ComputablyDecidable(a ↦ b ↦ (a ▫ b) ∨ (a ▫₂ b))
      disjunction = C.ComputablyDecidable-disjunction
