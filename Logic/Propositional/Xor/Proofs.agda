module Logic.Propositional.Xor.Proofs where

open import Data
open import Data.Boolean.Stmt
open import Functional
open import Logic.Propositional
open import Logic.Propositional.Xor.Functions
import      Lvl
open import Type

private variable ℓ : Lvl.Level
private variable A B : Type{ℓ}

isLeft-correctness : ∀{e : (A ⊕ B)} → IsTrue(isLeft e) ↔ A
isLeft-correctness {e = [⊕]-introₗ a nb} = [↔]-intro (const <>) (const a)
isLeft-correctness {e = [⊕]-introᵣ b na} = [↔]-intro ([⊥]-elim ∘ na) \()

isRight-correctness : ∀{e : (A ⊕ B)} → IsTrue(isRight e) ↔ B
isRight-correctness {e = [⊕]-introₗ a nb} = [↔]-intro ([⊥]-elim ∘ nb) \()
isRight-correctness {e = [⊕]-introᵣ b na} = [↔]-intro (const <>) (const b)
