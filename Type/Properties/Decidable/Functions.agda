module Type.Properties.Decidable.Functions where

open import Data
import      Lvl
open import Data.Boolean as Bool using (Bool ; 𝑇 ; 𝐹 ; not ; if_then_else_)
open import Data.Boolean.Proofs
open import Data.Boolean.Stmt
open import Functional
open import Logic.Propositional
open import Type.Properties.Decidable
open import Type

private variable ℓ ℓₚ : Lvl.Level
private variable A B C P Q : Type{ℓ}
private variable b : Bool

introTrue : P → IsTrue(b) → Decider₀(P)(b)
introTrue {b = 𝑇} p _ = true p

introFalse : (¬ P) → IsFalse(b) → Decider₀(P)(b)
introFalse {b = 𝐹} np _ = false np

flatMap : (f : Bool → Bool) → (P → Decider₀(Q)(f(𝑇))) → ((P → Empty) → Decider₀(Q)(f(𝐹))) → (∀{b} → Decider₀(P)(b) → Decider₀(Q)(f(b)))
flatMap f = elim (\{b} _ → Decider₀(_)(f(b)))

map : ∀{ℓ₁ ℓ₂}{P : Type{ℓ₁}}{Q : Type{ℓ₂}} →
  let Qb = if_then Q else (Q → Empty)
  in (f : Bool → Bool) → (P → Qb(f(𝑇))) → ((P → Empty) → Qb(f(𝐹))) → (∀{b} → Decider₀(P)(b) → Decider₀(Q)(f(b)))
map {P = P}{Q = Q} f p np =
  let proof = if-intro(\{b} T → T → Decider₀ Q b) true false
  in flatMap f (proof ∘ p) (proof ∘ np)

mapProp : (P → Q) → ((P → Empty) → (Q → Empty)) → (∀{b} → Decider₀(P)(b) → Decider₀(Q)(b))
mapProp p np = flatMap id (true ∘ p) (false ∘ np)

mapNegProp : (P → (Q → Empty)) → ((P → Empty) → Q) → (∀{b} → Decider₀(P)(b) → Decider₀(Q)(not b))
mapNegProp p np = flatMap not (false ∘ p) (true ∘ np)
