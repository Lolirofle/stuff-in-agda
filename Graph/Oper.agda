open import Type

module Graph.Oper {ℓ₁ ℓ₂} {V : Type{ℓ₁}} where

open import Logic.Propositional
open import Graph{ℓ₁}{ℓ₂}(V)

_∪_ : Graph → Graph → Graph
(g₁ ∪ g₂) v₁ v₂ = g₁ v₁ v₂ ∨ g₂ v₁ v₂ -- TODO: lift1On2
