open import Type

module Graph.Properties.Proofs where

open import Data.Either.Proofs
open import Functional
open import Function.Equals
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
import      Lvl
open import Graph
open import Graph.Properties
open import Relator.Equals.Proofs.Equivalence
open import Sets.Setoid.Uniqueness
open import Structure.Relator.Properties
open import Type.Unit

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : Graph{ℓ₁}{ℓ₂}(V)) where
  instance
    undirect-undirected : Undirected(undirect(_⟶_))
    Undirected.reversable         undirect-undirected = intro [∨]-symmetry
    Undirected.reverse-involution undirect-undirected = intro swap-involution

  -- [++]-visits : ∀{ae be a₁ b₁ a₂ b₂}{e : ae ⟶ be}{w₁ : Walk(_⟶_) a₁ b₁}{w₂ : Walk(_⟶_) a₂ b₂} → (Visits(_⟶_) e w₁) ∨ (Visits(_⟶_) e w₂) → Visits(_⟶_) e (w₁ ++ w₂)

  complete-singular-is-undirected : ⦃ Complete(_⟶_) ⦄ → ⦃ Singular(_⟶_) ⦄ → Undirected(_⟶_)
  Undirected.reversable         complete-singular-is-undirected = intro(const(complete(_⟶_)))
  Undirected.reverse-involution complete-singular-is-undirected = intro(singular(_⟶_))

  -- traceable-is-connected : ⦃ Traceable(_⟶_) ⦄ → Connected(_⟶_)
