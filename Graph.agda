open import Type

module Graph {ℓ₁ ℓ₂} (V : Type{ℓ₁}) where

-- A graph is represented by a binary relation which states whether there is an edge from one vertex to another.
-- In other words, a graph is here defined by only its adjacency relation.
-- This is by default (without any assumptions) a directed multigraph which is possibly infinite.
--
-- An object of type Graph is the adjacency relation.
-- For (_⟶_ : Graph), (a b : V), an object of type (a ⟶ b) is an edge from vertices a to b, and its existence means that there is an edge from a to b.
Graph : Type
Graph = (V → V → Type{ℓ₂})

module _ (_⟶_ : Graph) where
  -- Two vertices are adjacent when there is an edge from the first one to the second one.
  Adjacent = _⟶_
