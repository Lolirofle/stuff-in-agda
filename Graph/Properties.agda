open import Type

module Graph.Properties where

open import Functional
open import Function.Equals
open import Lang.Instance
open import Logic
open import Logic.Propositional
import      Lvl
open import Graph
open import Relator.Equals.Proofs.Equiv
open import Structure.Setoid.Uniqueness
open import Structure.Relator.Properties
open import Type.Properties.MereProposition

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : Graph{ℓ₁}{ℓ₂}(V)) where
  -- An undirected graph always have for every edge an edge in the other direction which is the same edge.
  record Undirected : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      ⦃ reversable ⦄ : Symmetry(_⟶_)
    reverse = symmetry(_⟶_)

    field
      reverse-involution : ∀{a b} → (reverse ∘ reverse ⊜ (id {T = a ⟶ b}))
  undirected-reverse = inst-fn Undirected.reverse

  -- Construction of an undirected graph from any graph.
  undirect : Graph{ℓ₁}{ℓ₂}(V)
  undirect a b = (b ⟶ a) ∨ (a ⟶ b)

  -- A graph is singular when there is at most one edge between every pair of vertices.
  -- In other words, when it is not a multigraph.
  -- Note: Equality on edges must respect uniqueness. In other words, one edge must not have multiple constructions.
  record Singular : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{a b : V} → MereProposition(a ⟶ b)
  singular = inst-fn(\inst {a}{b}{x}{y} → MereProposition.uniqueness(Singular.proof inst {a}{b}) {x}{y})

  -- A complete graph have an edge for each pair of vertices from V. TODO: Exclude loops
  record Complete : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x y : V} → (x ⟶ y)
  complete = inst-fn Complete.proof

  -- A linear graph contains vertices with a maximum of one outgoing edge and a maximum of one ingoing edge.
  record Linear : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      unique-start-vertex : ∀{y} → Unique(x ↦ (x ⟶ y))
      unique-end-vertex   : ∀{x} → Unique(y ↦ (x ⟶ y))

  module _ (v : V) where
    -- An initial vertex have no ingoing edges pointing towards it.
    record InitialVertex : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{x} → ¬(x ⟶ v)
    initialVertex = inst-fn InitialVertex.proof

    -- A final vertex have no outgoing edges pointing from it.
    record FinalVertex : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{x} → ¬(v ⟶ x)
    finalVertex = inst-fn FinalVertex.proof

  -- A graph is a list when it is linear and has an unique initial vertex and an unique final vertex.
  -- The linearity guarantees so that if there are preceding and succeding elements of the list, they are unique.
  -- The initial vertex represents the first element of the list.
  -- The final vertex represents the last element of the list.
  record IsList : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      ⦃ linear ⦄ : Linear
      unique-initial-vertex : Unique(InitialVertex)
      unique-final-vertex   : Unique(FinalVertex)

  -- A graph is a cycle when it is linear and do not have initial or final vertices.
  -- The linearity guarantees so that if there are preceding and succeding elements of the list, they are unique.
  -- The non-existence of initial vertices and final vertices means no first and last elements.
  record IsCycle : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      ⦃ linear ⦄ : Linear
      no-initial-vertex : ∀{v} → ¬(InitialVertex v)
      no-final-vertex   : ∀{v} → ¬(FinalVertex v)

  module _ where
    open import Graph.Walk
    open import Graph.Walk.Properties

    -- A graph is a tree when it has an unique path between every pair of vertices.
    -- The existence of a path means that it is always possible to traverse the tree from every vertex along the edges to every vertex.
    record IsTree : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{x y : V} → ∃!{T = Walk(_⟶_) x y}(Path)
    isTree = inst-fn IsTree.proof

    record IsForest : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{x y : V} → Unique{T = Walk(_⟶_) x y}(Path)
    isForest = inst-fn IsForest.proof

    record IsOutwardRootedTree : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field
        ⦃ tree ⦄ : IsTree
        unique-initial-vertex : ∃!(InitialVertex)
        -- TODO: Should not this be defined as ∃!(root ↦ InitialVertex(root) ∧ (∀{x : V} → ∃!{T = Walk(_⟶_) root x}(Path))) ?

    record IsInwardRootedTree : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field
        ⦃ tree ⦄ : IsTree
        unique-initial-vertex : ∃!(FinalVertex)

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : Graph{ℓ₁}{ℓ₂}(V)) where
  open import Graph.Walk

  -- A connected graph have walks from every vertex to any vertex.
  -- For undirected graphs, this can be visually interpreted as disconnected islands of vertices.
  -- Note: Equality on edges must respect uniqueness. In other words, one edge must not have multiple constructions.
  Connected = Complete(Walk(_⟶_))
  connected = complete(Walk(_⟶_))
