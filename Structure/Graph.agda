module Structure.Graph where

open import Lang.Instance
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals
open import Relator.Equals.Equivalence
open import Sets.Setoid
open import Sets.Setoid.Uniqueness
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Function
open import Type
open import Type.Unit

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} where
  -- A graph is represented by a binary relation which states whether there is an edge from one vertex to another.
  -- In other words, a graph is here defined by only its adjacency relation.
  -- This is by default (without any assumptions) a directed multigraph which is possibly infinite.
  Graph : Type
  Graph = (V → V → Type{ℓ₂})

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : V → V → Type{ℓ₂}) where
  -- Two vertices are adjacent when there is an edge from the first one to the second one.
  Adjacent = _⟶_

  -- A graph is singular when it is not a multigraph.
  -- Note: Equality on edges must respect uniqueness. In other words, one edge must not have multiple constructions.
  record Singular : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{a b : V} → IsProp(a ⟶ b)
  singular = inst-fn Singular.proof

  -- A path is matching directed edges connected to each other in a finite sequence.
  -- This is essentially a list of edges where the ends match.
  -- The terminology is that a walk is a sequence of connected edges and it visits all its vertices.
  -- Note: Walk is a generalized List for categories instead of monoids.
  data Walk : V → V → Type{ℓ₁ Lvl.⊔ ℓ₂} where
    start : Names.Reflexivity(Walk)
    step  : ∀{a b c} → (a ⟶ b) → (Walk b c) → (Walk a c)

  -- `WalksOn edge walk` states that the walk `walk` contains the edge `edge`.
  -- In other words, there is a step in the walk which is `edge`.
  -- Note: WalksOn is a generalized containment relation for paths instead of lists.
  data WalksOn {v₁ v₂ : V} (edge : v₁ ⟶ v₂) : ∀{a b : V} → Walk a b → Type{ℓ₁ Lvl.⊔ ℓ₂} where
    current : ∀{c : V}{rest : Walk v₂ c} → WalksOn edge (Walk.step edge rest)
    skip    : ∀{a b c : V}{e : (a ⟶ b)}{rest : Walk b c} → WalksOn edge rest → WalksOn edge (Walk.step e rest)

  -- `WalksThrough v walk` states that the walk `walk` visits the vertex `v`.
  -- In other words, one of the steps/edges in the walk mention the vertex v.
  data WalksThrough (v : V) : ∀{a b : V} → Walk a b → Type{ℓ₁ Lvl.⊔ ℓ₂} where
    current : ∀{b : V}{path : Walk v b} → WalksThrough v path
    skip    : ∀{a b c : V}{e : (a ⟶ b)}{rest : Walk b c} → WalksThrough v rest → WalksThrough v (Walk.step e rest)

  

  -- A walk that never visits the same edge twice.
  -- Note: Equality on edges must respect uniqueness. In other words, one edge must not have multiple constructions.
  record Trail (a : V) (b : V) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      walk   : Walk a b
      unique : ∀{v₁ v₂ : V}{edge : v₁ ⟶ v₂} → IsProp(WalksOn edge walk)

  module _ {a b : V} (walk : Walk a b) where
    -- A walk that never visits the same vertex twice.
    -- Also called "Simple path".
    -- Note: Equality on edges must respect uniqueness. In other words, one edge must not have multiple constructions.
    record Path : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{v : V} → Unique(WalksThrough v walk)
    path = inst-fn Path.proof

    record Traceable : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{v : V} → WalksThrough(v) walk
    traceable = inst-fn Traceable.proof

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : V → V → Type{ℓ₂}) where
  -- An undirected graph have for every edge always an edge in the other direction.
  Undirected = Symmetry(_⟶_)
  undirected = symmetry(_⟶_)

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : V → V → Type{ℓ₂}) where
  -- A complete graph have all the possible edges for its vertices.
  record Complete : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x y : V} → (x ⟶ y)
  complete = inst-fn Complete.proof

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : V → V → Type{ℓ₂}) where
  -- A connected graph have walks from every vertex to any vertex.
  -- For undirected graphs, this can be visually interpreted as disconnected islands of vertices.
  -- Note: Equality on edges must respect uniqueness. In other words, one edge must not have multiple constructions.
  Connected = Complete(Walk(_⟶_))
  connected = complete(Walk(_⟶_))

-- TODO: These definitions only works when the graph is not a multigraph
module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : V → V → Type{ℓ₂}) where
  record IsTree : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x y : V} → IsUnit(Path(_⟶_) x y) -- TODO: Does not work because the field `unique` is a function
  isTree = inst-fn IsTree.proof

  record IsForest : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x y : V} → IsProp(Path(_⟶_) x y)
  isForest = inst-fn IsForest.proof
