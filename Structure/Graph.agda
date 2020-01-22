module Structure.Graph where

import      Data.Either as Either
open import Data.Either.Proofs
open import Functional
open import Function.Equals
open import Lang.Instance
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
-- open import Relator.Equals using ()
open import Relator.Equals.Proofs.Equivalence hiding ([≡]-with)
open import Relator.Equals.Proofs using ([≡]-substitutionₗ)
import      Sets.PredicateSet as PredSet
open import Sets.Setoid
open import Sets.Setoid.Uniqueness
open import Structure.Function.Domain
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Function
open import Type
open import Type.Dependent
open import Type.Dependent.Functions
open import Type.Unit

module _ {ℓ₁ ℓ₂} (V : Type{ℓ₁}) where
  -- A graph is represented by a binary relation which states whether there is an edge from one vertex to another.
  -- In other words, a graph is here defined by only its adjacency relation.
  -- This is by default (without any assumptions) a directed multigraph which is possibly infinite.
  --
  -- An object of type Graph is the adjacency relation.
  -- For (_⟶_ : Graph), (a b : V), an object of type (a ⟶ b) is an edge from vertices a to b, and its existence means that there is an edge from a to b.
  Graph : Type
  Graph = (V → V → Type{ℓ₂})

  _∪_ : Graph → Graph → Graph
  (g₁ ∪ g₂) v₁ v₂ = g₁ v₁ v₂ ∨ g₂ v₁ v₂ -- TODO: lift1On2

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : Graph{ℓ₁}{ℓ₂}(V)) where
  -- Two vertices are adjacent when there is an edge from the first one to the second one.
  Adjacent = _⟶_

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
  undirect : Graph(V)
  undirect a b = (b ⟶ a) ∨ (a ⟶ b)

  -- A graph is singular when there is at most one edge between every pair of vertices.
  -- In other words, when it is not a multigraph.
  -- Note: Equality on edges must respect uniqueness. In other words, one edge must not have multiple constructions.
  record Singular : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{a b : V} → IsProp(a ⟶ b)
  singular = inst-fn(\inst {a}{b}{x}{y} → IsProp.uniqueness(Singular.proof inst {a}{b}) {x}{y})

  -- A path is matching directed edges connected to each other in a finite sequence.
  -- This is essentially a list of edges where the ends match.
  -- The terminology is that a walk is a sequence of connected edges and it visits all its vertices.
  -- Note: Walk is a generalized "List" for categories instead of the usual List which is for monoids.
  data Walk : V → V → Type{ℓ₁ Lvl.⊔ ℓ₂} where
    at      : Names.Reflexivity(Walk)
    prepend : ∀{a b c} → (a ⟶ b) → (Walk b c) → (Walk a c)

  module WalkFunctions where
    edge : ∀{a b} → (a ⟶ b) → (Walk a b)
    edge e = prepend e at

    join : ∀{a b c} → (a ⟶ b) → (b ⟶ c) → (Walk a c)
    join e₁ e₂ = prepend e₁ (edge e₂)

    _++_ : ∀{a b c} → Walk a b → Walk b c → Walk a c
    at            ++ w₂ = w₂
    prepend e₁ w₁ ++ w₂ = prepend e₁ (w₁ ++ w₂)

    postpend : ∀{a b c} → (Walk a b) → (b ⟶ c) → (Walk a c)
    postpend at             e₂ = edge e₂
    postpend (prepend e₁ w) e₂ = prepend e₁ (postpend w e₂)

    reverse : ⦃ Undirected ⦄ → ∀{a b} → Walk a b → Walk b a
    reverse at            = at
    reverse (prepend e w) = postpend (reverse w) (undirected-reverse e)

    prelop : ∀{a c} → (Walk a c) → Σ(_)(b ↦ Walk b c)
    prelop at            = Σ.intro _ at
    prelop (prepend e w) = Σ.intro _ w

    postlop : ∀{a c} → (Walk a c) → Σ(_)(b ↦ Walk a b)
    postlop at                          = Σ.intro _ at
    postlop (prepend e  at)             = Σ.intro _ at
    postlop (prepend e₁ (prepend e₂ w)) = [Σ]-mapᵣ (postlop(prepend e₂ w)) (prepend e₁)

    length : ∀{a b} → (Walk a b) → ℕ
    length at            = 𝟎
    length (prepend _ w) = 𝐒(length w)

  -- `Passes edge walk` states that the walk `walk` contains the edge `edge`.
  -- In other words, there is a step in the walk which is `edge`.
  -- Note: Passes is a generalized containment relation for paths instead of lists.
  data Passes {v₁ v₂ : V} (edge : v₁ ⟶ v₂) : ∀{a b : V} → Walk a b → Type{ℓ₁ Lvl.⊔ ℓ₂} where
    current : ∀{c}{rest : Walk v₂ c} → Passes edge (Walk.prepend edge rest)
    skip    : ∀{b c}{rest : Walk b c} → Passes edge rest → ∀{a}{e : (a ⟶ b)} → Passes edge (Walk.prepend e rest)

  -- `Visits v walk` states that the walk `walk` visits the vertex `v`.
  -- In other words, one of the steps/edges in the walk mention the vertex v.
  data Visits (v : V) : ∀{a b : V} → Walk a b → Type{ℓ₁ Lvl.⊔ ℓ₂} where
    current : ∀{b}{path : Walk v b} → Visits v path
    skip    : ∀{a b c}{e : (a ⟶ b)}{rest : Walk b c} → Visits v rest → Visits v (Walk.prepend e rest)

  module _ {a b : V} (walk₁ : Walk a b) {c d : V} (walk₂ : Walk c d) where
    record Subwalk : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{v₁ v₂ : V}{edge : v₁ ⟶ v₂} → Passes edge walk₁ → Passes edge walk₂

  module _ {a b : V} (walk : Walk a b) where
    -- A walk that never visits the same edge twice.
    -- Note: Equality on edges must respect uniqueness. In other words, one edge must not have multiple constructions.
    record Trail : Type{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{v₁ v₂ : V}{edge : v₁ ⟶ v₂} → IsProp(Passes edge walk)

    -- A walk that never visits the same vertex twice.
    -- Also called "Simple path".
    -- Note: Equality on edges must respect uniqueness. In other words, one edge must not have multiple constructions.
    record Path : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{v : V} → IsProp(Visits v walk)
    path = inst-fn Path.proof

    -- A walk that visits every vertex in the graph.
    record Traceable : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{v : V} → Visits v walk
    traceable = inst-fn Traceable.proof

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : Graph{ℓ₁}{ℓ₂}(V)) where
  -- A complete graph have an edge for each pair of vertices from V. TODO: Exclude loops
  record Complete : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x y : V} → (x ⟶ y)
  complete = inst-fn Complete.proof

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : Graph{ℓ₁}{ℓ₂}(V)) where
  -- A connected graph have walks from every vertex to any vertex.
  -- For undirected graphs, this can be visually interpreted as disconnected islands of vertices.
  -- Note: Equality on edges must respect uniqueness. In other words, one edge must not have multiple constructions.
  Connected = Complete(Walk(_⟶_))
  connected = complete(Walk(_⟶_))

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : Graph{ℓ₁}{ℓ₂}(V)) where
  record IsTree : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x y : V} → ∃!(Path(_⟶_) {x}{y})
  isTree = inst-fn IsTree.proof

  record IsForest : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x y : V} → Unique(Path(_⟶_) {x}{y})
  isForest = inst-fn IsForest.proof

  record Linear : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      unique-start-vertex : ∀{y} → ∃!(x ↦ (x ⟶ y))
      unique-end-vertex   : ∀{x} → ∃!(y ↦ (x ⟶ y))

  module _ (v : V) where
    record InitialVertex : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{x} → ¬(x ⟶ v)
    initialVertex = inst-fn InitialVertex.proof

    record FinalVertex : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{x} → ¬(v ⟶ x)
    finalVertex = inst-fn FinalVertex.proof

  record IsOutwardRootedTree : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      ⦃ tree ⦄ : IsTree
      unique-initial-vertex : ∃!(InitialVertex)

  record IsInwardRootedTree : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      ⦃ tree ⦄ : IsTree
      unique-initial-vertex : ∃!(FinalVertex)

  record IsList : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      ⦃ linear ⦄ : Linear
      unique-initial-vertex : ∃!(InitialVertex)
      unique-final-vertex   : ∃!(FinalVertex)

  record IsCycle : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      ⦃ linear ⦄ : Linear
      no-initial-vertex : ∀{v} → ¬(InitialVertex v)
      no-final-vertex   : ∀{v} → ¬(FinalVertex v)

module Proofs {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : Graph{ℓ₁}{ℓ₂}(V)) where
  instance
    undirect-undirected : Undirected(undirect(_⟶_))
    Undirected.reversable         undirect-undirected = intro [∨]-symmetry
    Undirected.reverse-involution undirect-undirected = intro swap-involution

  module _ where
    open WalkFunctions(_⟶_)

    at-path-length : ∀{a} → length(at{x = a}) ≡ 0
    at-path-length = reflexivity(_≡_)

    edge-path-length : ∀{a b}{e : a ⟶ b} → length(edge e) ≡ 1
    edge-path-length = reflexivity(_≡_)

    join-path-length : ∀{a b c}{e₁}{e₂} → length(join {a}{b}{c} e₁ e₂) ≡ 2
    join-path-length = reflexivity(_≡_)

    prepend-path-length : ∀{a b c}{e : a ⟶ b}{w : Walk(_⟶_) b c} → length(prepend e w) ≡ 𝐒(length w)
    prepend-path-length {w = at}          = reflexivity(_≡_)
    prepend-path-length {w = prepend e w} = [≡]-with(𝐒) (prepend-path-length{e = e}{w = w})

    [++]-identityᵣ : ∀{a b}{w : Walk(_⟶_) a b} → (w ++ at ≡ w)
    [++]-identityᵣ {w = at}          = reflexivity(_≡_)
    [++]-identityᵣ {w = prepend x w} = [≡]-with(prepend x) ([++]-identityᵣ {w = w})
    {-# REWRITE [++]-identityᵣ #-}

    [++]-path-length : ∀{a b c}{w₁ : Walk(_⟶_) a b}{w₂ : Walk(_⟶_) b c} → length(w₁ ++ w₂) ≡ length w₁ + length w₂
    [++]-path-length {a} {.a} {.a} {at}            {at}          = reflexivity(_≡_)
    [++]-path-length {a} {.a} {c}  {at}            {prepend e w} = prepend-path-length {e = e}{w = w}
    [++]-path-length {a} {b}  {c}  {prepend e₁ w₁} {w₂}          = [≡]-with(𝐒) ([++]-path-length {w₁ = w₁}{w₂ = w₂})

    at-visits : ∀{v} → Visits(_⟶_) v (at{x = v})
    at-visits = current

    edge-visits-left : ∀{a b}{e : a ⟶ b} → Visits(_⟶_) a (edge e)
    edge-visits-left = current

    edge-visits-right : ∀{a b}{e : a ⟶ b} → Visits(_⟶_) b (edge e)
    edge-visits-right = skip current

    join-visits-1 : ∀{a b c}{e₁ : a ⟶ b}{e₂ : b ⟶ c} → Visits(_⟶_) a (join e₁ e₂)
    join-visits-1 = current

    join-visits-2 : ∀{a b c}{e₁ : a ⟶ b}{e₂ : b ⟶ c} → Visits(_⟶_) b (join e₁ e₂)
    join-visits-2 = skip current

    join-visits-3 : ∀{a b c}{e₁ : a ⟶ b}{e₂ : b ⟶ c} → Visits(_⟶_) c (join e₁ e₂)
    join-visits-3 = skip (skip current)

    prepend-visitsᵣ-left : ∀{a b c}{e : a ⟶ b}{w : Walk(_⟶_) b c} → Visits(_⟶_) a (prepend e w)
    prepend-visitsᵣ-left = current

    prepend-visitsᵣ-right : ∀{v b c}{w : Walk(_⟶_) b c} → Visits(_⟶_) v w → ∀{a}{e : a ⟶ b} → Visits(_⟶_) v (prepend e w)
    prepend-visitsᵣ-right p = skip p

    prepend-visitsₗ : ∀{v a b c}{e : a ⟶ b}{w : Walk(_⟶_) b c} → Visits(_⟶_) v (prepend e w) → ((v ≡ a) ∨ Visits(_⟶_) v w)
    prepend-visitsₗ current  = [∨]-introₗ(reflexivity(_≡_))
    prepend-visitsₗ (skip p) = [∨]-introᵣ p

    [++]-visitsᵣ : ∀{v a b c}{w₁ : Walk(_⟶_) a b}{w₂ : Walk(_⟶_) b c} → (Visits(_⟶_) v w₁) ∨ (Visits(_⟶_) v w₂) → Visits(_⟶_) v (w₁ ++ w₂)
    [++]-visitsᵣ ([∨]-introₗ current) = current
    [++]-visitsᵣ {w₂ = w₂} ([∨]-introₗ (skip {rest = rest} p)) = skip ([++]-visitsᵣ {w₁ = rest}{w₂ = w₂} ([∨]-introₗ p))
    [++]-visitsᵣ {w₁ = at} ([∨]-introᵣ p) = p
    [++]-visitsᵣ {w₁ = prepend x w₁} {w₂ = w₂} ([∨]-introᵣ p) = skip ([++]-visitsᵣ {w₁ = w₁}{w₂ = w₂} ([∨]-introᵣ p))

    [++]-visitsₗ : ∀{v a b c}{w₁ : Walk(_⟶_) a b}{w₂ : Walk(_⟶_) b c} → (Visits(_⟶_) v w₁) ∨ (Visits(_⟶_) v w₂) ← Visits(_⟶_) v (w₁ ++ w₂)
    [++]-visitsₗ {v} {a} {.a} {.a} {at}           {at}            p = [∨]-introₗ p
    [++]-visitsₗ {v} {a} {.a} {c}  {at}           {prepend x w₂}  p = [∨]-introᵣ p
    [++]-visitsₗ {v} {a} {b}  {c}  {prepend e w₁} {w₂}            p with prepend-visitsₗ p
    [++]-visitsₗ {v} {a} {b}  {c}  {prepend e w₁} {w₂}            p | [∨]-introₗ eq = [∨]-introₗ ([≡]-substitutionₗ eq (Visits.current {path = prepend e w₁}))
    [++]-visitsₗ {v} {a} {b}  {c}  {prepend e w₁} {w₂}            _ | [∨]-introᵣ p  = Either.mapLeft skip ([++]-visitsₗ {w₁ = w₁} {w₂ = w₂} p)

    -- [++]-visits : ∀{ae be a₁ b₁ a₂ b₂}{e : ae ⟶ be}{w₁ : Walk(_⟶_) a₁ b₁}{w₂ : Walk(_⟶_) a₂ b₂} → (Visits(_⟶_) e w₁) ∨ (Visits(_⟶_) e w₂) → Visits(_⟶_) e (w₁ ++ w₂)

    complete-singular-is-undirected : ⦃ Complete(_⟶_) ⦄ → ⦃ Singular(_⟶_) ⦄ → Undirected(_⟶_)
    Undirected.reversable         complete-singular-is-undirected = intro(const(complete(_⟶_)))
    Undirected.reverse-involution complete-singular-is-undirected = intro(singular(_⟶_))

    -- traceable-is-connected : ⦃ Traceable(_⟶_) ⦄ → Connected(_⟶_)
