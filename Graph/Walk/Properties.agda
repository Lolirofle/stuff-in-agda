open import Type

module Graph.Walk.Properties {ℓ₁ ℓ₂} {V : Type{ℓ₁}} where

open import Functional.Instance
open import Logic
import      Lvl
open import Graph{ℓ₁}{ℓ₂}(V)
open import Graph.Walk{ℓ₁}{ℓ₂}{V}
open import Relator.Equals.Proofs.Equiv
open import Type.Properties.MereProposition

module _ (_⟶_ : Graph) where
  -- `Passes edge walk` states that the walk `walk` contains the edge `edge`.
  -- In other words, there is a step in the walk which is `edge`.
  -- Note: Passes is a generalized containment relation for paths instead of lists.
  data Passes {v₁ v₂ : V} (edge : v₁ ⟶ v₂) : ∀{a b : V} → Walk(_⟶_) a b → Type{ℓ₁ Lvl.⊔ ℓ₂} where
    current : ∀{c}{rest : Walk(_⟶_) v₂ c} → Passes edge (Walk.prepend edge rest)
    skip    : ∀{b c}{rest : Walk(_⟶_) b c} → Passes edge rest → ∀{a}{e : (a ⟶ b)} → Passes edge (Walk.prepend e rest)

  -- `Visits v walk` states that the walk `walk` visits the vertex `v`.
  -- In other words, one of the steps/edges in the walk mention the vertex v.
  data Visits (v : V) : ∀{a b : V} → Walk(_⟶_) a b → Type{ℓ₁ Lvl.⊔ ℓ₂} where
    current : ∀{b}{path : Walk(_⟶_) v b} → Visits v path
    skip    : ∀{a b c}{e : (a ⟶ b)}{rest : Walk(_⟶_) b c} → Visits v rest → Visits v (Walk.prepend e rest)

  module _ {a b : V} (walk₁ : Walk(_⟶_) a b) {c d : V} (walk₂ : Walk(_⟶_) c d) where
    record Subwalk : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{v₁ v₂ : V}{edge : v₁ ⟶ v₂} → Passes edge walk₁ → Passes edge walk₂

module _ {_⟶_ : Graph} {a b : V} (walk : Walk(_⟶_) a b) where
  -- A walk that never visits the same edge twice.
  -- Note: Equality on edges must respect uniqueness. In other words, one edge must not have multiple constructions.
  record Trail : Type{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{v₁ v₂ : V}{edge : v₁ ⟶ v₂} → MereProposition(Passes(_⟶_) edge walk)

  -- A walk that never visits the same vertex twice.
  -- Also called "Simple path".
  -- Note: Equality on edges must respect uniqueness. In other words, one edge must not have multiple constructions.
  record Path : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{v : V} → MereProposition(Visits(_⟶_) v walk)
  path = inferArg Path.proof

  -- A walk that visits every vertex in the graph.
  record Traceable : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{v : V} → Visits(_⟶_) v walk
  traceable = inferArg Traceable.proof
