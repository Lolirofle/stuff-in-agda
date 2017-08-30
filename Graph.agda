module Graph where

import      Level as Lvl
open import Data
open import Functional
open import List
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Sets.ListSet{Lvl.𝟎}

record Edge ⦃ Self : Set ⦄ (V : Set) : Set where
  constructor edge
  field
    from : ⦃ _ : Self ⦄ → V
    to   : ⦃ _ : Self ⦄ → V

-- TupleEdge : Edge

record Graph (V : Set) : Set where
  constructor graph

  field
    edges : List(V ⨯ V)

  -- Propositions
  HasEdge[_⟶_] : V → V → Set
  HasEdge[_⟶_](v₁)(v₂) = ((v₁ , v₂) ∈ edges)

  HasEdge[_⟵_] : V → V → Set
  HasEdge[_⟵_](v₁)(v₂) = HasEdge[_⟶_](v₂)(v₁)

  HasEdge[_⟷_] : V → V → Set
  HasEdge[_⟷_](v₁)(v₂) = HasEdge[_⟵_](v₁)(v₂) ∧ HasEdge[_⟶_](v₁)(v₂)

  data Path : V → V → Set where
    PathIntro        : ∀{v₁ v₂    : V} → HasEdge[ v₁ ⟶ v₂ ] → Path(v₁)(v₂)
    PathTransitivity : ∀{v₁ v₂ v₃ : V} → Path(v₁)(v₂) → Path(v₂)(v₃) → Path(v₁)(v₃)

  Connected : V → V → Set
  Connected(v₁)(v₂) = Path(v₁)(v₂)

  Disconnected : V → V → Set
  Disconnected(v₁)(v₂) = ¬(Connected(v₁)(v₂))

  -- Constructions
  map_vertices : ∀{V₂} → (V → V₂) → Graph(V₂)
  map_vertices(f) = record{edges = map (\{(v₁ , v₂) → (f(v₁) , f(v₂))}) (edges)}

  -- Boolean testing
  -- with-edge
  -- without-edge
  -- has-edge
  -- is-connected
  -- is-disconnected
