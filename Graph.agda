module Graph where

import      Level as Lvl
open import Data
open import Functional
open import List
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Sets.ListSet{Lvl.𝟎}

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

  data Path : List(V) → Set where
    Path𝟎 : Path(∅)
    Path𝐏 : ∀{v₁ v₂}{l} → HasEdge[ v₂ ⟵ v₁ ] → Path(v₂ ⊰ l) → Path(v₁ ⊰ v₂ ⊰ l)

  Connected : V → V → Set
  Connected(v₁)(v₂) = (∃{List(V)}(l ↦ Path((v₁ ⊰ l) ++ ([ v₂ ]))))

  Disconnected : V → V → Set
  Disconnected(v₁)(v₂) = ¬(Connected(v₁)(v₂))

  -- Constructions
  subgraph : ∀{V₂} → (V → V₂) → Graph(V₂)
  subgraph(f) = record{edges = map (\{(v₁ , v₂) → (f(v₁) , f(v₂))}) (edges)}

  -- Boolean testing
  -- with-edge
  -- without-edge
  -- has-edge
  -- is-connected
  -- is-disconnected
