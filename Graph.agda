module Graph where

import      Lvl
open import Data
open import Functional
open import List
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Relator.Equals{Lvl.𝟎}
open import Sets.ListSet{Lvl.𝟎}

record EdgeClass (V : Set) (Self : Set) : Set where
  constructor edgeInstance
  field
    from           : Self → V
    to             : Self → V
    _withVertices_ : Self → (V ⨯ V) → Self

module Edge where
  open EdgeClass ⦃ ... ⦄ public

instance
  EdgeInstance-Tuple : ∀{V} → EdgeClass(V)(V ⨯ V)
  Edge.from          ⦃ EdgeInstance-Tuple ⦄ (v₁ , v₂) = v₁
  Edge.to            ⦃ EdgeInstance-Tuple ⦄ (v₁ , v₂) = v₂
  Edge._withVertices_ ⦃ EdgeInstance-Tuple ⦄ (v₁ , v₂) (w₁ , w₂) = (w₁ , w₂)

record Graph (V : Set) (E : Set) ⦃ _ : EdgeClass(V)(E) ⦄ : Set where
  constructor graph

  field
    edges : List(E)

  -- Propositions
  HasEdge[_⟶_] : V → V → Set
  HasEdge[_⟶_](v₁)(v₂) = ∃(edge ↦ (edge ∈ edges)∧(Edge.from(edge) ≡ v₁)∧(Edge.to(edge) ≡ v₂))

  HasEdge[_⟵_] : V → V → Set
  HasEdge[_⟵_](v₁)(v₂) = HasEdge[_⟶_](v₂)(v₁)

  HasEdge[_⟷_] : V → V → Set
  HasEdge[_⟷_](v₁)(v₂) = HasEdge[_⟵_](v₁)(v₂) ∧ HasEdge[_⟶_](v₁)(v₂)

  data Path : V → V → Set where
    PathIntro        : ∀{v₁ v₂ : V} → HasEdge[ v₁ ⟶ v₂ ] → Path(v₁)(v₂)
    PathTransitivity : ∀{v₁ v₂ v₃ : V} → Path(v₁)(v₂) → Path(v₂)(v₃) → Path(v₁)(v₃)

  Connected : V → V → Set
  Connected(v₁)(v₂) = Path(v₁)(v₂)

  Disconnected : V → V → Set
  Disconnected(v₁)(v₂) = ¬(Connected(v₁)(v₂))

  -- Constructions
  mapVertices : ∀{V₂} → ⦃ _ : EdgeClass(V₂)(E) ⦄ → (V → V₂) → Graph(V₂)(E)
  mapVertices(f) = record{edges = map(edge ↦ (edge Edge.withVertices(f(Edge.from(edge)) , f(Edge.to(edge))))) (edges)}

  -- Boolean testing
  -- with-edge
  -- without-edge
  -- has-edge
  -- is-connected
  -- is-disconnected
