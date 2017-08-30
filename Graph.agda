module Graph where

import      Level as Lvl
open import Logic.Propositional{Lvl.𝟎}

record Graph (V : Set) : Set where
  field
    edges : List(V ⨯ V)

  HasEdge[_ ⟶ _] : V → V → Set
  HasEdge[_ ⟶ _](v₁)(v₂) = ((v₁ , v₂) ∈ edges)

  HasEdge[_ ⟵ _] : V → V → Set
  HasEdge[_ ⟵ _](v₁)(v₂) = HasEdge[_ ⟶ _](v₂)(v₁)

  HasEdge[_ ⟷ _] : V → V → Set
  HasEdge[_ ⟷ _](v₁)(v₂) = HasEdge[_ ⟵ _](v₁)(v₂) ∧ HasEdge[_ ⟶ _](v₁)(v₂)
