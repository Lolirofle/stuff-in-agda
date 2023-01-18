open import Type

module Graph.Walk {ℓ₁ ℓ₂} {V : Type{ℓ₁}} where

import      Lvl
open import Graph{ℓ₁}{ℓ₂}(V)
import      Structure.Relator.Names as Names

module _ (_⟶_ : Graph) where
  -- A path is matching directed edges connected to each other in a finite sequence.
  -- This is essentially a list of edges where the ends match.
  -- The terminology is that a walk is a sequence of connected edges and it visits all its vertices.
  -- Note: Walk is a generalized "List" in the sense that it is a category compared to the usual List which is a monoid.
  -- Note: Walk is equivalent to the reflexive-transitive closure.
  data Walk : V → V → Type{ℓ₁ Lvl.⊔ ℓ₂} where
    at      : Names.Reflexivity(Walk)
    prepend : ∀{a b c} → (a ⟶ b) → (Walk b c) → (Walk a c)
