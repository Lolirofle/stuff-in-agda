open import Type

module Graph.Walk.Proofs where

import      Lvl
open import Graph
open import Graph.Walk
open import Graph.Walk.Functions
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties

private variable ℓ : Lvl.Level
private variable V A B : Type{ℓ}
private variable _⟶_ _⟶₁_ _⟶₂_ : Graph(V)
private variable a b : V
private variable _▫_ : V → V → Type{ℓ}
private variable f : A → B

-- There is a walk between two vertices when there is one edge between them.
instance
  Walk-super : (_⟶_) ⊆₂ (Walk(_⟶_))
  Walk-super = intro edge

-- Walk is a "smallest" reflexive-transitive closure
Walk-sub : ⦃ _ : Reflexivity(_▫_) ⦄ → ⦃ _ : Transitivity(_▫_) ⦄ → ⦃ _ : (_⟶_) ⊆₂ (_▫_) ⦄ → (Walk(_⟶_)) ⊆₂ (_▫_)
Walk-sub {_▫_ = _▫_}{_⟶_ = _⟶_} = intro proof where
  proof : Names.Sub₂(Walk(_⟶_))(_▫_)
  proof at                    = transitivity(_▫_) (reflexivity(_▫_)) (reflexivity(_▫_))
  proof (prepend ab1 walkb1b) = transitivity(_▫_) (sub₂(_⟶_)(_▫_) ab1) (proof walkb1b)

instance
  -- A walk can be joined/concatenated to form a new walk.
  Walk-transitivity : Transitivity(Walk(_⟶_))
  Walk-transitivity = intro(_++_)

instance
  Walk-subtransitivityₗ : Subtransitivityₗ(Walk(_⟶_))(_⟶_)
  Walk-subtransitivityₗ = intro prepend

instance
  Walk-reflexivity : Reflexivity(Walk(_⟶_))
  Walk-reflexivity = intro at

Walk-map : (∀{a b} → (a ⟶₁ b) → (f(a) ⟶₂ f(b))) → (∀{a b} → Walk(_⟶₁_) a b → Walk(_⟶₂_) (f(a)) (f(b)))
Walk-map F at = at
Walk-map F (prepend x w) = prepend (F(x)) (Walk-map F w)
