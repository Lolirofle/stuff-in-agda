open import Type

module Graph.Walk.Proofs {ℓ₁ ℓ₂} {V : Type{ℓ₁}} where

open import Lang.Instance
open import Logic
import      Lvl
open import Graph{ℓ₁}{ℓ₂}(V)
open import Graph.Walk{ℓ₁}{ℓ₂}{V}
open import Relator.Equals.Proofs.Equivalence
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Type.Unit

private variable ℓ : Lvl.Level
private variable _⟶_ : Graph
private variable a b : V
private variable _▫_ : V → V → Type{ℓ}

-- There is a walk between two vertices when there is one edge between them.
instance
  Walk-super : (_⟶_) ⊆₂ (Walk(_⟶_))
  _⊆₂_.proof Walk-super p = prepend p at

-- Walk is a "smallest" reflexive-transitive closure
Walk-sub : ⦃ _ : Reflexivity(_▫_) ⦄ → ⦃ _ : Transitivity(_▫_) ⦄ → ⦃ _ : (_⟶_) ⊆₂ (_▫_) ⦄ → (Walk(_⟶_)) ⊆₂ (_▫_)
Walk-sub {_▫_ = _▫_}{_⟶_ = _⟶_} = intro proof where
  proof : Names.Subrelation(Walk(_⟶_))(_▫_)
  proof at                    = transitivity(_▫_) (reflexivity(_▫_)) (reflexivity(_▫_))
  proof (prepend ab1 walkb1b) = transitivity(_▫_) (sub₂(_⟶_)(_▫_) ab1) (proof walkb1b)

instance
  -- A walk can be joined/concatenated to form a new walk.
  Walk-transitivity : Transitivity(Walk(_⟶_))
  Transitivity.proof Walk-transitivity = proof where
    proof : Names.Transitivity(Walk(_⟶_))
    proof at             xz = xz
    proof (prepend xb by) yz = prepend xb (proof by yz)

instance
  Walk-reflexivity : Reflexivity(Walk(_⟶_))
  Walk-reflexivity = intro at
