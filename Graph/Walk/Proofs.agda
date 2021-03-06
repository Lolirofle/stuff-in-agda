open import Type

module Graph.Walk.Proofs {ℓ₁ ℓ₂} {V : Type{ℓ₁}} where

open import Lang.Instance
open import Logic
import      Lvl
open import Graph{ℓ₁}{ℓ₂}(V)
open import Graph.Walk{ℓ₁}{ℓ₂}{V}
open import Relator.Equals.Proofs.Equiv
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Type.Properties.Singleton

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

Walk-transitivity-raw : Names.Transitivity(Walk(_⟶_))
Walk-transitivity-raw at              xz = xz
Walk-transitivity-raw (prepend xb by) yz = prepend xb (Walk-transitivity-raw by yz)

instance
  -- A walk can be joined/concatenated to form a new walk.
  Walk-transitivity : Transitivity(Walk(_⟶_))
  Transitivity.proof Walk-transitivity = Walk-transitivity-raw

instance
  Walk-reflexivity : Reflexivity(Walk(_⟶_))
  Walk-reflexivity = intro at
