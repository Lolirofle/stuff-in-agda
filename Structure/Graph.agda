module Structure.Graph where

open import Lang.Instance
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Function
open import Type

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} ⦃ _ : Equiv(V) ⦄ where
  -- A graph is represented by a binary relation which states whether there is an edge from one vertex to another.
  -- This is by default (without any assumptions) a directed graph.
  Graph : (V → V → Type{ℓ₂}) → Type
  Graph(_⟶_) = BinaryRelator(_⟶_)

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : V → V → Type{ℓ₂}) where
  -- Two vertices are adjacent when there is an edge from the first one to the second one.
  Adjacent = _⟶_

  -- A path is matching directed edges connected to each other in a finite sequence.
  data Path : V → V → Type{ℓ₁ Lvl.⊔ ℓ₂} where
    start   : Names.Reflexivity(Path)
    prepend : ∀{a b c} → (a ⟶ b) → (Path b c) → (Path a c)

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : V → V → Type{ℓ₂}) where
  Undirected = Symmetry(_⟶_)
  undirected = symmetry(_⟶_)

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : V → V → Type{ℓ₂}) where
  record Complete : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x y : V} → (x ⟶ y)
  complete = inst-fn Complete.proof

module _ {ℓ₁ ℓ₂} {V : Type{ℓ₁}} (_⟶_ : V → V → Type{ℓ₂}) where
  Connected = Complete(Path(_⟶_))
  connected = complete(Path(_⟶_))
