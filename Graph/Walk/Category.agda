open import Type

module Graph.Walk.Category {ℓ₁ ℓ₂} {V : Type{ℓ₁}} where

import      Data.Tuple as Tuple
open import Functional
open import Logic.Propositional
import      Lvl
open import Graph{ℓ₁}{ℓ₂}(V)
open import Graph.Walk{ℓ₁}{ℓ₂}{V}
open import Graph.Walk.Functions
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Category
import      Structure.Categorical.Names as Names
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Relator.Properties

module _ {_⟶_ : Graph} where
  private variable a b c d : V
  private variable e e₁ e₂ e₃ : a ⟶ b
  private variable w w₁ w₂ w₃ : Walk(_⟶_) a b

  instance
    [++]-at-identityₗ : Morphism.Identityₗ{Obj = V}(\{a} → _++_ {_⟶_ = _⟶_} {c = a})(at)
    [++]-at-identityₗ = Morphism.intro(reflexivity(_≡_))

  instance
    [++]-at-identityᵣ : Morphism.Identityᵣ{Obj = V}(\{a} → _++_ {_⟶_ = _⟶_} {c = a})(at)
    [++]-at-identityᵣ = Morphism.intro proof where
      proof : Names.Morphism.Identityᵣ{Obj = V}(\{a} → _++_ {c = a})(at)
      proof {a}{.a} {Walk.at}                  = reflexivity(_≡_)
      proof {a}{c}  {Walk.prepend {b = b} e w} = congruence₁(prepend e) (proof{a}{b} {w})

  instance
    [++]-at-identity : Morphism.Identity{Obj = V}(\{a} → _++_ {_⟶_ = _⟶_} {c = a})(at)
    [++]-at-identity = [∧]-intro [++]-at-identityₗ [++]-at-identityᵣ

  instance
    [++]-associativity : Morphism.Associativity{Obj = V}(\{a} → _++_ {_⟶_ = _⟶_} {c = a})
    [++]-associativity = Morphism.intro(\{a}{b}{c}{d}{w₁}{w₂}{w₃} → proof{a}{b}{c}{d}{w₁}{w₂}{w₃}) where
      proof : Names.Morphism.Associativity{Obj = V}(\{a} → _++_ {_⟶_ = _⟶_} {c = a})
      proof {a}{b}{c}{d}  {Walk.at}          {w₂}{w₃} = reflexivity(_≡_)
      proof {a}{b}{c}{d}  {Walk.prepend e w₁}{w₂}{w₃} = congruence₁(prepend e) (proof {a}{b}{c}{_} {w₁}{w₂}{w₃})

  -- The category arising from a graph by its vertices and walks.
  -- Note that `Walk` is defined so that every sequence of edges have an unique walk. For example `ReflexitiveTransitiveClosure` (a relation equivalent to a walk) would not work.
  -- Walk is the free category in the same sense that List is the free monoid.
  -- Also called: Free category.
  graphWalkCategory : Category(Walk(_⟶_))
  Category._∘_                   graphWalkCategory  = swap(_++_)
  Category.id                    graphWalkCategory  = at
  Category.associativity         graphWalkCategory  = Morphism.intro \{a}{b}{c}{d} {w₁}{w₂}{w₃} → symmetry(_≡_) (Morphism.associativity(_++_) {d}{c}{b}{a} {w₃}{w₂}{w₁})
  Tuple.left (Category.identity  graphWalkCategory) = Morphism.intro(Morphism.identityᵣ(_++_)(at))
  Tuple.right (Category.identity graphWalkCategory) = Morphism.intro(Morphism.identityₗ(_++_)(at))
