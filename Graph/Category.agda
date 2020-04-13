open import Type

module Graph.Category {ℓ₁ ℓ₂} {V : Type{ℓ₁}} where

open import Data.Tuple as Tuple using ()
open import Functional
open import Logic.Propositional
import      Lvl
open import Graph{ℓ₁}{ℓ₂}(V)
open import Graph.Walk{ℓ₁}{ℓ₂}{V}
open import Graph.Walk.Proofs{ℓ₁}{ℓ₂}{V}
open import Relator.Equals
open import Relator.Equals.Proofs
open import Relator.Equals.Proofs.Equivalence
open import Structure.Setoid
open import Structure.Category
import      Structure.Category.Names as Names
open import Structure.Category.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Transitivity

module _ (_⟶_ : Graph) where
  private variable a b c d : V
  private variable e e₁ e₂ e₃ : a ⟶ b
  private variable w w₁ w₂ w₃ : Walk(_⟶_) a b

  Walk-transitivity-raw-identityₗ-raw : (Walk-transitivity-raw at w ≡ w)
  Walk-transitivity-raw-identityₗ-raw = [≡]-intro

  Walk-transitivity-raw-identityᵣ-raw : (Walk-transitivity-raw w at ≡ w)
  Walk-transitivity-raw-identityᵣ-raw {a}{.a} {Walk.at}                  = [≡]-intro
  Walk-transitivity-raw-identityᵣ-raw {a}{c}  {Walk.prepend {b = b} e w} = congruence₁(prepend e) (Walk-transitivity-raw-identityᵣ-raw {b}{c} {w})

  Walk-transitivity-raw-associativity-raw : Names.Morphism.Associativity{Obj = V}(\{w} → Walk-transitivity-raw{_⟶_ = _⟶_}{z = w})
  Walk-transitivity-raw-associativity-raw {a}{b}{c}{d}  {Walk.at}          {w₂}{w₃} = [≡]-intro
  Walk-transitivity-raw-associativity-raw {a}{b}{c}{d}  {Walk.prepend e w₁}{w₂}{w₃} = congruence₁(prepend e) (Walk-transitivity-raw-associativity-raw {a}{b}{c}{_} {w₁}{w₂}{w₃})

  instance
    Walk-transitivity-raw-identityₗ : Morphism.Identityₗ{Obj = V}(\{w} → Walk-transitivity-raw{z = w})(at)
    Walk-transitivity-raw-identityₗ = Morphism.intro Walk-transitivity-raw-identityₗ-raw

  instance
    Walk-transitivity-raw-identityᵣ : Morphism.Identityᵣ{Obj = V}(\{w} → Walk-transitivity-raw{z = w})(at)
    Walk-transitivity-raw-identityᵣ = Morphism.intro Walk-transitivity-raw-identityᵣ-raw

  instance
    Walk-transitivity-raw-identity : Morphism.Identity{Obj = V}(\{w} → Walk-transitivity-raw{_⟶_ = _⟶_}{z = w})(at)
    Walk-transitivity-raw-identity = [∧]-intro Walk-transitivity-raw-identityₗ Walk-transitivity-raw-identityᵣ

  -- The category arising from a graph by its vertices and walks.
  -- Note that `Walk` is defined so that every sequence of edges have an unique walk. For example `ReflexitiveTransitiveClosure` (a relation equivalent to a walk) would not work.
  free-category : Category(Walk(_⟶_))
  Category._∘_ free-category = swap(transitivity(Walk(_⟶_)))
  Category.id  free-category = reflexivity(Walk(_⟶_))
  BinaryOperator.congruence (Category.binaryOperator free-category) [≡]-intro [≡]-intro = [≡]-intro
  Morphism.Associativity.proof (Category.associativity free-category) {a}{b}{c}{d} {w₁}{w₂}{w₃} = symmetry(_≡_) (Walk-transitivity-raw-associativity-raw {d}{c}{b}{a} {w₃}{w₂}{w₁})
  Morphism.Identityₗ.proof (Tuple.left  (Category.identity free-category)) = Walk-transitivity-raw-identityᵣ-raw
  Morphism.Identityᵣ.proof (Tuple.right (Category.identity free-category)) = Walk-transitivity-raw-identityₗ-raw
