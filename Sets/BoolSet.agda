module Sets.BoolSet where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Logic using (_⟶_ ; _⟵_ ; _⟷_)
open        Data.Boolean.Operators.Programming hiding (_==_)
open import Data.Boolean.Stmt
open import Data.List as List using (List)
import      Data.List.Functions as List
open import Data.Option as Option using (Option)
open import Logic
open import Functional
open import Operator.Equals
open import Structure.Setoid
open import Type
open import Type.Properties.Listable

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

-- A function from a type T to a boolean value.
-- This can be interpreted as a computable set over T (a set with a computable membership relation).
BoolSet : Type{ℓ} → Type{ℓ}
BoolSet(T) = (T → Bool)

-- Decidable relations
module _ where
  _∈?_ : T → BoolSet(T) → Bool
  _∈?_ = apply

  _∉?_ : T → BoolSet(T) → Bool
  _∉?_ a set = !(a ∈? set)

  module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ listable : Listable(T) ⦄ where
    isEmpty : BoolSet(T) → Bool
    isEmpty A = List.satisfiesAll(_∉? A) (enum(T))

    extract : BoolSet(T) → Option(T)
    extract A = List.find(_∈? A) (enum(T))

    _⊆?_ : BoolSet(T) → BoolSet(T) → Bool
    _⊆?_ A B = List.satisfiesAll(elem ↦ (elem ∈? A) ⟶ (elem ∈? B)) (enum(T))

    _⊇?_ : BoolSet(T) → BoolSet(T) → Bool
    _⊇?_ A B = List.satisfiesAll(elem ↦ (elem ∈? A) ⟵ (elem ∈? B)) (enum(T))

    _≡?_ : BoolSet(T) → BoolSet(T) → Bool
    _≡?_ A B = List.satisfiesAll(elem ↦ (elem ∈? A) ⟷ (elem ∈? B)) (enum(T))

-- Relations
module _ where
  _∈_ : T → BoolSet(T) → Stmt
  _∈_ a set = IsTrue(a ∈? set)

  _∉_ : T → BoolSet(T) → Stmt
  _∉_ a set = IsTrue(a ∉? set)

  _⊆_ : BoolSet(T) → BoolSet(T) → Stmt
  _⊆_ set₁ set₂ = (∀{a} → (a ∈ set₁) → (a ∈ set₂))

  _⊇_ : BoolSet(T) → BoolSet(T) → Stmt
  _⊇_ set₁ set₂ = _⊆_ set₂ set₁

-- Operations
module _ where
  𝐔 : BoolSet(T)
  𝐔 = const(𝑇)

  ∅ : BoolSet(T)
  ∅ = const(𝐹)

  module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ equiv-dec : EquivDecidable(T) ⦄ where
    singleton : T → BoolSet(T)
    singleton(t) = (_== t)

    enumeration : List(T) → BoolSet(T)
    enumeration(l) = (x ↦ List.satisfiesAny(_== x)(l))

  _∪_ : BoolSet(T) → BoolSet(T) → BoolSet(T)
  _∪_ A B = (elem ↦ (elem ∈? A) || (elem ∈? B))

  _∩_ : BoolSet(T) → BoolSet(T) → BoolSet(T)
  _∩_ A B = (elem ↦ (elem ∈? A) && (elem ∈? B))

  _∖_ : BoolSet(T) → BoolSet(T) → BoolSet(T)
  _∖_ A B = (elem ↦ (elem ∈? A) && !(elem ∈? B))

  ∁_ : BoolSet(T) → BoolSet(T)
  ∁_ A = (elem ↦ !(elem ∈? A))

  ℘_ : BoolSet(T) → BoolSet(BoolSet(T))
  ℘_ _ = const(𝑇)
