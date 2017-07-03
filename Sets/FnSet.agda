module Sets.FnSet {ℓ₁} where

import      Level as Lvl
import      List
open import Boolean
import      Boolean.Operators
open        Boolean.Operators.Programming
open import Boolean.Theorems
open import Logic.Propositional
open import Functional
open import Operator.Equals
open import Relator.Equals{ℓ₁}{Lvl.𝟎}
open import Type

record FnSet{ℓ₂}(T : Type{ℓ₂}) : Type{ℓ₂} where
  field
    inclusion-fn : T → Bool

module _ {ℓ₂}{T : Type{ℓ₂}} where

  Universe : FnSet(T)
  Universe = record{inclusion-fn = const(𝑇)}

  ∅ : FnSet(T)
  ∅ = record{inclusion-fn = const(𝐹)}

  singleton : {{_ : Equals(T)}} → T → FnSet(T)
  singleton(t) = record{inclusion-fn = (x ↦ x == t)}

  enumeration : {{_ : Equals(T)}} → List.List(T) → FnSet(T)
  enumeration(l) = record{inclusion-fn = (x ↦ (List.any(t ↦ x == t)(l)))}

  _∈_ : T → FnSet(T) → Stmt
  _∈_ a set = ((FnSet.inclusion-fn set a) ≡ 𝑇)

  _∉_ : T → FnSet(T) → Stmt
  _∉_ a set = (!(FnSet.inclusion-fn set a) ≡ 𝑇)

  _⊆_ : FnSet(T) → FnSet(T) → Stmt
  _⊆_ set₁ set₂ = (∀{a} → (a ∈ set₁) → (a ∈ set₂))

  _⊇_ : FnSet(T) → FnSet(T) → Stmt
  _⊇_ set₁ set₂ = _⊆_ set₂ set₁

  _∪_ : FnSet(T) → FnSet(T) → FnSet(T)
  _∪_ A B =
    record{
      inclusion-fn = (elem ↦ FnSet.inclusion-fn(A)(elem) || FnSet.inclusion-fn(B)(elem))
    }

  _∩_ : FnSet(T) → FnSet(T) → FnSet(T)
  _∩_ A B =
    record{
      inclusion-fn = (elem ↦ FnSet.inclusion-fn(A)(elem) && FnSet.inclusion-fn(B)(elem))
    }

  _∖_ : FnSet(T) → FnSet(T) → FnSet(T)
  _∖_ A B =
    record{
      inclusion-fn = (elem ↦ FnSet.inclusion-fn(A)(elem) && ! FnSet.inclusion-fn(B)(elem))
    }

  ∁_ : FnSet(T) → FnSet(T)
  ∁_ A =
    record{
      inclusion-fn = (elem ↦ ! FnSet.inclusion-fn(A)(elem))
    }
