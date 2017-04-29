module FnSet where

import      List
import      Level as Lvl
open import Boolean
open        Boolean.Operators
open import BooleanTheorems
open import Functional
open import Operator.Equals
open import Relator.Equals(Lvl.𝟎)
open import Type

record FnSet {lvl : Lvl.Level} (T : TypeN(lvl)) : TypeN(lvl) where
  field
    inclusion-fn : T → Bool

Universe : ∀{lvl}{T} → FnSet{lvl}(T)
Universe = record{inclusion-fn = const(𝑇)}

∅ : ∀{lvl}{T} → FnSet{lvl}(T)
∅ = record{inclusion-fn = const(𝐹)}

singleton : ∀{lvl}{T} → {{_ : Eq(T)}} → T → FnSet{lvl}(T)
singleton(t) = record{inclusion-fn = (x ↦ x == t)}

enumeration : ∀{lvl}{T} → {{_ : Eq(T)}} → List.List(T) → FnSet{lvl}(T)
enumeration(l) = record{inclusion-fn = (x ↦ (List.any(t ↦ x == t)(l)))}

_∈_ : ∀{lvl}{T} → T → FnSet{lvl}(T) → Type
_∈_ a set = ((FnSet.inclusion-fn set a) ≡ 𝑇)

_∉_ : ∀{lvl}{T} → T → FnSet{lvl}(T) → Type
_∉_ a set = (¬ (FnSet.inclusion-fn set a) ≡ 𝑇)

_⊆_ : ∀{lvl}{T} → FnSet{lvl}(T) → FnSet{lvl}(T) → TypeN(lvl)
_⊆_ set₁ set₂ = (∀{a} → (a ∈ set₁) → (a ∈ set₂))

_⊇_ : ∀{lvl}{T} → FnSet{lvl}(T) → FnSet{lvl}(T) → TypeN(lvl)
_⊇_ set₁ set₂ = _⊆_ set₂ set₁

_∪_ : ∀{lvl}{T} → FnSet{lvl}(T) → FnSet{lvl}(T) → FnSet{lvl}(T)
_∪_ A B =
  record{
    inclusion-fn = (elem ↦ FnSet.inclusion-fn(A)(elem) ∨ FnSet.inclusion-fn(B)(elem))
  }

_∩_ : ∀{lvl}{T} → FnSet{lvl}(T) → FnSet{lvl}(T) → FnSet{lvl}(T)
_∩_ A B =
  record{
    inclusion-fn = (elem ↦ FnSet.inclusion-fn(A)(elem) ∧ FnSet.inclusion-fn(B)(elem))
  }

_∖_ : ∀{lvl}{T} → FnSet{lvl}(T) → FnSet{lvl}(T) → FnSet{lvl}(T)
_∖_ A B =
  record{
    inclusion-fn = (elem ↦ FnSet.inclusion-fn(A)(elem) ∧ ¬ FnSet.inclusion-fn(B)(elem))
  }

∁_ : ∀{lvl}{T} → FnSet{lvl}(T) → FnSet{lvl}(T)
∁_ A =
  record{
    inclusion-fn = (elem ↦ ¬ FnSet.inclusion-fn(A)(elem))
  }
