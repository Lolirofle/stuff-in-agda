open import Type

module Relator.ReflexiveTransitiveClosure.Proofs {ℓ₁ ℓ₂} {T : Type{ℓ₁}} {_▫_ : T → T → Type{ℓ₂}} where

open import Graph.Walk
open import Graph.Walk.Proofs
import      Lvl
open import Logic.Propositional
open import Relator.ReflexiveTransitiveClosure(_▫_)
open import Structure.Relator.Properties

instance
  ReflexiveTransitiveClosure-reflexivity : Reflexivity(ReflexiveTransitiveClosure)
  ReflexiveTransitiveClosure-reflexivity = intro refl

instance
  ReflexiveTransitiveClosure-transitivity : Transitivity(ReflexiveTransitiveClosure)
  ReflexiveTransitiveClosure-transitivity = intro trans

-- The "prepend"-property of reflexive-transitive closure
ReflexiveTransitiveClosure-prepend : ∀{a b c} → (a ▫ b) → ReflexiveTransitiveClosure b c → ReflexiveTransitiveClosure a c
ReflexiveTransitiveClosure-prepend ab bc = trans (super ab) bc

-- A reflexive-transitive closure is the same as a path.
ReflexiveTransitiveClosure-Walk-equivalence : ∀{a b} → (ReflexiveTransitiveClosure a b) ↔ (Walk(_▫_) a b)
ReflexiveTransitiveClosure-Walk-equivalence = [↔]-intro l r where
  r : ∀{a b} → ReflexiveTransitiveClosure a b → Walk(_▫_) a b
  r ReflexiveTransitiveClosure.refl              = reflexivity(Walk(_▫_))
  r (ReflexiveTransitiveClosure.super ab)        = sub₂(_▫_)(Walk(_▫_)) ab
  r (ReflexiveTransitiveClosure.trans rab1 rb1b) = transitivity(Walk(_▫_)) (r rab1) (r rb1b)

  l : ∀{a b} → Walk(_▫_) a b → ReflexiveTransitiveClosure a b
  l Walk.at        = ReflexiveTransitiveClosure.refl
  l (Walk.prepend ab1 sb1b) = ReflexiveTransitiveClosure-prepend ab1 (l sb1b)
