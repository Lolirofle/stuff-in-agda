import      Lvl
open import Type

module Type.Singleton.Proofs {ℓ : Lvl.Level} {X : Type{ℓ}} where

open import Functional
open import Function.Domains
open import Logic.Predicate
open import Relator.Equals
open import Relator.Equals.Proofs
open import Type.Properties.Empty
open import Type.Singleton
open import Type.Properties.Singleton
open import Structure.Type.Identity

instance
  -- There is always a construction of a singleton type
  Singleton-existence : ∀{x : X} → Singleton(x)
  Singleton-existence {x} = [∃]-intro(x) ⦃ [≡]-intro ⦄

instance
  -- There is an unique construction of a singleton type
  Singleton-is-unit : ∀{x : X} → IsUnit(Singleton(x))
  Singleton-is-unit {x} = intro (Singleton-existence{x}) (g{x}) where
    A : ∀{y x : X} → (y ≡ x) → Type{ℓ}
    A {y}{x} (xy-proof) = ([∃]-intro y ⦃ xy-proof ⦄ ≡ Singleton-existence{x})

    f : ∀{x : X} → A{x}{x}([≡]-intro {_}{_} {x})
    f{x} = [≡]-intro {_}{_} {Singleton-existence{x}}

    Φ : ∀{y x : X}{xy-proof : (y ≡ x)} → ([∃]-intro y ⦃ xy-proof ⦄ ≡ Singleton-existence{x})
    Φ {y}{x}{xy-proof} = idElim(_≡_ {T = X}) (A)(f) {y}{x}(xy-proof)

    g : ∀{x : X}{σ : Singleton(x)} → (σ ≡ Singleton-existence{x})
    g{x}{[∃]-intro y ⦃ proof ⦄} = Φ{y}{x}{proof}
