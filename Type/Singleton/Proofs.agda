import      Lvl
open import Type

module Type.Singleton.Proofs {ℓₗ ℓₒ : Lvl.Level} {X : Type{ℓₒ}} where

open import Functional
open import Functional.Domains
open import Logic.Predicate{ℓₗ}
open import Relator.Equals{ℓₗ Lvl.⊔ ℓₒ}
open import Relator.Equals.Proofs
open import Type.Empty
open import Type.Singleton {ℓₗ}{ℓₒ}
open import Type.Unit

instance
  -- There is always a construction of a singleton type
  Singleton-existence : ∀{x : X} → Singleton(x)
  Singleton-existence {x} = intro(x) ⦃ [≡]-intro ⦄

instance
  -- There is an unique construction of a singleton type
  Singleton-is-unit : ∀{x : X} → IsUnit(Singleton(x))
  Singleton-is-unit {x} = intro (Singleton-existence{x}) (g{x}) where
    A : ∀{y x : X} → (y ≡ x) → Type{ℓₗ Lvl.⊔ ℓₒ}
    A {y}{x} (xy-proof) = (intro y ⦃ xy-proof ⦄ ≡ Singleton-existence{x})

    f : ∀{x : X} → A{x}{x}([≡]-intro {_}{_} {x})
    f{x} = [≡]-intro {_}{_} {Singleton-existence{x}}

    Φ : ∀{y x : X}{xy-proof : (y ≡ x)} → (intro y ⦃ xy-proof ⦄ ≡ Singleton-existence{x})
    Φ {y}{x}{xy-proof} = [≡]-identity-eliminator {ℓₗ Lvl.⊔ ℓₒ}{ℓₒ} {X} (A)(f) {y}{x}(xy-proof)

    g : ∀{x : X}{σ : Singleton(x)} → (σ ≡ Singleton-existence{x})
    g{x}{intro y ⦃ proof ⦄} = Φ{y}{x}{proof}