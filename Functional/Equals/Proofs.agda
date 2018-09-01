module Functional.Equals.Proofs{ℓₗ} where

import      Lvl
open import Data
open import Functional
open import Functional.Equals{ℓₗ}
open import Logic.Propositional
open import Relator.Equals.Proofs{ℓₗ}
open import Sets.Setoid{ℓₗ}
open import Structure.Relator.Equivalence{ℓₗ}
open import Structure.Relator.Properties{ℓₗ}
open import Type

[⊜]-emptyₗ : ∀{ℓ ℓₑ}{T : Type{ℓ}}{f g : T → Empty{ℓₑ}} → (f ⊜ g)
[⊜]-emptyₗ {_}{_} {_} {f}{_} = [⊜]-intro(\{x} → empty(f(x)))

[⊜]-emptyᵣ : ∀{ℓ ℓₑ}{T : Type{ℓ}}{f g : Empty{ℓₑ} → T} → (f ⊜ g)
[⊜]-emptyᵣ{_}{_} {_} {_}{_} = [⊜]-intro(\{})

[⊜]-unitₗ : ∀{ℓ ℓₑ}{T : Type{ℓ}}{f g : T → Unit{ℓₑ}} → (f ⊜ g)
[⊜]-unitₗ{_}{_} {_} {_}{_} = [⊜]-intro(reflexivity)

-- [⊜]-compose TODO: When does (f₁∘g₁ ⊜ f₂∘g₂) hold?

-- TODO: Is this correct?
-- [⊜]-not-all : ∀{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (∀{f g : T₁ → T₂} → (f ⊜ g)) → IsEmpty(T₁)
-- [⊜]-not-all{_}{_} {_} {_}{_} = [⊜]-intro(\{})
