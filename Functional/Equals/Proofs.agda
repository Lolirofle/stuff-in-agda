module Functional.Equals.Proofs where

import      Lvl
open import Data
open import Functional
open import Functional.Equals
open import Logic.Propositional
open import Sets.Setoid
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

module _ where
  import Relator.Equals.Proofs

  [⊜]-emptyₗ : ∀{ℓ ℓₑ}{T : Type{ℓ}}{f g : T → Empty{ℓₑ}} → (f ⊜ g)
  [⊜]-emptyₗ {_}{_} {_} {f}{_} = [⊜]-intro(\{x} → empty(f(x)))

module _ {ℓ}{ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ where
  [⊜]-emptyᵣ : ∀{f g : Empty{ℓₑ} → T} → (f ⊜ g)
  [⊜]-emptyᵣ {_}{_} = [⊜]-intro(\{})

module _ {ℓ}{ℓₑ} {T : Type{ℓ}} where
  import Relator.Equals.Proofs

  [⊜]-unitₗ : ∀{f g : T → Unit{ℓₑ}} → (f ⊜ g)
  [⊜]-unitₗ {_}{_} = [⊜]-intro(reflexivity(_≡_))

module _ {ℓ₁}{ℓ₂}{ℓ₃} {A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} ⦃ _ : Equiv(C) ⦄ where
  [⊜]-compose₁ : ∀{f₁ f₂ : B → C}{g : A → B} → (f₁ ⊜ f₂) → ((f₁ ∘ g) ⊜ (f₂ ∘ g))
  [⊜]-compose₁ {g = g} ([⊜]-intro feq) = [⊜]-intro(\{x} → feq{g(x)})

-- TODO: When does ((x⊜y) → (f(x) ⊜ f(y))) hold? Does it need some assumptions about the setoid?
-- TODO: When is BinaryOperator(_∘_) satisfied?
module _ {ℓ₁}{ℓ₂}{ℓ₃} {A : Type{ℓ₁}} {B : Type{ℓ₂}} ⦃ _ : Equiv(B) ⦄ {C : Type{ℓ₃}} ⦃ _ : Equiv(C) ⦄ ⦃ _ : BinaryOperator(_∘_) ⦄ where
  [⊜]-compose : ∀{f₁ f₂ : B → C}{g₁ g₂ : A → B} → (f₁ ⊜ f₂) → (g₁ ⊜ g₂) → (f₁ ∘ g₁ ⊜ f₂ ∘ g₂)
  [⊜]-compose {f₁}{f₂} feq geq =
    [≡]-with (f₁ ∘_) ⦃ [≡]-congruence2-right(_∘_) {f₁} ⦄ geq
    🝖 [⊜]-compose₁ feq

-- TODO: Is this correct?
-- [⊜]-not-all : ∀{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (∀{f g : T₁ → T₂} → (f ⊜ g)) → IsEmpty(T₁)
-- [⊜]-not-all{_}{_} {_} {_}{_} = [⊜]-intro(\{})
