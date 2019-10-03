module Functional.Equals.Proofs where

import      Lvl
open import Data
open import Functional
open import Functional.Equals
open import Logic.Propositional
open import Sets.Setoid
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

module _ {ℓ₁}{ℓ₂} {A : Type{ℓ₁}}{B : Type{ℓ₂}} ⦃ _ : Equiv(B) ⦄ where
  [⊜]-identityₗ : Identityₗ {T₂ = A → B} (_∘_)(id)
  _⊜_.proof(Identityₗ.proof([⊜]-identityₗ)) =  reflexivity(_≡_)

module _ {ℓ₁}{ℓ₂} {A : Type{ℓ₁}}{B : Type{ℓ₂}} ⦃ _ : Equiv(B) ⦄ where
  [⊜]-identityᵣ : Identityᵣ {T₁ = A → B} (_∘_)(id)
  _⊜_.proof(Identityᵣ.proof([⊜]-identityᵣ)) =  reflexivity(_≡_)

module _ {ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄} {A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}}{D : Type{ℓ₄}} ⦃ _ : Equiv(A) ⦄ where
  [⊜]-associativity : Names.AssociativityPattern {T₁ = B → A} {T₂ = C → B} {T₃ = D → C} (_∘_)(_∘_)(_∘_)(_∘_)
  _⊜_.proof ([⊜]-associativity {f} {g} {h}) {x} = reflexivity(_≡_)

module _ where
  import Relator.Equals.Proofs

  [⊜]-emptyₗ : ∀{ℓ ℓₑ}{T : Type{ℓ}}{f g : T → Empty{ℓₑ}} → (f ⊜ g)
  [⊜]-emptyₗ {_}{_} {_} {f}{_} = intro(\{x} → empty(f(x)))

module _ {ℓ}{ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ where
  [⊜]-emptyᵣ : ∀{f g : Empty{ℓₑ} → T} → (f ⊜ g)
  [⊜]-emptyᵣ {_}{_} = intro(\{})

module _ {ℓ}{ℓₑ} {T : Type{ℓ}} where
  import Relator.Equals.Proofs

  [⊜]-unitₗ : ∀{f g : T → Unit{ℓₑ}} → (f ⊜ g)
  [⊜]-unitₗ {_}{_} = intro(reflexivity(_≡_))

module _ {ℓ₁}{ℓ₂}{ℓ₃} {A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} ⦃ _ : Equiv(C) ⦄ where
  [⊜]-compose₁ : ∀{f₁ f₂ : B → C}{g : A → B} → (f₁ ⊜ f₂) → ((f₁ ∘ g) ⊜ (f₂ ∘ g))
  [⊜]-compose₁ {g = g} (intro feq) = intro(\{x} → feq{g(x)})

-- TODO: When does ((x⊜y) → (f(x) ⊜ f(y))) hold? Does it need some assumptions about the setoid?
-- TODO: When is BinaryOperator(_∘_) satisfied?
-- TODO: The instance resolutions here are preventing overlapping instances from working
module _ {ℓ₁}{ℓ₂}{ℓ₃} {A : Type{ℓ₁}} {B : Type{ℓ₂}} ⦃ _ : Equiv(B) ⦄ {C : Type{ℓ₃}} ⦃ _ : Equiv(C) ⦄ ⦃ _ : BinaryOperator(_∘_) ⦄ where
  [⊜]-compose : ∀{f₁ f₂ : B → C}{g₁ g₂ : A → B} → (f₁ ⊜ f₂) → (g₁ ⊜ g₂) → (f₁ ∘ g₁ ⊜ f₂ ∘ g₂)
  [⊜]-compose {f₁}{f₂} feq geq =
    [≡]-with (f₁ ∘_) ⦃ [≡]-congruence2-right(_∘_) {f₁} ⦄ geq
    🝖 [⊜]-compose₁ feq

-- TODO: Is this correct?
-- [⊜]-not-all : ∀{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (∀{f g : T₁ → T₂} → (f ⊜ g)) → IsEmpty(T₁)
-- [⊜]-not-all{_}{_} {_} {_}{_} = intro(\{})

{- TODO: What assumptions? Unprovable?
module _
  {ℓ} -- {ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄}
  {A : Type{ℓ}} ⦃ _ : Equiv(A) ⦄
  {B : Type{ℓ}} ⦃ _ : Equiv(B) ⦄
  {C : Type{ℓ}} ⦃ eq-c : Equiv(C) ⦄
  {D : Type{ℓ}} ⦃ eq-d : Equiv(D) ⦄
  {f : (A → B) → (C → D)}
  ⦃ fn : ∀{ab} → Function {T₁ = C} ⦃ eq-c ⦄ {T₂ = D} ⦃ eq-d ⦄ (f(ab)) ⦄
  where

  instance
    [⊜]-function : Function {T₁ = A → B} ⦃ [⊜]-equiv ⦄ {T₂ = C → D} ⦃ [⊜]-equiv ⦄ (f)
    _⊜_.proof (Function.congruence ([⊜]-function) {g} {h} (intro eq)) {x} = {!!}
-}
