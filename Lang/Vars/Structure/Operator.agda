module Lang.Vars.Structure.Operator where

import Lvl
open import Data
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Operator
open import Type

-- TODO: These are to make the generalized variables work when they depend on each other. Are there any better ways?
module Select where
  module _ {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂} {A : Type{ℓ₁}} {B : Type{ℓ₂}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
    select-func : ∀(f : A → B) → Function(f) → Type{Lvl.𝟎}
    select-func _ _ = Data.Unit

    module _ {f : A → B} where
      variable ⦃ func ⦄ : Function ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ (f)

  module _ {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
    select-invol : ∀(f : T → T) → Involution(f) → Type{Lvl.𝟎}
    select-invol _ _ = Data.Unit

    module _ {f : T → T} where
      variable ⦃ invol ⦄ : Involution ⦃ equiv ⦄ f

  module _ {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_▫_ : T → T → T} where
    select-id : ∀(id) → Identity(_▫_)(id) → Type{Lvl.𝟎}
    select-id _ _ = Data.Unit

    select-idₗ : ∀(id) → Identityₗ(_▫_)(id) → Type{Lvl.𝟎}
    select-idₗ _ _ = Data.Unit

    select-idᵣ : ∀(id) → Identityᵣ(_▫_)(id) → Type{Lvl.𝟎}
    select-idᵣ _ _ = Data.Unit

    select-inv : ∀(id)(ident)(inv) → InverseFunction(_▫_) ⦃ [∃]-intro(id) ⦃ ident ⦄ ⦄ (inv) → Type{Lvl.𝟎}
    select-inv _ _ _ _ = Data.Unit

    select-invₗ : ∀(id)(ident)(inv) → InverseFunctionₗ(_▫_) ⦃ [∃]-intro(id) ⦃ ident ⦄ ⦄ (inv) → Type{Lvl.𝟎}
    select-invₗ _ _ _ _ = Data.Unit

    select-invᵣ : ∀(id)(ident)(inv) → InverseFunctionᵣ(_▫_) ⦃ [∃]-intro(id) ⦃ ident ⦄ ⦄ (inv) → Type{Lvl.𝟎}
    select-invᵣ _ _ _ _ = Data.Unit

    select-invPropₗ : ∀(inv) → InversePropertyₗ(_▫_)(inv) → Type{Lvl.𝟎}
    select-invPropₗ _ _ = Data.Unit

    select-invPropᵣ : ∀(inv) → InversePropertyᵣ(_▫_)(inv) → Type{Lvl.𝟎}
    select-invPropᵣ _ _ = Data.Unit

    select-abs : ∀(id) → Absorber(_▫_)(id) → Type{Lvl.𝟎}
    select-abs _ _ = Data.Unit

    select-absₗ : ∀(id) → Absorberₗ(_▫_)(id) → Type{Lvl.𝟎}
    select-absₗ _ _ = Data.Unit

    select-absᵣ : ∀(id) → Absorberᵣ(_▫_)(id) → Type{Lvl.𝟎}
    select-absᵣ _ _ = Data.Unit

module One {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_▫_ : T → T → T} where
  variable {id idₗ idᵣ ab abₗ abᵣ} : T
  variable {inv invₗ invᵣ} : T → T
  variable ⦃ op ⦄ : BinaryOperator ⦃ equiv ⦄ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫_)
  variable ⦃ comm ⦄ : Commutativity ⦃ equiv ⦄ (_▫_)
  variable ⦃ cancₗ ⦄ : Cancellationₗ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫_)
  variable ⦃ cancᵣ ⦄ : Cancellationᵣ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫_)
  variable ⦃ assoc ⦄ : Associativity ⦃ equiv ⦄ (_▫_)
  variable ⦃ ident  ⦄ : Identity ⦃ equiv ⦄ (_▫_)(id)
  variable ⦃ identₗ ⦄ : Identityₗ ⦃ equiv ⦄ (_▫_)(id)
  variable ⦃ identᵣ ⦄ : Identityᵣ ⦃ equiv ⦄ (_▫_)(id)
  variable ⦃ inver  ⦄ : InverseFunction ⦃ equiv ⦄ (_▫_) ⦃ [∃]-intro(id) ⦃ ident ⦄ ⦄ (inv)
  variable ⦃ inverₗ ⦄ : InverseFunctionₗ ⦃ equiv ⦄ (_▫_) ⦃ [∃]-intro(idₗ) ⦃ identₗ ⦄ ⦄ (invₗ)
  variable ⦃ inverᵣ ⦄ : InverseFunctionᵣ ⦃ equiv ⦄ (_▫_) ⦃ [∃]-intro(idᵣ) ⦃ identᵣ ⦄ ⦄ (invᵣ)
  variable ⦃ inverPropₗ ⦄ : InversePropertyₗ ⦃ equiv ⦄ (_▫_) (invₗ)
  variable ⦃ inverPropᵣ ⦄ : InversePropertyᵣ ⦃ equiv ⦄ (_▫_) (invᵣ)
  variable ⦃ absorb  ⦄ : Absorber ⦃ equiv ⦄ (_▫_)(ab)
  variable ⦃ absorbₗ ⦄ : Absorberₗ ⦃ equiv ⦄ (_▫_)(ab)
  variable ⦃ absorbᵣ ⦄ : Absorberᵣ ⦃ equiv ⦄ (_▫_)(ab)

module OneTypeTwoOp {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_▫₁_ _▫₂_ : T → T → T} where
  variable {id id₁ id₂} : T
  variable {inv inv₁ inv₂} : T → T

  variable ⦃ op₁ ⦄ : BinaryOperator ⦃ equiv ⦄ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₁_)
  variable ⦃ comm₁ ⦄ : Commutativity ⦃ equiv ⦄ (_▫₁_)
  variable ⦃ cancₗ₁ ⦄ : Cancellationₗ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₁_)
  variable ⦃ cancᵣ₁ ⦄ : Cancellationᵣ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₁_)
  variable ⦃ assoc₁ ⦄ : Associativity ⦃ equiv ⦄ (_▫₁_)
  variable ⦃ ident₁  ⦄ : Identity ⦃ equiv ⦄ (_▫₁_)(id)
  variable ⦃ identₗ₁ ⦄ : Identityₗ ⦃ equiv ⦄ (_▫₁_)(id)
  variable ⦃ identᵣ₁ ⦄ : Identityᵣ ⦃ equiv ⦄ (_▫₁_)(id)
  variable ⦃ inver₁  ⦄ : InverseFunction ⦃ equiv ⦄ (_▫₁_) ⦃ [∃]-intro(id) ⦃ ident₁ ⦄ ⦄ (inv)
  variable ⦃ inverₗ₁ ⦄ : InverseFunctionₗ ⦃ equiv ⦄ (_▫₁_) ⦃ [∃]-intro(id) ⦃ identₗ₁ ⦄ ⦄ (inv)
  variable ⦃ inverᵣ₁ ⦄ : InverseFunctionᵣ ⦃ equiv ⦄ (_▫₁_) ⦃ [∃]-intro(id) ⦃ identᵣ₁ ⦄ ⦄ (inv)
  variable ⦃ absorbₗ₁ ⦄ : Absorberₗ ⦃ equiv ⦄ (_▫₁_)(id)
  variable ⦃ absorbᵣ₁ ⦄ : Absorberᵣ ⦃ equiv ⦄ (_▫₁_)(id)

  variable ⦃ op₂ ⦄ : BinaryOperator ⦃ equiv ⦄ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₂_)
  variable ⦃ comm₂ ⦄ : Commutativity ⦃ equiv ⦄ (_▫₂_)
  variable ⦃ cancₗ₂ ⦄ : Cancellationₗ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₂_)
  variable ⦃ cancᵣ₂ ⦄ : Cancellationᵣ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₂_)
  variable ⦃ assoc₂ ⦄ : Associativity ⦃ equiv ⦄ (_▫₂_)
  variable ⦃ ident₂  ⦄ : Identity ⦃ equiv ⦄ (_▫₂_)(id)
  variable ⦃ identₗ₂ ⦄ : Identityₗ ⦃ equiv ⦄ (_▫₂_)(id)
  variable ⦃ identᵣ₂ ⦄ : Identityᵣ ⦃ equiv ⦄ (_▫₂_)(id)
  variable ⦃ inver₂  ⦄ : InverseFunction ⦃ equiv ⦄ (_▫₂_) ⦃ [∃]-intro(id) ⦃ ident₂ ⦄ ⦄ (inv)
  variable ⦃ inverₗ₂ ⦄ : InverseFunctionₗ ⦃ equiv ⦄ (_▫₂_) ⦃ [∃]-intro(id) ⦃ identₗ₂ ⦄ ⦄ (inv)
  variable ⦃ inverᵣ₂ ⦄ : InverseFunctionᵣ ⦃ equiv ⦄ (_▫₂_) ⦃ [∃]-intro(id) ⦃ identᵣ₂ ⦄ ⦄ (inv)
  variable ⦃ absorbₗ₂ ⦄ : Absorberₗ ⦃ equiv ⦄ (_▫₂_)(id)
  variable ⦃ absorbᵣ₂ ⦄ : Absorberᵣ ⦃ equiv ⦄ (_▫₂_)(id)

  variable ⦃ distriₗ ⦄ : Distributivityₗ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)
  variable ⦃ distriᵣ ⦄ : Distributivityᵣ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)
  variable ⦃ absorpₗ ⦄ : Absorptionₗ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)
  variable ⦃ absorpᵣ ⦄ : Absorptionᵣ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)
  variable ⦃ inverOpₗ ⦄ : InverseOperatorₗ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)
  variable ⦃ inverOpᵣ ⦄ : InverseOperatorᵣ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)

module Two {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂} {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {_▫₁_ : A → A → A} {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ {_▫₂_ : B → B → B} where
  variable {id₁} : A
  variable {inv₁} : A → A
  variable {id₂} : B
  variable {inv₂} : B → B

  variable ⦃ op₁ ⦄ : BinaryOperator ⦃ equiv-A ⦄ ⦃ equiv-A ⦄ ⦃ equiv-A ⦄ (_▫₁_)
  variable ⦃ comm₁ ⦄ : Commutativity ⦃ equiv-A ⦄ (_▫₁_)
  variable ⦃ cancₗ₁ ⦄ : Cancellationₗ ⦃ equiv-A ⦄ ⦃ equiv-A ⦄ (_▫₁_)
  variable ⦃ cancᵣ₁ ⦄ : Cancellationᵣ ⦃ equiv-A ⦄ ⦃ equiv-A ⦄ (_▫₁_)
  variable ⦃ assoc₁ ⦄ : Associativity ⦃ equiv-A ⦄ (_▫₁_)
  variable ⦃ ident₁  ⦄ : Identity ⦃ equiv-A ⦄ (_▫₁_)(id₁)
  variable ⦃ identₗ₁ ⦄ : Identityₗ ⦃ equiv-A ⦄ (_▫₁_)(id₁)
  variable ⦃ identᵣ₁ ⦄ : Identityᵣ ⦃ equiv-A ⦄ (_▫₁_)(id₁)
  variable ⦃ inver₁  ⦄ : InverseFunction ⦃ equiv-A ⦄ (_▫₁_) ⦃ [∃]-intro(id₁) ⦃ ident₁ ⦄ ⦄ (inv₁)
  variable ⦃ inverₗ₁ ⦄ : InverseFunctionₗ ⦃ equiv-A ⦄ (_▫₁_) ⦃ [∃]-intro(id₁) ⦃ identₗ₁ ⦄ ⦄ (inv₁)
  variable ⦃ inverᵣ₁ ⦄ : InverseFunctionᵣ ⦃ equiv-A ⦄ (_▫₁_) ⦃ [∃]-intro(id₁) ⦃ identᵣ₁ ⦄ ⦄ (inv₁)

  variable ⦃ op₂ ⦄ : BinaryOperator ⦃ equiv-B ⦄ ⦃ equiv-B ⦄ ⦃ equiv-B ⦄ (_▫₂_)
  variable ⦃ comm₂ ⦄ : Commutativity ⦃ equiv-B ⦄ (_▫₂_)
  variable ⦃ cancₗ₂ ⦄ : Cancellationₗ ⦃ equiv-B ⦄ ⦃ equiv-B ⦄ (_▫₂_)
  variable ⦃ cancᵣ₂ ⦄ : Cancellationᵣ ⦃ equiv-B ⦄ ⦃ equiv-B ⦄ (_▫₂_)
  variable ⦃ assoc₂ ⦄ : Associativity ⦃ equiv-B ⦄ (_▫₂_)
  variable ⦃ ident₂  ⦄ : Identity ⦃ equiv-B ⦄ (_▫₂_)(id₂)
  variable ⦃ identₗ₂ ⦄ : Identityₗ ⦃ equiv-B ⦄ (_▫₂_)(id₂)
  variable ⦃ identᵣ₂ ⦄ : Identityᵣ ⦃ equiv-B ⦄ (_▫₂_)(id₂)
  variable ⦃ inver₂  ⦄ : InverseFunction ⦃ equiv-B ⦄ (_▫₂_) ⦃ [∃]-intro(id₂) ⦃ ident₂ ⦄ ⦄ (inv₂)
  variable ⦃ inverₗ₂ ⦄ : InverseFunctionₗ ⦃ equiv-B ⦄ (_▫₂_) ⦃ [∃]-intro(id₂) ⦃ identₗ₂ ⦄ ⦄ (inv₂)
  variable ⦃ inverᵣ₂ ⦄ : InverseFunctionᵣ ⦃ equiv-B ⦄ (_▫₂_) ⦃ [∃]-intro(id₂) ⦃ identᵣ₂ ⦄ ⦄ (inv₂)
