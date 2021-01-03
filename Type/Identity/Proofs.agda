module Type.Identity.Proofs where

import      Lvl
open import Structure.Function
open import Structure.Relator.Properties
open import Structure.Relator
open import Structure.Type.Identity
open import Type.Identity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ ℓₚ : Lvl.Level
private variable T A B : Type{ℓ}
private variable P : T → Type{ℓ}
private variable _▫_ : A → B → Type{ℓ}

instance
  Id-reflexivity : Reflexivity(Id{T = T})
  Reflexivity.proof Id-reflexivity = intro

instance
  Id-identityEliminator : IdentityEliminator{ℓₚ = ℓₚ}(Id{T = T})
  IdentityEliminator.elim Id-identityEliminator = elim

instance
  Id-identityEliminationOfIntro : IdentityEliminationOfIntro{ℓₘ = ℓ}(Id{T = T})(Id)
  IdentityEliminationOfIntro.proof Id-identityEliminationOfIntro P p = intro

instance
  Id-identityType : IdentityType(Id)
  Id-identityType = intro

{-
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Relator.Equals.Proofs
open import Structure.Setoid

te : ⦃ equiv-A : Equiv{ℓₑ}(A)⦄ → ∀{f : A → Type{ℓ}} → Function ⦃ equiv-A ⦄ ⦃ [↔]-equiv ⦄ (f)

test : ⦃ equiv-A : Equiv{ℓₑ}(A)⦄ → ∀{P : A → Type{ℓ}} → UnaryRelator ⦃ equiv-A ⦄ (P)
UnaryRelator.substitution test eq p = [↔]-to-[→] (Function.congruence te eq) p
-}
