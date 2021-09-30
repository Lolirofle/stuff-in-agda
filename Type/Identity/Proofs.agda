module Type.Identity.Proofs where

import      Lvl
open import Structure.Function
open import Structure.Relator.Properties
open import Structure.Relator
open import Structure.Relator.Equivalence
open import Structure.Setoid
open import Structure.Type.Identity
open import Structure.Type.Identity.Proofs
open import Type.Identity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ ℓₗ ℓₚ ℓₘ : Lvl.Level
private variable T A B : Type{ℓ}
private variable P : T → Type{ℓ}
private variable _▫_ : A → B → Type{ℓ}

module One{T : Type{ℓ}} where
  instance
    Id-reflexivity : Reflexivity(Id{T = T})
    Reflexivity.proof Id-reflexivity = intro

  instance
    Id-identityEliminator : IdentityEliminator{ℓₚ = ℓₚ}(Id{T = T})
    IdentityEliminator.elim Id-identityEliminator = elim

  instance
    Id-identityEliminationOfIntro : IdentityEliminationOfIntro{ℓₘ = ℓₘ}(Id{T = T})(Id)
    IdentityEliminationOfIntro.proof Id-identityEliminationOfIntro P p = intro

  instance
    Id-symmetry : Symmetry(Id{T = T})
    Id-symmetry = identity-eliminator-to-symmetry

  instance
    Id-transitivity : Transitivity(Id{T = T})
    Id-transitivity = identity-eliminator-to-transitivity

  instance
    Id-equivalence : Equivalence(Id{T = T})
    Id-equivalence = intro

  Id-equiv : Equiv(T)
  Id-equiv = intro Id ⦃ Id-equivalence ⦄

  -- Id is a subrelation to every reflexive relation.
  -- One interpretation of this is that identity is the "smallest" reflexive relation in the sense that the size is the cardinality of the set representation of the relation (as a set of tuples).
  instance
    Id-reflexive-relator-sub : ∀{_▫_ : T → T → Type{ℓₗ}} → ⦃ Reflexivity(_▫_) ⦄ → (Id ⊆₂ (_▫_))
    _⊆₂_.proof Id-reflexive-relator-sub intro = reflexivity(_)
open One public

instance
  Id-identityType : IdentityType(Id)
  Id-identityType = intro

Id-to-function : ∀ ⦃ equiv : Equiv{ℓₑ}(B) ⦄ {f : A → B} → Function ⦃ Id-equiv ⦄ ⦃ equiv ⦄ f
Id-to-function = minimal-reflection-to-function ⦃ equiv-A = Id-equiv ⦄

{-
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Relator.Equals.Proofs
open import Structure.Setoid

te : ⦃ equiv-A : Equiv{ℓₑ}(A)⦄ → ∀{f : A → Type{ℓ}} → Function ⦃ equiv-A ⦄ ⦃ [↔]-equiv ⦄ (f)

test : ⦃ equiv-A : Equiv{ℓₑ}(A)⦄ → ∀{P : A → Type{ℓ}} → UnaryRelator ⦃ equiv-A ⦄ (P)
UnaryRelator.substitution test eq p = [↔]-to-[→] (Function.congruence te eq) p
-}
