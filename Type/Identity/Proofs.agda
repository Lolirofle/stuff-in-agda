module Type.Identity.Proofs where

import      Lvl
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Relator
open import Structure.Relator.Equivalence
open import Structure.Setoid
open import Structure.Type.Identity
open import Structure.Type.Identity.Eliminator.Equality
open import Type.Identity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ ℓₗ ℓₚ ℓₘ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable P : T → Type{ℓ}
private variable _▫_ : A → B → Type{ℓ}

module One{T : Type{ℓ}} where
  instance
    Id-reflexivity : Reflexivity(Id{T = T})
    Reflexivity.proof Id-reflexivity = intro

  instance
    Id-identityEliminator : IdentityEliminator(Id{T = T}) {ℓₚ}
    IdentityEliminator.elim Id-identityEliminator = elim

  instance
    Id-identityEliminationOfIntro : ∀{P : ∀{x y : T} → Id x y → Type{ℓₚ}} → IdentityEliminationOfIntro Id P Id
    IdentityEliminationOfIntro.proof Id-identityEliminationOfIntro p = intro

  instance
    Id-symmetry : Symmetry(Id{T = T})
    Id-symmetry = identityEliminator-to-symmetry

  instance
    Id-transitivity : Transitivity(Id{T = T})
    Id-transitivity = identityEliminator-to-transitivity

  instance
    Id-equivalence : Equivalence(Id{T = T})
    Id-equivalence = identityEliminator-to-equivalence

  Id-equiv : Equiv(T)
  Id-equiv = intro Id ⦃ Id-equivalence ⦄

  -- Id is a subrelation to every reflexive relation.
  -- One interpretation of this is that identity is the "smallest" reflexive relation in the sense that the size is the cardinality of the set representation of the relation (as a set of tuples).
  instance
    Id-minimalReflexiveRelation : MinimalReflexiveRelation{ℓₚ = ℓₚ}{T = T}(Id)
    Id-minimalReflexiveRelation = identityEliminator-to-reflexive-subrelation
open One public

instance
  Id-identityType : IdentityType(Id)
  Id-identityType = intro

Id-to-function : ∀ ⦃ equiv : Equiv{ℓₑ}(B) ⦄ {f : A → B} → Function ⦃ Id-equiv ⦄ ⦃ equiv ⦄ f
Id-to-function = identityEliminator-to-function

Id-to-function₂ : ∀ ⦃ equiv : Equiv{ℓₑ}(C) ⦄ {f : A → B → C} → BinaryOperator ⦃ Id-equiv ⦄ ⦃ Id-equiv ⦄ ⦃ equiv ⦄ f
Id-to-function₂ = identityEliminator-to-binaryOperator

Id-function : ∀{f : A → B} → Function ⦃ Id-equiv ⦄ ⦃ Id-equiv ⦄ f
Id-function = Id-to-function ⦃ Id-equiv ⦄

Id-function₂ : ∀{f : A → B → C} → BinaryOperator ⦃ Id-equiv ⦄ ⦃ Id-equiv ⦄ ⦃ Id-equiv ⦄ f
Id-function₂ = Id-to-function₂ ⦃ Id-equiv ⦄
