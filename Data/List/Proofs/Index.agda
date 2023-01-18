module Data.List.Proofs.Index where

{- TODO: This is in Data.List.Relation.Enum.Proofs
open import Data.List
open import Data.List.Functions
open import Data.List.Relation.Membership.Proofs
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  private variable l : List(T)

  instance
    surj : Surjective(index l)
    Surjective.proof surj{y} = [∃]-map-proof (symmetry(_≡_)) ([↔]-to-[→] [∈]-index-existence (p{y}))
    
-}
