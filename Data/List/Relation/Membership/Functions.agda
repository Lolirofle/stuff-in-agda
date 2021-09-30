module Data.List.Relation.Membership.Functions where

open import Data.List
open import Data.List.Relation.Membership
open import Data.List.Relation.Quantification
open import Structure.Setoid renaming (_≡_ to _≡ₛ_)
import      Lvl
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T A B C : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  without : (l : List(T)) → ∀{x} → (x ∈ l) → List(T)
  without (_ ⊰ l) (• _) = l
  without (x ⊰ l) (⊰ p) = x ⊰ without l p

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  open import Data.List.Relation.Sublist
  open import Data.List.Relation.Sublist.Proofs
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  private variable x y : T
  private variable l : List(T)

  without-sublist : (elem : x ∈ l) → (without l elem ⊏ l)
  without-sublist (• p) = _⊏_.skip (reflexivity(_⊑_))
  without-sublist (⊰ p) = _⊏_.use (reflexivity(_≡ₛ_)) (without-sublist p)

  AllElements-without : ∀{P : _ → Type{ℓ}} → (xl : x ∈ l) → AllElements P(l) → AllElements P(without l xl)
  AllElements-without (• _)  (_  ⊰ apl) = apl
  AllElements-without (⊰ xl) (px ⊰ apl) = px ⊰ AllElements-without xl apl

module _ where
  open import Data.List.Relation.Permutation
  open import Data.List.Relation.Permutation.Proofs
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  private variable x y : T
  private variable l : List(T)

  prepend-without-inverse-permutes : (xl : x ∈ l) → (l permutes (x ⊰ (without l xl)))
  prepend-without-inverse-permutes (• [≡]-intro) = _permutes_.prepend (reflexivity(_permutes_))
  prepend-without-inverse-permutes (⊰ p)         = _permutes_.prepend (prepend-without-inverse-permutes p) 🝖 _permutes_.swap
