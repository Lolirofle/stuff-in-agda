module Structure.Operator.Monoid.Category where

open import Data
open import Functional
import      Lvl
open import Sets.Setoid
open import Structure.Category
open import Structure.Operator.Monoid
open import Structure.Operator.Properties using (associativity)
open import Type

module _
  {ℓ}
  {T : Type{ℓ}}
  ⦃ _ : Equiv(T) ⦄
  {_▫_ : T → T → T}
  (M : Monoid(_▫_))
  where

  monoidCategory : Category{Obj = Unit{Lvl.𝟎}}(const(const(T)))
  Category._∘_           (monoidCategory) {_}{_}{_} = (_▫_)
  Category.id            (monoidCategory) {_} = Monoid.id(M)
  Category.identityₗ     (monoidCategory) {_}{_} = Monoid.identityₗ(M)
  Category.identityᵣ     (monoidCategory) {_}{_} = Monoid.identityᵣ(M)
  Category.associativity (monoidCategory) {_}{_}{_}{_} = associativity(_▫_) ⦃ Monoid.associativity(M) ⦄
