module Structure.Operator.Monoid.Category where

open import Data
open import Data.Tuple as Tuple using (_,_)
open import Functional
import      Lvl
open import Sets.Setoid
open import Structure.Category
open import Structure.Category.Properties
open import Structure.Operator.Monoid
open import Structure.Operator.Properties using (associativity ; identityₗ ; identityᵣ)
open import Structure.Operator
open import Type

module _
  {ℓ}
  {T : Type{ℓ}}
  ⦃ _ : Equiv(T) ⦄
  {_▫_ : T → T → T}
  ⦃ op : BinaryOperator(_▫_) ⦄
  (M : Monoid(_▫_))
  where

  monoidCategory : Category{Obj = Unit{Lvl.𝟎}}(const(const(T)))
  Category._∘_            monoidCategory = (_▫_)
  Category.id             monoidCategory = Monoid.id(M)
  Category.binaryOperator monoidCategory = op
  Category.associativity  monoidCategory = Morphism.intro(associativity(_▫_))
  Category.identity       monoidCategory = Morphism.intro (identityₗ(_▫_)(Monoid.id(M))) , Morphism.intro ((identityᵣ(_▫_)(Monoid.id(M))))
