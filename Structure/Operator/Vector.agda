module Structure.Operator.Vector where

open import Functional using (swap)
import      Lvl
open import Logic
open import Logic.Propositional
open import Structure.Setoid.WithLvl
open import Structure.Operator.Field
open import Structure.Operator.Group
open import Structure.Operator.Monoid
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Operator
open import Type

record VectorSpace {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ}
                   {V : Type{ℓᵥ}} ⦃ _ : Equiv{ℓᵥₑ}(V) ⦄
                   {S : Type{ℓₛ}} ⦃ _ : Equiv{ℓₛₑ}(S) ⦄
                   (_+ᵥ_ : V → V → V)
                   (_⋅ₛᵥ_ : S → V → V)
                   (_+ₛ_ : S → S → S)
                   (_⋅ₛ_ : S → S → S)
                   : Stmt{ℓₛₑ Lvl.⊔ ℓₛ Lvl.⊔ ℓᵥₑ Lvl.⊔ ℓᵥ} where
  constructor intro
  field
    ⦃ scalarField ⦄            : Field(_+ₛ_)(_⋅ₛ_)
    ⦃ vectorCommutativeGroup ⦄ : CommutativeGroup(_+ᵥ_)

  open Field(scalarField)
    renaming (
      𝟎 to 𝟎ₛ ;
      𝟏 to 𝟏ₛ ;
      _−_ to _−ₛ_ ;
      _/_ to _/ₛ_ ;
      −_ to −ₛ_ ;
      ⅟ to ⅟ₛ ;
      [+]-group              to [+ₛ]-group ;
      [+]-commutativity      to [+ₛ]-commutativity ;
      [+]-monoid             to [+ₛ]-monoid ;
      [+]-binary-operator    to [+ₛ]-binary-operator ;
      [+]-associativity      to [+ₛ]-associativity ;
      [+]-identity-existence to [+ₛ]-identity-existence ;
      [+]-identity           to [+ₛ]-identity ;
      [+]-identityₗ          to [+ₛ]-identityₗ ;
      [+]-identityᵣ          to [+ₛ]-identityᵣ ;
      [+]-inverse-existence  to [+ₛ]-inverse-existence ;
      [+]-inverse            to [+ₛ]-inverse ;
      [+]-inverseₗ           to [+ₛ]-inverseₗ ;
      [+]-inverseᵣ           to [+ₛ]-inverseᵣ ;
      [−]-function           to [−ₛ]-function ;
      [⋅]-binary-operator    to [⋅ₛ]-binary-operator ;
      [⋅]-associativity      to [⋅ₛ]-associativity ;
      [⋅]-identity-existence to [⋅ₛ]-identity-existence ;
      [⋅]-identity           to [⋅ₛ]-identity ;
      [⋅]-identityₗ          to [⋅ₛ]-identityₗ ;
      [⋅]-identityᵣ          to [⋅ₛ]-identityᵣ ;
      [⋅]-inverseₗ           to [⋅ₛ]-inverseₗ ;
      [⋅]-inverseᵣ           to [⋅ₛ]-inverseᵣ ;
      distinct-identities to distinct-identitiesₛ
    ) public
  open CommutativeGroup(vectorCommutativeGroup)
    renaming (
      id to 𝟎ᵥ ;
      inv to −ᵥ_ ;
      inv-op to _−ᵥ_ ;
      group               to [+ᵥ]-group;
      commutativity       to [+ᵥ]-commutativity;
      monoid              to [+ᵥ]-monoid ;
      binary-operator     to [+ᵥ]-binary-operator ;
      associativity       to [+ᵥ]-associativity ;
      identity-existence  to [+ᵥ]-identity-existence ;
      identity            to [+ᵥ]-identity ;
      identityₗ           to [+ᵥ]-identityₗ ;
      identityᵣ           to [+ᵥ]-identityᵣ ;
      inverse-existence   to [+ᵥ]-inverse-existence ;
      inverse             to [+ᵥ]-inverse ;
      inverseₗ            to [+ᵥ]-inverseₗ ;
      inverseᵣ            to [+ᵥ]-inverseᵣ ;
      inv-function        to [−ᵥ]-function
    ) public

  field
    ⦃ [⋅ₛᵥ]-binaryOperator ⦄      : BinaryOperator(_⋅ₛᵥ_)
    [⋅ₛ][⋅ₛᵥ]-compatibility       : Names.Compatibility(_⋅ₛ_)(_⋅ₛᵥ_) -- TODO: This is semigroup action
    ⦃ [⋅ₛᵥ]-identity ⦄            : Identityₗ(_⋅ₛᵥ_)(𝟏ₛ)
    ⦃ [⋅ₛᵥ][+ᵥ]-distributivityₗ ⦄ : Distributivityₗ(_⋅ₛᵥ_)(_+ᵥ_)
    [⋅ₛᵥ][+ₛ][+ᵥ]-distributivityᵣ : Names.DistributivityPatternᵣ(_⋅ₛᵥ_)(_+ₛ_)(_+ᵥ_) -- TODO: This is ∀? → Preserving₂

  _⋅ᵥₛ_ = swap(_⋅ₛᵥ_)

record VectorSpaceVObject {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ}
  {S : Type{ℓₛ}} ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (_+ₛ_ : S → S → S)
  (_⋅ₛ_ : S → S → S)
  : Stmt{ℓₛₑ Lvl.⊔ ℓₛ Lvl.⊔ Lvl.𝐒(ℓᵥₑ Lvl.⊔ ℓᵥ)}
  where

  constructor intro
  field
    {Vector} : Type{ℓᵥ}
    ⦃ Vector-equiv ⦄ : Equiv{ℓᵥₑ}(Vector)
    _+ᵥ_ : Vector → Vector → Vector
    _⋅ₛᵥ_ : S → Vector → Vector
    ⦃ vectorSpace ⦄ : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_)
  open VectorSpace(vectorSpace) public

record VectorSpaceObject {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ} : Stmt{Lvl.𝐒(ℓₛₑ Lvl.⊔ ℓₛ Lvl.⊔ ℓᵥₑ Lvl.⊔ ℓᵥ)} where
  constructor intro
  field
    {Vector} : Type{ℓᵥ}
    ⦃ equiv-Vector ⦄ : Equiv{ℓᵥₑ}(Vector)
    {Scalar} : Type{ℓₛ}
    ⦃ equiv-Scalar ⦄ : Equiv{ℓₛₑ}(Scalar)
    _+ᵥ_  : Vector → Vector → Vector
    _⋅ₛᵥ_ : Scalar → Vector → Vector
    _+ₛ_  : Scalar → Scalar → Scalar
    _⋅ₛ_  : Scalar → Scalar → Scalar
    ⦃ vectorSpace ⦄ : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_)
  open VectorSpace(vectorSpace) public
