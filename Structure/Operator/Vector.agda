module Structure.Operator.Vector where

open import Functional using (swap)
import      Lvl
open import Logic
open import Logic.Propositional
open import Structure.Function.Multi
open import Structure.Operator.Field
open import Structure.Operator.Group
open import Structure.Operator.Monoid
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Structure.Operator.Semi
open import Structure.Operator
open import Structure.Setoid
open import Type

private variable ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ : Lvl.Level
private variable V : Type{ℓᵥ}
private variable S : Type{ℓₛ}

module _
  ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (_+ᵥ_ : V → V → V)
  (_⋅ₛᵥ_ : S → V → V)
  (_+ₛ_ : S → S → S)
  (_⋅ₛ_ : S → S → S)
  where

  record ScalarMultiplicationCore ⦃ scalarSemiRg : SemiRg(_+ₛ_)(_⋅ₛ_) ⦄ ⦃ vectorSemi : Semi(_+ᵥ_) ⦄ : Stmt{ℓₛₑ Lvl.⊔ Lvl.of(S) Lvl.⊔ ℓᵥₑ Lvl.⊔ Lvl.of(V)} where
    constructor intro
    field
      ⦃ [⋅ₛᵥ]-binaryOperator ⦄      : BinaryOperator(_⋅ₛᵥ_)
      ⦃ [⋅ₛᵥ][+ᵥ]-distributivityₗ ⦄ : Distributivityₗ(_⋅ₛᵥ_)(_+ᵥ_)
      ⦃ [⋅ₛᵥ]ₗ[⋅]ᵣ-preserving ⦄     : ∀{s}{v} → Preserving₁(_⋅ₛᵥ v)(s ⋅ₛ_)(s ⋅ₛᵥ_) -- Note: This is also called: Semigroup action
      ⦃ [⋅ₛᵥ]ₗ[+]-preserving ⦄      : ∀{v} → Preserving₂(_⋅ₛᵥ v)(_+ₛ_)(_+ᵥ_)
    _⋅ᵥₛ_ = swap(_⋅ₛᵥ_)

  record RigModule {ℓₙ₀} : Stmt{ℓₛₑ Lvl.⊔ Lvl.of(S) Lvl.⊔ ℓᵥₑ Lvl.⊔ Lvl.of(V) Lvl.⊔ Lvl.𝐒(ℓₙ₀)} where
    constructor intro
    field
      ⦃ scalarRig ⦄    : Rig(_+ₛ_)(_⋅ₛ_) {ℓₙ₀}
      ⦃ vectorMonoid ⦄ : Monoid(_+ᵥ_)
    open Rig(scalarRig)
      renaming (
        𝟎 to 𝟎ₛ ;
        𝟏 to 𝟏ₛ ;
        semiRg                 to scalarSemiRg ;
        rg                     to scalarRg ;
        [+]-monoid             to [+ₛ]-monoid ;
        [+]-semi               to [+ₛ]-semi ;
        [+]-binaryOperator     to [+ₛ]-binaryOperator ;
        [+]-associativity      to [+ₛ]-associativity ;
        [+]-identity-existence to [+ₛ]-identity-existence ;
        [+]-identity           to [+ₛ]-identity ;
        [+]-identityₗ          to [+ₛ]-identityₗ ;
        [+]-identityᵣ          to [+ₛ]-identityᵣ ;
        [⋅]-monoid             to [⋅ₛ]-monoid ;
        [⋅]-semi               to [⋅ₛ]-semi ;
        [⋅]-binaryOperator     to [⋅ₛ]-binaryOperator ;
        [⋅]-associativity      to [⋅ₛ]-associativity ;
        [⋅]-identity-existence to [⋅ₛ]-identity-existence ;
        [⋅]-identity           to [⋅ₛ]-identity ;
        [⋅]-identityₗ          to [⋅ₛ]-identityₗ ;
        [⋅]-identityᵣ          to [⋅ₛ]-identityᵣ ;
        [⋅][+]-distributivity  to [⋅ₛ][+ₛ]-distributivity ;
        [⋅][+]-distributivityₗ to [⋅ₛ][+ₛ]-distributivityₗ ;
        [⋅][+]-distributivityᵣ to [⋅ₛ][+ₛ]-distributivityᵣ
      ) public
    open Monoid(vectorMonoid)
      renaming (
        id to 𝟎ᵥ ;
        binaryOperator     to [+ᵥ]-binaryOperator ;
        associativity       to [+ᵥ]-associativity ;
        identity-existence  to [+ᵥ]-identity-existence ;
        identity            to [+ᵥ]-identity ;
        identityₗ           to [+ᵥ]-identityₗ ;
        identityᵣ           to [+ᵥ]-identityᵣ
      ) public

    field
      ⦃ [⋅ₛᵥ]-scalarMultiplication ⦄ : ScalarMultiplicationCore
      ⦃ [⋅ₛᵥ]-identity ⦄             : Identityₗ(_⋅ₛᵥ_)(𝟏ₛ)
      ⦃ [⋅ₛᵥ]-absorberₗ ⦄            : ∀{v} → (𝟎ₛ ⋅ₛᵥ v ≡ 𝟎ᵥ)
      ⦃ [⋅ₛᵥ]-absorberᵣ ⦄            : ∀{s} → (s ⋅ₛᵥ 𝟎ᵥ ≡ 𝟎ᵥ)
    open ScalarMultiplicationCore([⋅ₛᵥ]-scalarMultiplication) public

  record Module {ℓₙ₀} : Stmt{ℓₛₑ Lvl.⊔ Lvl.of(S) Lvl.⊔ ℓᵥₑ Lvl.⊔ Lvl.of(V) Lvl.⊔ Lvl.𝐒(ℓₙ₀)} where
    constructor intro
    field
      ⦃ scalarRing ⦄   : Ring(_+ₛ_)(_⋅ₛ_) {ℓₙ₀}
      ⦃ vectorMonoid ⦄ : Monoid(_+ᵥ_)
    open Ring(scalarRing)
      renaming (
        𝟎   to 𝟎ₛ ;
        𝟏   to 𝟏ₛ ;
        _−_ to _−ₛ_ ;
        −_  to −ₛ_ ;
        semiRg                 to scalarSemiRg ;
        rg                     to scalarRg ;
        rng                    to scalarRng ;
        [+]-group              to [+ₛ]-group ;
        [+]-monoid             to [+ₛ]-monoid ;
        [+]-semi               to [+ₛ]-semi ;
        [+]-binaryOperator     to [+ₛ]-binaryOperator ;
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
        [⋅]-monoid             to [⋅ₛ]-monoid ;
        [⋅]-semi               to [⋅ₛ]-semi ;
        [⋅]-binaryOperator     to [⋅ₛ]-binaryOperator ;
        [⋅]-associativity      to [⋅ₛ]-associativity ;
        [⋅]-identity-existence to [⋅ₛ]-identity-existence ;
        [⋅]-identity           to [⋅ₛ]-identity ;
        [⋅]-identityₗ          to [⋅ₛ]-identityₗ ;
        [⋅]-identityᵣ          to [⋅ₛ]-identityᵣ ;
        [⋅][+]-distributivity  to [⋅ₛ][+ₛ]-distributivity ;
        [⋅][+]-distributivityₗ to [⋅ₛ][+ₛ]-distributivityₗ ;
        [⋅][+]-distributivityᵣ to [⋅ₛ][+ₛ]-distributivityᵣ
      ) public
    open Monoid(vectorMonoid)
      renaming (
        id to 𝟎ᵥ ;
        semi                to vectorSemi ;
        binaryOperator     to [+ᵥ]-binaryOperator ;
        associativity       to [+ᵥ]-associativity ;
        identity-existence  to [+ᵥ]-identity-existence ;
        identity            to [+ᵥ]-identity ;
        identityₗ           to [+ᵥ]-identityₗ ;
        identityᵣ           to [+ᵥ]-identityᵣ
      ) public

    field
      ⦃ [⋅ₛᵥ]-scalarMultiplication ⦄ : ScalarMultiplicationCore
      ⦃ [⋅ₛᵥ]-identity ⦄             : Identityₗ(_⋅ₛᵥ_)(Ring.𝟏 scalarRing)

  record VectorSpace {ℓₙ₀} : Stmt{ℓₛₑ Lvl.⊔ Lvl.of(S) Lvl.⊔ ℓᵥₑ Lvl.⊔ Lvl.of(V) Lvl.⊔ Lvl.𝐒(ℓₙ₀)} where
    constructor intro
    field
      ⦃ scalarField ⦄            : Field(_+ₛ_)(_⋅ₛ_) {ℓₙ₀}
      ⦃ vectorCommutativeGroup ⦄ : CommutativeGroup(_+ᵥ_)

    open Field(scalarField)
      renaming (
        𝟎   to 𝟎ₛ ;
        𝟏   to 𝟏ₛ ;
        _−_ to _−ₛ_ ;
        _/_ to _/ₛ_ ;
        −_  to −ₛ_ ;
        ⅟   to ⅟ₛ ;
        semiRg                 to scalarSemiRg ;
        rg                     to scalarRg ;
        rng                    to scalarRng ;
        ring                   to scalarRing ;
        [+]-commutativeGroup   to [+ₛ]-commutativeGroup ;
        [+]-group              to [+ₛ]-group ;
        [+]-monoid             to [+ₛ]-monoid ;
        [+]-semi               to [+ₛ]-semi ;
        [+]-binaryOperator     to [+ₛ]-binaryOperator ;
        [+]-commutativity      to [+ₛ]-commutativity ;
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
        [⋅]-monoid             to [⋅ₛ]-monoid ;
        [⋅]-semi               to [⋅ₛ]-semi ;
        [⋅]-binaryOperator     to [⋅ₛ]-binaryOperator ;
        [⋅]-commutativity      to [⋅ₛ]-commutativity ;
        [⋅]-associativity      to [⋅ₛ]-associativity ;
        [⋅]-identity-existence to [⋅ₛ]-identity-existence ;
        [⋅]-identity           to [⋅ₛ]-identity ;
        [⋅]-identityₗ          to [⋅ₛ]-identityₗ ;
        [⋅]-identityᵣ          to [⋅ₛ]-identityᵣ ;
        [⋅]-inverseₗ           to [⋅ₛ]-inverseₗ ;
        [⋅]-inverseᵣ           to [⋅ₛ]-inverseᵣ ;
        [⋅][+]-distributivity  to [⋅ₛ][+ₛ]-distributivity ;
        [⋅][+]-distributivityₗ to [⋅ₛ][+ₛ]-distributivityₗ ;
        [⋅][+]-distributivityᵣ to [⋅ₛ][+ₛ]-distributivityᵣ ;
        distinct-identities    to distinct-identitiesₛ
      ) public
    open CommutativeGroup(vectorCommutativeGroup)
      renaming (
        id     to 𝟎ᵥ ;
        inv    to −ᵥ_ ;
        inv-op to _−ᵥ_ ;
        group               to [+ᵥ]-group;
        monoid              to [+ᵥ]-monoid ;
        semi                to [+ᵥ]-semi ;
        binaryOperator     to [+ᵥ]-binaryOperator ;
        commutativity       to [+ᵥ]-commutativity;
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
      ⦃ [⋅ₛᵥ]-scalarMultiplication ⦄ : ScalarMultiplicationCore
      ⦃ [⋅ₛᵥ]-identity ⦄             : Identityₗ(_⋅ₛᵥ_)(𝟏ₛ)
    open ScalarMultiplicationCore([⋅ₛᵥ]-scalarMultiplication) public

record VectorSpaceVObject {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ}
  {S : Type{ℓₛ}} ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (_+ₛ_ : S → S → S)
  (_⋅ₛ_ : S → S → S)
  {ℓₙ₀}
  : Stmt{ℓₛₑ Lvl.⊔ ℓₛ Lvl.⊔ Lvl.𝐒(ℓᵥₑ Lvl.⊔ ℓᵥ Lvl.⊔ ℓₙ₀)}
  where

  constructor intro
  field
    {Vector} : Type{ℓᵥ}
    ⦃ Vector-equiv ⦄ : Equiv{ℓᵥₑ}(Vector)
    _+ᵥ_ : Vector → Vector → Vector
    _⋅ₛᵥ_ : S → Vector → Vector
    ⦃ vectorSpace ⦄ : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) {ℓₙ₀}
  open VectorSpace(vectorSpace) public

record VectorSpaceObject {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ ℓₙ₀} : Stmt{Lvl.𝐒(ℓₛₑ Lvl.⊔ ℓₛ Lvl.⊔ ℓᵥₑ Lvl.⊔ ℓᵥ Lvl.⊔ ℓₙ₀)} where
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
    ⦃ vectorSpace ⦄ : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) {ℓₙ₀}
  open VectorSpace(vectorSpace) public
