module Structure.Set.Operators where

open import Data.Boolean
open import Data.Boolean.Stmt
open import Functional
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Function
open import Structure.Relator
open import Structure.Setoid using (Equiv) renaming (_≡_ to _≡ₛ_ ; _≢_ to _≢ₛ_)
import      Structure.Set.Names as Names
open import Structure.Set.Relators using (SubsetRelation)
open import Type

private variable ℓ ℓₗ ℓₗ₁ ℓₗ₂ ℓᵣ ℓᵣₑₗ ℓₒ ℓₛ : Lvl.Level
private variable A B C S S₁ S₂ Sₒ Sᵢ Sₗ Sᵣ E E₁ E₂ Eₗ Eᵣ I O : Type{ℓ}
private variable _∈_ _∈ₒ_ _∈ᵢ_ : E → S → Stmt{ℓₗ}
private variable _∈ₗ_ : E → Sₗ → Stmt{ℓₗ}
private variable _∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}
private variable _⊆_ : Sₗ → Sᵣ → Stmt{ℓᵣ}

private variable ⦃ equiv-I ⦄ : Equiv{ℓₗ}(I)
private variable ⦃ equiv-E ⦄ : Equiv{ℓₗ}(E)
private variable ⦃ equiv-Eₗ ⦄ : Equiv{ℓₗ}(Eₗ)
private variable ⦃ equiv-Eᵣ ⦄ : Equiv{ℓₗ}(Eᵣ)
private variable ⦃ equiv-O ⦄ : Equiv{ℓₗ}(O)
private variable ⦃ sub ⦄ : SubsetRelation(_∈ₗ_)(_∈ᵣ_)(_⊆_)

module _ (_∈_ : E → S → Stmt{ℓₗ}) where
  record EmptySet(∅ : S) : Type{Lvl.of(E) Lvl.⊔ ℓₗ} where
    constructor intro
    field membership : Names.EmptyMembership(_∈_)(∅)

  record UniversalSet(𝐔 : S) : Type{Lvl.of(E) Lvl.⊔ ℓₗ} where
    constructor intro
    field membership : Names.UniversalMembership(_∈_)(𝐔)

  module _ ⦃ equiv-I : Equiv{ℓₗ₁}(I) ⦄ ⦃ equiv-E : Equiv{ℓₗ₂}(E) ⦄ where
    record ImageFunction(⊶ : (f : I → E) → ⦃ func : Function(f) ⦄ → S) : Type{Lvl.of(E) Lvl.⊔ Lvl.of(I) Lvl.⊔ ℓₗ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
      constructor intro
      field membership : Names.ImageMembership(_∈_)(⊶)

  module _ ⦃ equiv-E : Equiv{ℓₗ₁}(E) ⦄ {O : Type{ℓ}} ⦃ equiv-O : Equiv{ℓₗ₂}(O) ⦄ where
    record FiberFunction(fiber : (f : E → O) → ⦃ func : Function(f) ⦄ → (O → S)) : Type{Lvl.of(E) Lvl.⊔ ℓ Lvl.⊔ ℓₗ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
      constructor intro
      field membership : Names.FiberMembership(_∈_)(fiber)

  module _ ⦃ equiv-E : Equiv{ℓₗ}(E) ⦄ where
    record SingletonFunction(singleton : E → S) : Type{Lvl.of(E) Lvl.⊔ ℓₗ} where
      constructor intro
      field membership : Names.SingletonMembership(_∈_)(singleton)

    record PairFunction(pair : E → E → S) : Type{Lvl.of(E) Lvl.⊔ ℓₗ} where
      constructor intro
      field membership : Names.PairMembership(_∈_)(pair)

    record ComprehensionFunction(comp : (P : E → Stmt{ℓ}) ⦃ unaryRelator : UnaryRelator(P) ⦄ → S) : Type{Lvl.of(E) Lvl.⊔ ℓₗ Lvl.⊔ Lvl.𝐒(ℓ)} where
      constructor intro
      field membership : Names.ComprehensionMembership(_∈_)(comp)

module _ (_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}) where
  record ComplementOperator(∁ : Sₗ → Sᵣ) : Type{Lvl.of(E) Lvl.⊔ Lvl.of(Sₗ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ} where
    constructor intro
    field membership : Names.ComplementMembership(_∈ₗ_)(_∈ᵣ_)(∁)

  module _ ⦃ equiv-E : Equiv{ℓₗ}(E) ⦄ where
    record AddOperator(add : E → Sₗ → Sᵣ) : Type{Lvl.of(E) Lvl.⊔ Lvl.of(Sₗ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ} where
      constructor intro
      field membership : Names.AddMembership(_∈ₗ_)(_∈ᵣ_)(add)

    record RemoveOperator(remove : E → Sₗ → Sᵣ) : Type{Lvl.of(E) Lvl.⊔ Lvl.of(Sₗ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ} where
      constructor intro
      field membership : Names.RemoveMembership(_∈ₗ_)(_∈ᵣ_)(remove)

    record FilterFunction(filter : (P : E → Stmt{ℓ}) ⦃ unaryRelator : UnaryRelator(P) ⦄ → (Sₗ → Sᵣ)) : Type{Lvl.of(E) Lvl.⊔ Lvl.of(Sₗ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ Lvl.⊔ Lvl.𝐒(ℓ)} where
      constructor intro
      field membership : Names.FilterMembership(_∈ₗ_)(_∈ᵣ_)(filter)

  record BooleanFilterFunction(boolFilter : (E → Bool) → (Sₗ → Sᵣ)) : Type{Lvl.of(E) Lvl.⊔ Lvl.of(Sₗ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ} where
    constructor intro
    field membership : Names.BooleanFilterMembership(_∈ₗ_)(_∈ᵣ_)(boolFilter)

  record IndexedBigUnionOperator(⋃ᵢ : (I → Sₗ) → Sᵣ) : Type{Lvl.of(E) Lvl.⊔ Lvl.of(Sₗ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ Lvl.⊔ Lvl.of(I)} where
    constructor intro
    field membership : Names.IndexedBigUnionMembership(_∈ₗ_)(_∈ᵣ_)(⋃ᵢ)

  record IndexedBigIntersectionOperator(⋂ᵢ : (I → Sₗ) → Sᵣ) : Type{Lvl.of(E) Lvl.⊔ Lvl.of(Sₗ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ Lvl.⊔ Lvl.of(I)} where
    constructor intro
    field membership : Names.IndexedBigIntersectionMembership(_∈ₗ_)(_∈ᵣ_)(⋂ᵢ)

module _ (_∈ₗ_ : Eₗ → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : Eᵣ → Sᵣ → Stmt{ℓᵣ}) where
  module _ ⦃ equiv-Eₗ : Equiv{ℓₗ₁}(Eₗ) ⦄ ⦃ equiv-Eᵣ : Equiv{ℓₗ₂}(Eᵣ) ⦄ where
    record MapFunction(map : (f : Eₗ → Eᵣ) ⦃ func : Function(f) ⦄ → (Sₗ → Sᵣ)) : Type{Lvl.of(Eₗ) Lvl.⊔ Lvl.of(Eᵣ) Lvl.⊔ Lvl.of(Sₗ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
      constructor intro
      field membership : Names.MapMembership(_∈ₗ_)(_∈ᵣ_)(map)

    record UnmapFunction(unmap : (f : Eₗ → Eᵣ) ⦃ func : Function(f) ⦄ → (Sᵣ → Sₗ)) : Type{Lvl.of(Eₗ) Lvl.⊔ Lvl.of(Eᵣ) Lvl.⊔ Lvl.of(Sᵣ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
      constructor intro
      field membership : Names.UnmapMembership(_∈ₗ_)(_∈ᵣ_)(unmap)

module _ (_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}) (_∈ₒ_ : E → Sₒ → Stmt{ℓₒ}) where
  record LogicalOperator{ℓ} (_△_ : Stmt{ℓₗ} → Stmt{ℓᵣ} → Stmt{ℓ}) (_▫_ : Sₗ → Sᵣ → Sₒ) : Type{Lvl.of(E) Lvl.⊔ Lvl.of(Sₗ) Lvl.⊔ Lvl.of(Sᵣ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ Lvl.⊔ ℓₒ Lvl.⊔ ℓ} where
    constructor intro
    field membership : Names.LogicalOperatorMembership(_∈ₗ_)(_∈ᵣ_)(_∈ₒ_)(_△_)(_▫_)

  UnionOperator        = LogicalOperator(_∨_)
  IntersectionOperator = LogicalOperator(_∧_)
  WithoutOperator      = LogicalOperator(\A B → A ∧ ¬ B)

module _ {_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}} {_∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}} {_∈ₒ_ : E → Sₒ → Stmt{ℓₒ}} where
  module UnionOperator        = LogicalOperator{_∈ₗ_ = _∈ₗ_}{_∈ᵣ_ = _∈ᵣ_}{_∈ₒ_ = _∈ₒ_} {_△_ = _∨_}
  module IntersectionOperator = LogicalOperator{_∈ₗ_ = _∈ₗ_}{_∈ᵣ_ = _∈ᵣ_}{_∈ₒ_ = _∈ₒ_} {_△_ = _∧_}
  module WithoutOperator      = LogicalOperator{_∈ₗ_ = _∈ₗ_}{_∈ᵣ_ = _∈ᵣ_}{_∈ₒ_ = _∈ₒ_} {_△_ = \A B → A ∧ ¬ B}

module _ (_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}) (_∈ₒ_ : Sₗ → Sₒ → Stmt{ℓₒ}) {_⊆_ : Sₗ → Sᵣ → Stmt{ℓₛ}} ⦃ sub : SubsetRelation(_∈ₗ_)(_∈ᵣ_)(_⊆_) ⦄ where
  record PowerFunction(℘ : Sᵣ → Sₒ) : Type{Lvl.of(Sₗ) Lvl.⊔ Lvl.of(Sᵣ) Lvl.⊔ ℓₛ Lvl.⊔ ℓₒ} where
    constructor intro
    field membership : Names.PowerMembership(_∈ₒ_)(_⊆_)(℘)

module _ (_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : Sₗ → Sᵣ → Stmt{ℓᵣ}) (_∈ₒ_ : E → Sₒ → Stmt{ℓₒ}) where
  record BigUnionOperator(⋃ : Sᵣ → Sₒ) : Type{Lvl.of(E) Lvl.⊔ Lvl.of(Sₗ) Lvl.⊔ Lvl.of(Sᵣ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ Lvl.⊔ ℓₒ} where
    constructor intro
    field membership : Names.BigUnionMembership(_∈ₗ_)(_∈ᵣ_)(_∈ₒ_)(⋃)

  record BigIntersectionOperator(⋂ : Sᵣ → Sₒ) : Type{Lvl.of(E) Lvl.⊔ Lvl.of(Sₗ) Lvl.⊔ Lvl.of(Sᵣ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ Lvl.⊔ ℓₒ} where
    constructor intro
    field membership : Names.BigIntersectionMembership(_∈ₗ_)(_∈ᵣ_)(_∈ₒ_)(⋂)

module _ ⦃ p : ∃(EmptySet(_∈_)) ⦄ where
  open ∃(p) using () renaming (witness to ∅) public
  open EmptySet([∃]-proof p) using () renaming (membership to [∅]-membership) public

module _ ⦃ p : ∃(UniversalSet(_∈_)) ⦄ where
  open ∃(p) using () renaming (witness to 𝐔) public
  open UniversalSet([∃]-proof p) using () renaming (membership to [𝐔]-membership) public

module _ ⦃ p : ∃(ImageFunction(_∈_) ⦃ equiv-I ⦄ ⦃ equiv-E ⦄) ⦄ where
  open ∃(p) using () renaming (witness to ⊶) public
  open ImageFunction([∃]-proof p) using () renaming (membership to [⊶]-membership) public

module _ ⦃ p : ∃(FiberFunction(_∈_) ⦃ equiv-E ⦄ ⦃ equiv-O ⦄) ⦄ where
  open ∃(p) using () renaming (witness to fiber) public
  open FiberFunction([∃]-proof p) using () renaming (membership to Fiber-membership) public

module _ ⦃ p : ∃(SingletonFunction(_∈_) ⦃ equiv-E ⦄) ⦄ where
  open ∃(p) using () renaming (witness to singleton) public
  open SingletonFunction([∃]-proof p) using () renaming (membership to Singleton-membership) public

module _ ⦃ p : ∃(PairFunction(_∈_) ⦃ equiv-E ⦄) ⦄ where
  open ∃(p) using () renaming (witness to pair) public
  open PairFunction([∃]-proof p) using () renaming (membership to Pair-membership) public

module _ ⦃ p : ∃(ComplementOperator(_∈ₗ_)(_∈ᵣ_)) ⦄ where
  open ∃(p) using () renaming (witness to ∁) public
  open ComplementOperator([∃]-proof p) using () renaming (membership to [∁]-membership) public

module _ ⦃ p : ∃(AddOperator(_∈ₗ_)(_∈ᵣ_) ⦃ equiv-E ⦄) ⦄ where
  open ∃(p) using () renaming (witness to add) public
  open AddOperator([∃]-proof p) using () renaming (membership to Add-membership) public

module _ ⦃ p : ∃(RemoveOperator(_∈ₗ_)(_∈ᵣ_) ⦃ equiv-E ⦄) ⦄ where
  open ∃(p) using () renaming (witness to remove) public
  open RemoveOperator([∃]-proof p) using () renaming (membership to Remove-membership) public

module _ ⦃ p : ∃(FilterFunction(_∈ₗ_)(_∈ᵣ_) ⦃ equiv-E ⦄ {ℓ}) ⦄ where
  open ∃(p) using () renaming (witness to filter) public
  open FilterFunction([∃]-proof p) using () renaming (membership to Filter-membership) public

module _ ⦃ p : ∃(BooleanFilterFunction(_∈ₗ_)(_∈ᵣ_)) ⦄ where
  open ∃(p) using () renaming (witness to boolFilter) public
  open BooleanFilterFunction([∃]-proof p) using () renaming (membership to BooleanFilter-membership) public

module _ ⦃ p : ∃(IndexedBigUnionOperator(_∈ₗ_)(_∈ᵣ_) {I = I}) ⦄ where
  open ∃(p) using () renaming (witness to ⋃ᵢ) public
  open IndexedBigUnionOperator([∃]-proof p) using () renaming (membership to [⋃ᵢ]-membership) public

module _ ⦃ p : ∃(IndexedBigIntersectionOperator(_∈ₗ_)(_∈ᵣ_) {I = I}) ⦄ where
  open ∃(p) using () renaming (witness to ⋂ᵢ) public
  open IndexedBigIntersectionOperator([∃]-proof p) using () renaming (membership to [⋂ᵢ]-membership) public

module _ ⦃ p : ∃(MapFunction(_∈ₗ_)(_∈ᵣ_) ⦃ equiv-Eₗ ⦄ ⦃ equiv-Eᵣ ⦄) ⦄ where
  open ∃(p) using () renaming (witness to map) public
  open MapFunction([∃]-proof p) using () renaming (membership to Map-membership) public

module _ ⦃ p : ∃(UnmapFunction(_∈ₗ_)(_∈ᵣ_) ⦃ equiv-Eₗ ⦄ ⦃ equiv-Eᵣ ⦄) ⦄ where
  open ∃(p) using () renaming (witness to unmap) public
  open UnmapFunction([∃]-proof p) using () renaming (membership to Unmap-membership) public

module _ ⦃ p : ∃(UnionOperator(_∈ₗ_)(_∈ᵣ_)(_∈ₒ_)) ⦄ where
  open ∃(p) using () renaming (witness to _∪_) public
  open UnionOperator([∃]-proof p) using () renaming (membership to [∪]-membership) public

module _ ⦃ p : ∃(IntersectionOperator(_∈ₗ_)(_∈ᵣ_)(_∈ₒ_)) ⦄ where
  open ∃(p) using () renaming (witness to _∩_) public
  open IntersectionOperator([∃]-proof p) using () renaming (membership to [∩]-membership) public

module _ ⦃ p : ∃(WithoutOperator(_∈ₗ_)(_∈ᵣ_)(_∈ₒ_)) ⦄ where
  open ∃(p) using () renaming (witness to _∖_) public
  open WithoutOperator([∃]-proof p) using () renaming (membership to [∖]-membership) public

module _ ⦃ p : ∃(PowerFunction(_∈ₗ_)(_∈ᵣ_)(_∈ₒ_) ⦃ sub ⦄) ⦄ where
  open ∃(p) using () renaming (witness to ℘) public
  open PowerFunction([∃]-proof p) using () renaming (membership to [℘]-membership) public

module _ ⦃ p : ∃(BigUnionOperator(_∈ₗ_)(_∈ᵣ_)(_∈ₒ_)) ⦄ where
  open ∃(p) using () renaming (witness to ⋃) public
  open BigUnionOperator([∃]-proof p) using () renaming (membership to [⋃]-membership) public

module _ ⦃ p : ∃(BigIntersectionOperator(_∈ₗ_)(_∈ᵣ_)(_∈ₒ_)) ⦄ where
  open ∃(p) using () renaming (witness to ⋂) public
  open BigIntersectionOperator([∃]-proof p) using () renaming (membership to [⋂]-membership) public
