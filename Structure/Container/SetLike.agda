module Structure.Container.SetLike where

open import Data.Boolean
open import Data.Boolean.Stmt
open import Functional
open import Lang.Instance
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid.WithLvl renaming (_≡_ to _≡ₛ_ ; _≢_ to _≢ₛ_)
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Relator hiding (module Names)
open import Type.Properties.Inhabited
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ₉ ℓ₁₀ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level
private variable A B C C₁ C₂ Cₒ Cᵢ E E₁ E₂ : Type{ℓ}
private variable _∈_ _∈ₒ_ _∈ᵢ_ : E → C

module _ {C : Type{ℓ₁}} {E : Type{ℓ₂}} (_∈_ : E → C → Stmt{ℓ₃}) where
  record SetLike : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃ Lvl.⊔ Lvl.𝐒(ℓ₄ Lvl.⊔ ℓ₅)} where
    field
      _⊆_ : C → C → Stmt{ℓ₄}
      _≡_ : C → C → Stmt{ℓ₅}

    field
      [⊆]-membership : ∀{a b} → (a ⊆ b) ↔ (∀{x} → (x ∈ a) → (x ∈ b))
      [≡]-membership : ∀{a b} → (a ≡ b) ↔ (∀{x} → (x ∈ a) ↔ (x ∈ b))

    _∋_ : C → E → Stmt
    _∋_ = swap(_∈_)

    _⊇_ : C → C → Stmt
    _⊇_ = swap(_⊆_)

    _∉_ : E → C → Stmt
    _∉_ = (¬_) ∘₂ (_∈_)

    _⊈_ : C → C → Stmt
    _⊈_ = (¬_) ∘₂ (_⊆_)

    _⊉_ : C → C → Stmt
    _⊉_ = (¬_) ∘₂ (_⊇_)

    _≢_ : C → C → Stmt
    _≢_ = (¬_) ∘₂ (_≡_)

  -- A type such that its inhabitants is the elements of the set `S`.
  SetElement : C → Stmt
  SetElement(S) = ∃(_∈ S)

  module FunctionProperties where
    module Names where
      _closed-under₁_ : C → (E → E) → Stmt -- TODO: Maybe possible to generalize over n
      S closed-under₁ f = (∀{x} → (x ∈ S) → (f(x) ∈ S))

      _closed-under₂_ : C → (E → E → E) → Stmt
      S closed-under₂ (_▫_) = (∀{x y} → (x ∈ S) → (y ∈ S) → ((x ▫ y) ∈ S))

    open import Lang.Instance
    module _ (S : C) (f : E → E) where
      record _closed-under₁_ : Stmt{Lvl.of(S Names.closed-under₁ f)} where
        constructor intro
        field proof : S Names.closed-under₁ f
      _closureUnder₁_ = inst-fn _closed-under₁_.proof

    module _ (S : C) (_▫_ : E → E → E) where
      record _closed-under₂_ : Stmt{Lvl.of(S Names.closed-under₂ (_▫_))} where
        constructor intro
        field proof : S Names.closed-under₂ (_▫_)
      _closureUnder₂_ = inst-fn _closed-under₂_.proof

module _ (_∈_ : _) ⦃ setLike : SetLike{ℓ₁}{ℓ₂}{ℓ₃}{C}{E} (_∈_) {ℓ₄}{ℓ₅} ⦄ where
  open SetLike(setLike)

  record EmptySet : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    field ∅ : C
    Membership = ∀{x} → (x ∉ ∅)
    field membership : Membership
  open EmptySet ⦃ ... ⦄ hiding (Membership ; membership) public
  module Empty ⦃ inst ⦄ = EmptySet(inst)
  {-# DISPLAY EmptySet.∅ = ∅ #-}

  record UniversalSet : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    field 𝐔 : C
    Membership = ∀{x} → (x ∈ 𝐔)
    field membership : Membership
  open UniversalSet ⦃ ... ⦄ hiding (Membership ; membership) public
  module Universal ⦃ inst ⦄ = UniversalSet(inst)

  record UnionOperator : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    field _∪_ : C → C → C
    Membership = ∀{a b}{x} → (x ∈ (a ∪ b)) ↔ ((x ∈ a) ∨ (x ∈ b))
    field membership : Membership
  open UnionOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module Union ⦃ inst ⦄ = UnionOperator(inst)

  record IntersectionOperator : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    field _∩_ : C → C → C
    Membership = ∀{a b}{x} → (x ∈ (a ∩ b)) ↔ ((x ∈ a) ∧ (x ∈ b))
    field membership : Membership
  open IntersectionOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module Intersection ⦃ inst ⦄ = IntersectionOperator(inst)
  {-# DISPLAY IntersectionOperator._∩_ = _∩_ #-}

  record WithoutOperator : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    field _∖_ : C → C → C
    Membership = ∀{a b}{x} → (x ∈ (a ∖ b)) ↔ ((x ∈ a) ∧ (x ∉ b))
    field membership : Membership
  open WithoutOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module Without ⦃ inst ⦄ = WithoutOperator(inst)

  record ComplementOperator : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    field ∁ : C → C
    Membership = ∀{a}{x} → (x ∈ (∁ a)) ↔ (x ∉ a)
    field membership : Membership
  open ComplementOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module Complement ⦃ inst ⦄ = ComplementOperator(inst)

  module _ {I : Type{ℓ}} ⦃ equiv-I : Equiv{ℓₗ₁}(I) ⦄ ⦃ equiv-E : Equiv{ℓₗ₂}(E) ⦄ where
    record ImageOperator : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃ Lvl.⊔ ℓ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
      field ⊶ : (f : I → E) → ⦃ func : Function(f) ⦄ → C
      Membership = ∀{f} ⦃ func : Function(f) ⦄ → ∀{y} → (y ∈ (⊶ f)) ↔ ∃(x ↦ f(x) ≡ₛ y)
      field membership : Membership
    open ImageOperator ⦃ ... ⦄ hiding (Membership ; membership) public
    module Image ⦃ inst ⦄ = ImageOperator(inst)

  module _ ⦃ _ : Equiv{ℓₗ}(E) ⦄ where
    record SingletonSet : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃ Lvl.⊔ ℓₗ} where
      field singleton : E → C
      Membership = ∀{y}{x} → (x ∈ singleton(y)) ↔ (x ≡ₛ y)
      field membership : Membership
    open SingletonSet ⦃ ... ⦄ hiding (Membership ; membership) public
    module Singleton ⦃ inst ⦄ = SingletonSet(inst)

    record PairSet : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃ Lvl.⊔ ℓₗ} where
      field pair : E → E → C
      Membership = ∀{y₁ y₂}{x} → (x ∈ pair y₁ y₂) ↔ (x ≡ₛ y₁)∨(x ≡ₛ y₂)
      field membership : Membership
    open PairSet ⦃ ... ⦄ hiding (Membership ; membership) public
    module Pair ⦃ inst ⦄ = PairSet(inst)

    record AddFunction : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃ Lvl.⊔ ℓₗ} where
      field add : E → C → C
      Membership = ∀{y}{a}{x} → (x ∈ add y a) ↔ ((x ∈ a) ∨ (x ≡ₛ y))
      field membership : Membership
    open AddFunction ⦃ ... ⦄ hiding (Membership ; membership) public
    module Add ⦃ inst ⦄ = AddFunction(inst)

    record RemoveFunction : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃ Lvl.⊔ ℓₗ} where
      field remove : E → C → C
      Membership = ∀{y}{a}{x} → (x ∈ remove y a) ↔ ((x ∈ a) ∧ (x ≢ₛ y))
      field membership : Membership
    open RemoveFunction ⦃ ... ⦄ hiding (Membership ; membership) public
    module Remove ⦃ inst ⦄ = RemoveFunction(inst)

    module _ {ℓ} where
      record FilterFunction : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃ Lvl.⊔ Lvl.𝐒(ℓ) Lvl.⊔ ℓₗ} where
        field filter : (P : E → Stmt{ℓ}) ⦃ unaryRelator : UnaryRelator(P) ⦄ → (C → C)
        Membership = ∀{A}{P} ⦃ unaryRelator : UnaryRelator(P) ⦄ {x} → (x ∈ filter P(A)) ↔ ((x ∈ A) ∧ P(x))
        field membership : Membership
      open FilterFunction ⦃ ... ⦄ hiding (Membership ; membership) public
      module Filter ⦃ inst ⦄ = FilterFunction(inst)

  record BooleanFilterFunction : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    field boolFilter : (E → Bool) → (C → C)
    Membership = ∀{A}{P}{x} → (x ∈ boolFilter P(A)) ↔ ((x ∈ A) ∧ IsTrue(P(x)))
    field membership : Membership
  open BooleanFilterFunction ⦃ ... ⦄ hiding (Membership ; membership) public
  module BooleanFilter ⦃ inst ⦄ = BooleanFilterFunction(inst)

module _ (_∈_ : _) ⦃ setLike : SetLike{ℓ₁}{ℓ₂}{ℓ₃}{C}{E} (_∈_) {ℓ₄}{ℓ₅} ⦄ ⦃ equiv-E : Equiv{ℓₗ₁}(E) ⦄ {O : Type{ℓ₆}} ⦃ equiv-O : Equiv{ℓₗ₂}(O) ⦄ where
  record UnapplyFunction : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃ Lvl.⊔ ℓ₆ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
    field unapply : (f : E → O) ⦃ func : Function(f) ⦄ → O → C
    Membership = ∀{f} ⦃ func : Function(f) ⦄ {y}{x} → (x ∈ unapply f(y)) ↔ (f(x) ≡ₛ y)
    field membership : Membership
  open UnapplyFunction ⦃ ... ⦄ hiding (Membership ; membership) public
  module Unapply ⦃ inst ⦄ = UnapplyFunction(inst)

module _
  ⦃ equiv-E₁ : Equiv{ℓₗ₁}(E₁) ⦄
  (_∈₁_ : _) ⦃ setLike₁ : SetLike{ℓ₁}{ℓ₂}{ℓ₃}{C₁}{E₁} (_∈₁_) {ℓ₄}{ℓ₅} ⦄
  ⦃ equiv-E₂ : Equiv{ℓₗ₂}(E₂) ⦄
  (_∈₂_ : _) ⦃ setLike₂ : SetLike{ℓ₆}{ℓ₇}{ℓ₈}{C₂}{E₂} (_∈₂_) {ℓ₉}{ℓ₁₀} ⦄
  where

  open SetLike ⦃ … ⦄
  record MapFunction : Type{ℓₗ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃ Lvl.⊔ ℓ₆ Lvl.⊔ ℓ₇ Lvl.⊔ ℓ₈} where
    field map : (f : E₁ → E₂) ⦃ func : Function(f) ⦄ → (C₁ → C₂)
    Membership = ∀{f} ⦃ func : Function(f) ⦄ {A}{y} → (y ∈₂ map f(A)) ↔ ∃(x ↦ (x ∈₁ A) ∧ (f(x) ≡ₛ y))
    field membership : Membership
  open MapFunction ⦃ ... ⦄ hiding (Membership ; membership) public
  module Map ⦃ inst ⦄ = MapFunction(inst)

  record UnmapFunction : Type{ℓₗ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃ Lvl.⊔ ℓ₆ Lvl.⊔ ℓ₇ Lvl.⊔ ℓ₈} where
    field unmap : (f : E₁ → E₂) ⦃ func : Function(f) ⦄ → (C₂ → C₁)
    Membership = ∀{f} ⦃ func : Function(f) ⦄ {A}{x} → (x ∈₁ unmap f(A)) ↔ (f(x) ∈₂ A)
    field membership : Membership
  open UnmapFunction ⦃ ... ⦄ hiding (Membership ; membership) public
  module Unmap ⦃ inst ⦄ = UnmapFunction(inst)

module _ (_∈ₒ_ : _) ⦃ outer-setLike : SetLike{ℓ₁}{ℓ₂}{ℓ₃}{Cₒ}{Cᵢ} (_∈ₒ_) {ℓ₄}{ℓ₅} ⦄ (_∈ᵢ_ : _) ⦃ inner-setLike : SetLike{ℓ₂}{ℓ₆}{ℓ₇}{Cᵢ}{E} (_∈ᵢ_) {ℓ₈}{ℓ₉} ⦄ where
  open SetLike ⦃ … ⦄

  record PowerFunction : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃ Lvl.⊔ ℓ₈} where
    field ℘ : Cᵢ → Cₒ
    Membership = ∀{A x} → (x ∈ₒ ℘(A)) ↔ (x ⊆ A)
    field membership : Membership
  open PowerFunction ⦃ ... ⦄ hiding (Membership ; membership) public
  module Power ⦃ inst ⦄ = PowerFunction(inst)

  record BigUnionOperator : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃ Lvl.⊔ ℓ₆ Lvl.⊔ ℓ₇} where
    field ⋃ : Cₒ → Cᵢ
    Membership = ∀{A}{x} → (x ∈ᵢ (⋃ A)) ↔ ∃(a ↦ (a ∈ₒ A) ∧ (x ∈ᵢ a))
    field membership : Membership
  open BigUnionOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module BigUnion ⦃ inst ⦄ = BigUnionOperator(inst)

  record BigIntersectionOperator : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃ Lvl.⊔ ℓ₆ Lvl.⊔ ℓ₇} where
    field ⋂ : Cₒ → Cᵢ
    Membership = ∀{A} → ∃(_∈ₒ A) → ∀{x} → (x ∈ᵢ (⋂ A)) ↔ (∀{a} → (a ∈ₒ A) → (x ∈ᵢ a))
    field membership : Membership
  open BigIntersectionOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module BigIntersection ⦃ inst ⦄ = BigIntersectionOperator(inst)

module _ {I : Type{ℓ}} ⦃ equiv-I : Equiv{ℓₗ₁}(I) ⦄ ⦃ equiv-E : Equiv{ℓₗ₂}(E) ⦄ (_∈_ : _) ⦃ setLike : SetLike{ℓ₁}{ℓ₂}{ℓ₃}{C}{E} (_∈_) {ℓ₄}{ℓ₅} ⦄ where
  record IndexedBigUnionOperator : Type{ℓ Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    field ⋃ᵢ : (I → C) → C
    Membership = ∀{Ai}{x} → (x ∈ (⋃ᵢ Ai)) ↔ ∃(i ↦ (x ∈ Ai(i)))
    field membership : Membership
  open IndexedBigUnionOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module IndexedBigUnion ⦃ inst ⦄ = IndexedBigUnionOperator(inst)

  record IndexedBigIntersectionOperator : Type{ℓ Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    field ⋂ᵢ : (I → C) → C
    Membership = ∀{Ai} → ◊(I) → ∀{x} → (x ∈ (⋂ᵢ Ai)) ↔ (∀{i} → (x ∈ Ai(i)))
    field membership : Membership
  open IndexedBigIntersectionOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module IndexedBigIntersection ⦃ inst ⦄ = IndexedBigIntersectionOperator(inst)

{-
open SetLike ⦃ … ⦄
  using (
    _∈_ ; _⊆_ ; _≡_ ;
    _∋_ ; _⊇_ ;
    _∉_ ; _⊈_ ; _⊉_ ; _≢_ ;
    ∅ ; _∪_ ; _∩_ ; _∖_ ;
    singleton ; add ; remove
  )
-}
