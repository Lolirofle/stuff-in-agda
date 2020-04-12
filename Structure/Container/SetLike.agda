module Structure.Container.SetLike where

open import Data.Boolean
open import Data.Boolean.Stmt
open import Functional
open import Lang.Instance
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid.WithLvl using (Equiv ; Function ; UnaryRelator ; BinaryRelator ; substitute₁ ; substitute₂ ; [≡]-with ; binaryRelator) renaming (_≡_ to _≡ₛ_ ; _≢_ to _≢ₛ_)
open import Structure.Function.Domain
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level
private variable A B C E : Type{ℓ}
private variable _∈_ : E → C

module _ {C : Type{ℓ₁}} {E : Type{ℓ₂}} (_∈_ : E → C → Stmt{ℓ₃}) where
  record SetLike : Type{ℓ₁ ⊔ ℓ₂ ⊔ Lvl.𝐒(ℓ₃)} where
    field
      _⊆_ : C → C → Stmt{ℓ₃}
      _≡_ : C → C → Stmt{ℓ₃}

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

module _ ⦃ setLike : SetLike{ℓ₁}{ℓ₂}{ℓ₃}{C}{E} (_∈_) ⦄ where
  open SetLike(setLike)

  record EmptySet : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃} where
    field ∅ : C
    Membership = ∀{x} → (x ∉ ∅)
    field membership : Membership
  open EmptySet ⦃ ... ⦄ hiding (Membership ; membership) public
  module Empty ⦃ inst ⦄ = EmptySet(inst)

  record UniversalSet : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃} where
    field 𝐔 : C
    Membership = ∀{x} → (x ∈ 𝐔)
    field membership : Membership
  open UniversalSet ⦃ ... ⦄ hiding (Membership ; membership) public
  module Universal ⦃ inst ⦄ = UniversalSet(inst)

  record UnionOperator : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃} where
    field _∪_ : C → C → C
    Membership = ∀{a b}{x} → (x ∈ (a ∪ b)) ↔ ((x ∈ a) ∨ (x ∈ b))
    field membership : Membership
  open UnionOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module Union ⦃ inst ⦄ = UnionOperator(inst)

  record IntersectionOperator : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃} where
    field _∩_ : C → C → C
    Membership = ∀{a b}{x} → (x ∈ (a ∩ b)) ↔ ((x ∈ a) ∧ (x ∈ b))
    field membership : Membership
  open IntersectionOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module Intersection ⦃ inst ⦄ = IntersectionOperator(inst)

  record WithoutOperator : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃} where
    field _∖_ : C → C → C
    Membership = ∀{a b}{x} → (x ∈ (a ∖ b)) ↔ ((x ∈ a) ∧ (x ∉ b))
    field membership : Membership
  open WithoutOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module Without ⦃ inst ⦄ = WithoutOperator(inst)

  record ComplementOperator : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃} where
    field ∁ : C → C
    Membership = ∀{a}{x} → (x ∈ (∁ a)) ↔ (x ∉ a)
    field membership : Membership
  open ComplementOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module Complement ⦃ inst ⦄ = ComplementOperator(inst)

  module _ ⦃ _ : Equiv{ℓₗ}(E) ⦄ where
    record SingletonSet : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓₗ} where
      field singleton : E → C
      Membership = ∀{y}{x} → (x ∈ singleton(y)) ↔ (x ≡ₛ y)
      field membership : Membership
    open SingletonSet ⦃ ... ⦄ hiding (Membership ; membership) public
    module Singleton ⦃ inst ⦄ = SingletonSet(inst)

    record PairSet : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓₗ} where
      field pair : E → E → C
      Membership = ∀{y₁ y₂}{x} → (x ∈ pair y₁ y₂) ↔ (x ≡ₛ y₁)∨(x ≡ₛ y₂)
      field membership : Membership
    open PairSet ⦃ ... ⦄ hiding (Membership ; membership) public
    module Pair ⦃ inst ⦄ = PairSet(inst)

    record AddFunction : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓₗ} where
      field add : E → C → C
      Membership = ∀{y}{a}{x} → (x ∈ add y a) ↔ ((x ∈ a) ∨ (x ≡ₛ y))
      field membership : Membership
    open AddFunction ⦃ ... ⦄ hiding (Membership ; membership) public
    module Add ⦃ inst ⦄ = AddFunction(inst)

    record RemoveFunction : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓₗ} where
      field remove : E → C → C
      Membership = ∀{y}{a}{x} → (x ∈ remove y a) ↔ ((x ∈ a) ∧ (x ≢ₛ y))
      field membership : Membership
    open RemoveFunction ⦃ ... ⦄ hiding (Membership ; membership) public
    module Remove ⦃ inst ⦄ = RemoveFunction(inst)

    record MapFunction : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓₗ} where
      field map : (E → E) → (C → C)
      Membership = ∀{A}{f} ⦃ _ : Function(f) ⦄ {y} → (y ∈ map f(A)) ↔ ∃(x ↦ (x ∈ A) ∧ (y ≡ₛ f(x)))
      field membership : Membership
    open MapFunction ⦃ ... ⦄ hiding (Membership ; membership) public
    module Map ⦃ inst ⦄ = MapFunction(inst)

    module _ {ℓ} where
      record FilterFunction : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ Lvl.𝐒(ℓ) ⊔ ℓₗ} where
        field filter : (E → Stmt{ℓ}) → (C → C)
        Membership = ∀{A}{P} ⦃ unaryRelator : UnaryRelator(P) ⦄ {x} → (x ∈ filter P(A)) ↔ ((x ∈ A) ∧ P(x))
        field membership : Membership
      open FilterFunction ⦃ ... ⦄ hiding (Membership ; membership) public
      module Filter ⦃ inst ⦄ = FilterFunction(inst)

  record BooleanFilterFunction : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃} where
    field boolFilter : (E → Bool) → (C → C)
    Membership = ∀{A}{P}{x} → (x ∈ boolFilter P(A)) ↔ ((x ∈ A) ∧ IsTrue(P(x)))
    field membership : Membership
  open BooleanFilterFunction ⦃ ... ⦄ hiding (Membership ; membership) public
  module BooleanFilter ⦃ inst ⦄ = BooleanFilterFunction(inst)

module _ ⦃ setLike : SetLike{ℓ₁}{ℓ₁}{ℓ₂}{C}{C} (_∈_) ⦄ where
  open SetLike(setLike)

  module _ ⦃ _ : Equiv{ℓₗ}(C) ⦄ where
    record PowerFunction : Type{ℓ₁ ⊔ ℓ₂} where
      field ℘ : C → C
      Membership = ∀{A x} → (x ∈ ℘(A)) ↔ (x ⊆ A)
      field membership : Membership
    open BooleanFilterFunction ⦃ ... ⦄ hiding (Membership ; membership) public
    module Power ⦃ inst ⦄ = BooleanFilterFunction(inst)

  record BigUnionOperator : Type{ℓ₁ ⊔ ℓ₂} where
    field ⋃ : C → C
    Membership = ∀{A}{x} → (x ∈ (⋃ A)) ↔ ∃(a ↦ (a ∈ A) ∧ (x ∈ a))
    field membership : Membership
  open BigUnionOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module BigUnion ⦃ inst ⦄ = BigUnionOperator(inst)

  record BigIntersectionOperator : Type{ℓ₁ ⊔ ℓ₂} where
    field ⋂ : C → C
    Membership = ∀{A} → ∃(_∈ A) → ∀{x} → (x ∈ (⋂ A)) ↔ (∀{a} → (a ∈ A) → (x ∈ a))
    field membership : Membership
  open BigIntersectionOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module BigIntersection ⦃ inst ⦄ = BigIntersectionOperator(inst)

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

module Proofs where
  import      Data
  import      Data.Tuple as Tuple
  open import Logic.Predicate.Theorems
  open import Logic.Propositional.Theorems
  open import Structure.Relator.Ordering
  open import Structure.Relator.Proofs
  open import Syntax.Transitivity

  module _ ⦃ setLike : SetLike{ℓ₁}{ℓ₁}{ℓ₂}{C}{C} (_∈_) ⦄ where
    open SetLike(setLike)

    module _ ⦃ _ : Equiv{ℓₗ}(C) ⦄ where
      private
        instance
          big-intersection-filter-unary-relator : ⦃ _ : Equiv{ℓₗ}(E) ⦄ ⦃ _ : BinaryRelator{B = C}(_∈_) ⦄ → ∀{As} → UnaryRelator(\a → ∀{A} → (A ∈ As) → (a ∈ A))
          big-intersection-filter-unary-relator ⦃ [∈]-binaryRelator ⦄ = [∀]-unaryRelator ⦃ rel-P = \{A} → [→]-unaryRelator ⦃ rel-P = const-unaryRelator ⦄ ⦃ rel-Q = BinaryRelator.left (binaryRelator(_∈_)) {A} ⦄ ⦄

      filter-big-union-to-big-intersection : ⦃ _ : BinaryRelator(_∈_) ⦄ ⦃ _ : FilterFunction{ℓ = ℓ₁ ⊔ ℓ₂} ⦄ ⦃ _ : BigUnionOperator ⦄ → BigIntersectionOperator
      BigIntersectionOperator.⋂ filter-big-union-to-big-intersection As = filter(\a → ∀{A} → (A ∈ As) → (a ∈ A))(⋃ As)
      Tuple.left (BigIntersectionOperator.membership filter-big-union-to-big-intersection {As} eAs {a}) p = [↔]-to-[←] Filter.membership ([∧]-intro ([↔]-to-[←] BigUnion.membership ([∃]-map-proof (aAs ↦ [∧]-intro aAs (p aAs)) eAs)) (\{x} → p{x}))
      Tuple.right (BigIntersectionOperator.membership filter-big-union-to-big-intersection {As} eAs {a}) xfilter {A} AAs = [∧]-elimᵣ([↔]-to-[→] Filter.membership xfilter) AAs

    module _
      ⦃ _ : Equiv{ℓₗ}(C) ⦄
      ⦃ _ : BinaryRelator(_∈_) ⦄
      where

      -- Also called: Russell's paradox.
      filter-universal-contradiction : ⦃ _ : FilterFunction{ℓ = ℓ₂} ⦄ ⦃ _ : UniversalSet ⦄ → ⊥
      filter-universal-contradiction = proof-not-in proof-in where
        instance
          filter-unary-relator : UnaryRelator(x ↦ (x ∉ x))
          filter-unary-relator = [¬]-unaryRelator ⦃ rel-P = binary-unaryRelator ⦄

        notInSelf : C
        notInSelf = filter (x ↦ (x ∉ x))(𝐔)

        proof-not-in : (notInSelf ∉ notInSelf)
        proof-not-in pin = [∧]-elimᵣ([↔]-to-[→] Filter.membership pin) pin

        proof-in : (notInSelf ∈ notInSelf)
        proof-in = [↔]-to-[←] Filter.membership ([∧]-intro Universal.membership proof-not-in)

  module _ ⦃ setLike : SetLike{ℓ₁}{ℓ₂}{ℓ₃}{C}{E} (_∈_) ⦄ where
    open SetLike(setLike)

    private variable a b c : C
    private variable x y z : E

    [⊇]-membership : ∀{a b} → (a ⊇ b) ↔ (∀{x} → (x ∈ a) ← (x ∈ b))
    [⊇]-membership = [⊆]-membership

    module _ ⦃ _ : Equiv{ℓₗ}(E) ⦄ where
      pair-to-singleton : ⦃ _ : PairSet ⦄ → SingletonSet
      SingletonSet.singleton  pair-to-singleton e = pair e e
      SingletonSet.membership pair-to-singleton = [↔]-transitivity Pair.membership ([↔]-intro [∨]-introₗ ([∨]-elim id id))

      filter-to-empty : let _ = c in ⦃ _ : FilterFunction{ℓ = Lvl.𝟎} ⦄ → EmptySet
      EmptySet.∅ (filter-to-empty {c = c}) = filter (const ⊥) c
      EmptySet.membership filter-to-empty p = [∧]-elimᵣ ([↔]-to-[→] Filter.membership p)

      module _
        ⦃ _ : Equiv{ℓₗ}(C) ⦄
        ⦃ _ : BinaryRelator(_∈_) ⦄
        where

        filter-to-intersection : ⦃ _ : FilterFunction{ℓ = ℓ₃} ⦄ → IntersectionOperator
        IntersectionOperator._∩_ filter-to-intersection a b = filter (_∈ b) a
        IntersectionOperator.membership filter-to-intersection = Filter.membership ⦃ unaryRelator = BinaryRelator.left infer ⦄

    module _ ⦃ equivalence : Equivalence(_≡_) ⦄ where
      private
        instance
          [≡]-equiv : Equiv{ℓ₃}(C)
          Equiv._≡_ [≡]-equiv = _≡_
          Equiv.[≡]-equivalence [≡]-equiv = equivalence

      module _
        ⦃ _ : Equiv{ℓₗ₂}(E) ⦄
        ⦃ _ : Weak.PartialOrder(_⊆_)(_≡_) ⦄
        ⦃ _ : BinaryRelator(_∈_) ⦄
        ⦃ _ : (_≡_) ⊆₂ (_⊆_) ⦄
        ⦃ _ : (_≡_) ⊆₂ (_⊇_) ⦄
        where

        instance
          [⊆]-binaryRelator : BinaryRelator(_⊆_)
          BinaryRelator.substitution [⊆]-binaryRelator p1 p2 ps = sub₂(_≡_)(_⊇_) p1 🝖 ps 🝖 sub₂(_≡_)(_⊆_) p2

        instance
          [⊇]-binaryRelator : BinaryRelator(_⊇_)
          BinaryRelator.substitution [⊇]-binaryRelator = swap(substitute₂(_⊆_))

    instance
      [≡]-to-[⊆] : (_≡_) ⊆₂ (_⊆_)
      _⊆₂_.proof [≡]-to-[⊆] =
        [↔]-to-[←] [⊆]-membership
        ∘ [∀][→]-distributivity [↔]-to-[→]
        ∘ [↔]-to-[→] [≡]-membership

    instance
      [≡]-to-[⊇] : (_≡_) ⊆₂ (_⊇_)
      _⊆₂_.proof [≡]-to-[⊇] =
        [↔]-to-[←] [⊆]-membership
        ∘ [∀][→]-distributivity [↔]-to-[←]
        ∘ [↔]-to-[→] [≡]-membership

    instance
      [⊆]-reflexivity : Reflexivity(_⊆_)
      Reflexivity.proof [⊆]-reflexivity = [↔]-to-[←] [⊆]-membership [→]-reflexivity

    instance
      [⊆]-antisymmetry : Antisymmetry(_⊆_)(_≡_)
      Antisymmetry.proof [⊆]-antisymmetry ab ba =
        [↔]-to-[←] [≡]-membership ([↔]-intro ([↔]-to-[→] [⊇]-membership ba) ([↔]-to-[→] [⊆]-membership ab))

    instance
      [⊆]-transitivity : Transitivity(_⊆_)
      Transitivity.proof [⊆]-transitivity xy yz =
        [↔]-to-[←] [⊆]-membership ([→]-transitivity ([↔]-to-[→] [⊆]-membership xy) ([↔]-to-[→] [⊆]-membership yz))

    instance
      [⊆]-partialOrder : Weak.PartialOrder(_⊆_)(_≡_)
      [⊆]-partialOrder = Weak.intro

    instance
      [≡]-reflexivity : Reflexivity(_≡_)
      Reflexivity.proof [≡]-reflexivity = [↔]-to-[←] [≡]-membership [↔]-reflexivity

    instance
      [≡]-symmetry : Symmetry(_≡_)
      Symmetry.proof [≡]-symmetry =
        [↔]-to-[←] [≡]-membership
        ∘ [∀][→]-distributivity [↔]-symmetry
        ∘ [↔]-to-[→] [≡]-membership

    instance
      [≡]-transitivity : Transitivity(_≡_)
      Transitivity.proof [≡]-transitivity xy yz = [↔]-to-[←] [≡]-membership ([↔]-transitivity ([↔]-to-[→] [≡]-membership xy) ([↔]-to-[→] [≡]-membership yz))

    instance
      [≡]-equivalence : Equivalence(_≡_)
      [≡]-equivalence = intro
