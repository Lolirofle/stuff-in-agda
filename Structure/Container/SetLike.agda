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
open import Structure.Relator
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ₉ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level
private variable A B C Cₒ Cᵢ E : Type{ℓ}
private variable _∈_ _∈ₒ_ _∈ᵢ_ : E → C

module _ {C : Type{ℓ₁}} {E : Type{ℓ₂}} (_∈_ : E → C → Stmt{ℓ₃}) where
  record SetLike : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ Lvl.𝐒(ℓ₄ ⊔ ℓ₅)} where
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

module _ (_∈_ : _) ⦃ setLike : SetLike{ℓ₁}{ℓ₂}{ℓ₃}{C}{E} (_∈_) {ℓ₄}{ℓ₅} ⦄ where
  open SetLike(setLike)

  record EmptySet : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃} where
    field ∅ : C
    Membership = ∀{x} → (x ∉ ∅)
    field membership : Membership
  open EmptySet ⦃ ... ⦄ hiding (Membership ; membership) public
  module Empty ⦃ inst ⦄ = EmptySet(inst)
  {-# DISPLAY EmptySet.∅ = ∅ #-}

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
  {-# DISPLAY IntersectionOperator._∩_ = _∩_ #-}

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

module _ (_∈ₒ_ : _) ⦃ outer-setLike : SetLike{ℓ₁}{ℓ₂}{ℓ₃}{Cₒ}{Cᵢ} (_∈ₒ_) {ℓ₄}{ℓ₅} ⦄ (_∈ᵢ_ : _) ⦃ inner-setLike : SetLike{ℓ₂}{ℓ₆}{ℓ₇}{Cᵢ}{E} (_∈ᵢ_) {ℓ₈}{ℓ₉} ⦄ where
  open SetLike ⦃ … ⦄

  record PowerFunction : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₈} where
    field ℘ : Cᵢ → Cₒ
    Membership = ∀{A x} → (x ∈ₒ ℘(A)) ↔ (x ⊆ A)
    field membership : Membership
  open PowerFunction ⦃ ... ⦄ hiding (Membership ; membership) public
  module Power ⦃ inst ⦄ = PowerFunction(inst)

  record BigUnionOperator : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₆ ⊔ ℓ₇} where
    field ⋃ : Cₒ → Cᵢ
    Membership = ∀{A}{x} → (x ∈ᵢ (⋃ A)) ↔ ∃(a ↦ (a ∈ₒ A) ∧ (x ∈ᵢ a))
    field membership : Membership
  open BigUnionOperator ⦃ ... ⦄ hiding (Membership ; membership) public
  module BigUnion ⦃ inst ⦄ = BigUnionOperator(inst)

  record BigIntersectionOperator : Type{ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₆ ⊔ ℓ₇} where
    field ⋂ : Cₒ → Cᵢ
    Membership = ∀{A} → ∃(_∈ₒ A) → ∀{x} → (x ∈ᵢ (⋂ A)) ↔ (∀{a} → (a ∈ₒ A) → (x ∈ᵢ a))
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
  import      Data.Either as Either
  import      Data.Tuple as Tuple
  open import Logic.Predicate.Theorems
  open import Logic.Propositional.Theorems
  open import Structure.Relator.Ordering
  open import Structure.Relator.Proofs
  open import Syntax.Transitivity

  module _ ⦃ setLike : SetLike{ℓ₁}{ℓ₁}{ℓ₂}{C}{C} (_∈_) {ℓ₄}{ℓ₅} ⦄ where
    open SetLike(setLike)

    module _ ⦃ _ : Equiv{ℓₗ}(C) ⦄ where
      private
        instance
          big-intersection-filter-unary-relator : ⦃ _ : Equiv{ℓₗ}(E) ⦄ ⦃ _ : BinaryRelator{B = C}(_∈_) ⦄ → ∀{As} → UnaryRelator(\a → ∀{A} → (A ∈ As) → (a ∈ A))
          big-intersection-filter-unary-relator ⦃ [∈]-binaryRelator ⦄ = [∀]-unaryRelator ⦃ rel-P = \{A} → [→]-unaryRelator ⦃ rel-P = const-unaryRelator ⦄ ⦃ rel-Q = BinaryRelator.left (binaryRelator(_∈_)) {A} ⦄ ⦄

      filter-big-union-to-big-intersection : ⦃ _ : BinaryRelator(_∈_) ⦄ ⦃ _ : FilterFunction(_∈_){ℓ = ℓ₁ ⊔ ℓ₂} ⦄ ⦃ _ : BigUnionOperator(_∈_)(_∈_) ⦄ → BigIntersectionOperator(_∈_)(_∈_)
      BigIntersectionOperator.⋂ filter-big-union-to-big-intersection As = filter(\a → ∀{A} → (A ∈ As) → (a ∈ A))(⋃ As)
      Tuple.left (BigIntersectionOperator.membership filter-big-union-to-big-intersection {As} eAs {a}) p = [↔]-to-[←] Filter.membership ([∧]-intro ([↔]-to-[←] BigUnion.membership ([∃]-map-proof (aAs ↦ [∧]-intro aAs (p aAs)) eAs)) (\{x} → p{x}))
      Tuple.right (BigIntersectionOperator.membership filter-big-union-to-big-intersection {As} eAs {a}) xfilter {A} AAs = [∧]-elimᵣ([↔]-to-[→] Filter.membership xfilter) AAs

    module _
      ⦃ _ : Equiv{ℓₗ}(C) ⦄
      ⦃ _ : BinaryRelator(_∈_) ⦄
      where

      -- Also called: Russell's paradox.
      filter-universal-contradiction : ⦃ _ : FilterFunction(_∈_){ℓ = ℓ₂} ⦄ ⦃ _ : UniversalSet(_∈_) ⦄ → ⊥
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

  module _ ⦃ setLike : SetLike{ℓ₁}{ℓ₂}{ℓ₃}{C}{E} (_∈_) {ℓ₄}{ℓ₅} ⦄ where
    open SetLike(setLike)

    private variable a b c : C
    private variable x y z : E

    [⊇]-membership : ∀{a b} → (a ⊇ b) ↔ (∀{x} → (x ∈ a) ← (x ∈ b))
    [⊇]-membership = [⊆]-membership

    module _ ⦃ _ : Equiv{ℓₗ}(E) ⦄ where
      pair-to-singleton : ⦃ _ : PairSet(_∈_) ⦄ → SingletonSet(_∈_)
      SingletonSet.singleton  pair-to-singleton e = pair e e
      SingletonSet.membership pair-to-singleton = [↔]-transitivity Pair.membership ([↔]-intro [∨]-introₗ ([∨]-elim id id))

      filter-to-empty : let _ = c in ⦃ _ : FilterFunction(_∈_){ℓ = Lvl.𝟎} ⦄ → EmptySet(_∈_)
      EmptySet.∅ (filter-to-empty {c = c}) = filter (const ⊥) c
      EmptySet.membership filter-to-empty p = [∧]-elimᵣ ([↔]-to-[→] Filter.membership p)

      module _
        ⦃ _ : Equiv{ℓₗ}(C) ⦄
        ⦃ _ : BinaryRelator(_∈_) ⦄
        where

        filter-to-intersection : ⦃ _ : FilterFunction(_∈_){ℓ = ℓ₃} ⦄ → IntersectionOperator(_∈_)
        IntersectionOperator._∩_ filter-to-intersection a b = filter (_∈ b) a
        IntersectionOperator.membership filter-to-intersection = Filter.membership ⦃ unaryRelator = BinaryRelator.left infer ⦄

    module _ ⦃ equivalence : Equivalence(_≡_) ⦄ where
      private
        instance
          [≡]-equiv : Equiv{ℓ₅}(C)
          Equiv._≡_ [≡]-equiv = _≡_
          Equiv.equivalence [≡]-equiv = equivalence

      [∈]-unaryOperatorᵣ : UnaryRelator(x ∈_)
      UnaryRelator.substitution [∈]-unaryOperatorᵣ xy = [↔]-to-[→] ([↔]-to-[→] [≡]-membership xy)

      module _
        ⦃ _ : Equiv{ℓₗ₂}(E) ⦄
        ⦃ _ : Weak.PartialOrder(_⊆_)(_≡_) ⦄
        ⦃ _ : BinaryRelator(_∈_) ⦄
        ⦃ _ : (_≡_) ⊆₂ (_⊆_) ⦄
        ⦃ _ : (_≡_) ⊆₂ (_⊇_) ⦄
        where

        [⊆]-binaryRelator : BinaryRelator(_⊆_)
        BinaryRelator.substitution [⊆]-binaryRelator p1 p2 ps = sub₂(_≡_)(_⊇_) p1 🝖 ps 🝖 sub₂(_≡_)(_⊆_) p2

        [⊇]-binaryRelator : BinaryRelator(_⊇_)
        BinaryRelator.substitution [⊇]-binaryRelator = swap(substitute₂(_⊆_) ⦃ [⊆]-binaryRelator ⦄)

    [≡]-to-[⊆] : (_≡_) ⊆₂ (_⊆_)
    _⊆₂_.proof [≡]-to-[⊆] =
      [↔]-to-[←] [⊆]-membership
      ∘ [∀][→]-distributivity [↔]-to-[→]
      ∘ [↔]-to-[→] [≡]-membership

    [≡]-to-[⊇] : (_≡_) ⊆₂ (_⊇_)
    _⊆₂_.proof [≡]-to-[⊇] =
      [↔]-to-[←] [⊆]-membership
      ∘ [∀][→]-distributivity [↔]-to-[←]
      ∘ [↔]-to-[→] [≡]-membership

    [⊆]-reflexivity : Reflexivity(_⊆_)
    Reflexivity.proof [⊆]-reflexivity = [↔]-to-[←] [⊆]-membership [→]-reflexivity

    [⊆]-antisymmetry : Antisymmetry(_⊆_)(_≡_)
    Antisymmetry.proof [⊆]-antisymmetry ab ba =
      [↔]-to-[←] [≡]-membership ([↔]-intro ([↔]-to-[→] [⊇]-membership ba) ([↔]-to-[→] [⊆]-membership ab))

    [⊆]-transitivity : Transitivity(_⊆_)
    Transitivity.proof [⊆]-transitivity xy yz =
      [↔]-to-[←] [⊆]-membership ([→]-transitivity ([↔]-to-[→] [⊆]-membership xy) ([↔]-to-[→] [⊆]-membership yz))

    [⊆]-partialOrder : Weak.PartialOrder(_⊆_)(_≡_)
    [⊆]-partialOrder = Weak.intro ⦃ [⊆]-antisymmetry ⦄ ⦃ [⊆]-transitivity ⦄ ⦃ [⊆]-reflexivity ⦄

    [≡]-reflexivity : Reflexivity(_≡_)
    Reflexivity.proof [≡]-reflexivity = [↔]-to-[←] [≡]-membership [↔]-reflexivity

    [≡]-symmetry : Symmetry(_≡_)
    Symmetry.proof [≡]-symmetry =
      [↔]-to-[←] [≡]-membership
      ∘ [∀][→]-distributivity [↔]-symmetry
      ∘ [↔]-to-[→] [≡]-membership

    [≡]-transitivity : Transitivity(_≡_)
    Transitivity.proof [≡]-transitivity xy yz = [↔]-to-[←] [≡]-membership ([↔]-transitivity ([↔]-to-[→] [≡]-membership xy) ([↔]-to-[→] [≡]-membership yz))

    [≡]-equivalence : Equivalence(_≡_)
    [≡]-equivalence = intro ⦃ [≡]-reflexivity ⦄ ⦃ [≡]-symmetry ⦄ ⦃ [≡]-transitivity ⦄

    -- TODO: These are unneccessary if one uses Structure.Operator.SetAlgebra or lattices
    module _ ⦃ _ : EmptySet(_∈_) ⦄ ⦃ _ : UniversalSet(_∈_) ⦄ ⦃ _ : ComplementOperator(_∈_) ⦄ where
      ∁-of-∅ : (∁(∅) ≡ 𝐔)
      ∁-of-∅ = [↔]-to-[←] [≡]-membership ([↔]-intro ([↔]-to-[←] Complement.membership ∘ const Empty.membership) (const Universal.membership))

      ∁-of-𝐔 : (∁(𝐔) ≡ ∅)
      ∁-of-𝐔 = [↔]-to-[←] [≡]-membership ([↔]-intro ([⊥]-elim ∘ Empty.membership) ([⊥]-elim ∘ apply Universal.membership ∘ [↔]-to-[→] Complement.membership))

  module _ ⦃ setLike : SetLike{ℓ₁}{ℓ₂}{ℓ₃}{C}{E} (_∈_) {ℓ₄}{ℓ₅} ⦄ where
    open SetLike(setLike)

    open import Logic.Classical
    open import Structure.Operator.Lattice
    open import Structure.Operator.Properties

    module _ where
      private
        instance
          equiv-C : Equiv{ℓ₅}(C)
          equiv-C = intro(_≡_) ⦃ [≡]-equivalence ⦄

      module _ ⦃ _ : ComplementOperator(_∈_) ⦄ where
        instance
          [∁]-function : Function(∁)
          Function.congruence [∁]-function xy =
            [↔]-to-[←] [≡]-membership (
              Complement.membership 〔 [↔]-transitivity 〕
              [↔]-negationᵣ ([↔]-to-[→] [≡]-membership xy) 〔 [↔]-transitivity 〕
              [↔]-symmetry Complement.membership
            )

        instance
          [∁]-involution : ⦃ _ : ∀{x y} → Classical(x ∈ y) ⦄ → Involution(∁)
          Involution.proof [∁]-involution =
            [↔]-to-[←] [≡]-membership (
              Complement.membership 〔 [↔]-transitivity 〕
              [↔]-negationᵣ Complement.membership 〔 [↔]-transitivity 〕
              [↔]-intro [¬¬]-intro [¬¬]-elim
            )

      module _ ⦃ _ : UnionOperator(_∈_) ⦄ where
        instance
          [∪]-binaryOperator : BinaryOperator(_∪_)
          BinaryOperator.congruence [∪]-binaryOperator xy₁ xy₂ =
            [↔]-to-[←] [≡]-membership (
              Union.membership 〔 [↔]-transitivity 〕
              [↔]-intro (Either.map2 ([↔]-to-[←] ([↔]-to-[→] [≡]-membership xy₁)) ([↔]-to-[←] ([↔]-to-[→] [≡]-membership xy₂))) (Either.map2 ([↔]-to-[→] ([↔]-to-[→] [≡]-membership xy₁)) ([↔]-to-[→] ([↔]-to-[→] [≡]-membership xy₂))) 〔 [↔]-transitivity 〕
              [↔]-symmetry Union.membership
            )

        instance
          [∪]-commutativity : Commutativity(_∪_)
          Commutativity.proof [∪]-commutativity {x} {y} =
            [↔]-to-[←] [≡]-membership (
              Union.membership                    〔 [↔]-transitivity 〕
              [↔]-intro [∨]-symmetry [∨]-symmetry 〔 [↔]-transitivity 〕
              [↔]-symmetry Union.membership
            )

        instance
          [∪]-associativity : Associativity(_∪_)
          Associativity.proof [∪]-associativity {x} {y} =
            [↔]-to-[←] [≡]-membership (
              Union.membership 〔 [↔]-transitivity 〕
              [↔]-intro (Either.mapLeft ([↔]-to-[←] Union.membership)) (Either.mapLeft ([↔]-to-[→] Union.membership)) 〔 [↔]-transitivity 〕
              [∨]-associativity 〔 [↔]-transitivity 〕
              [↔]-symmetry([↔]-intro (Either.mapRight ([↔]-to-[←] Union.membership)) (Either.mapRight ([↔]-to-[→] Union.membership))) 〔 [↔]-transitivity 〕
              [↔]-symmetry Union.membership
            )

        module _ ⦃ _ : EmptySet(_∈_) ⦄ where
          instance
            [∪]-identityₗ : Identityₗ(_∪_)(∅)
            Identityₗ.proof [∪]-identityₗ {x} =
              [↔]-to-[←] [≡]-membership (
                Union.membership 〔 [↔]-transitivity 〕
                [↔]-intro (Either.mapLeft [⊥]-elim) (Either.mapLeft Empty.membership) 〔 [↔]-transitivity 〕
                [↔]-intro [∨]-introᵣ [∨]-identityₗ
              )

      module _ ⦃ _ : IntersectionOperator(_∈_) ⦄ where
        instance
          [∩]-binaryOperator : BinaryOperator(_∩_)
          BinaryOperator.congruence [∩]-binaryOperator xy₁ xy₂ =
            [↔]-to-[←] [≡]-membership (
              Intersection.membership 〔 [↔]-transitivity 〕
              [↔]-intro (Tuple.map ([↔]-to-[←] ([↔]-to-[→] [≡]-membership xy₁)) ([↔]-to-[←] ([↔]-to-[→] [≡]-membership xy₂))) (Tuple.map ([↔]-to-[→] ([↔]-to-[→] [≡]-membership xy₁)) ([↔]-to-[→] ([↔]-to-[→] [≡]-membership xy₂))) 〔 [↔]-transitivity 〕
              [↔]-symmetry Intersection.membership
            )

        instance
          [∩]-commutativity : Commutativity(_∩_)
          Commutativity.proof [∩]-commutativity {x} {y} =
            [↔]-to-[←] [≡]-membership (
              Intersection.membership             〔 [↔]-transitivity 〕
              [↔]-intro [∧]-symmetry [∧]-symmetry 〔 [↔]-transitivity 〕
              [↔]-symmetry Intersection.membership
            )

        instance
          [∩]-associativity : Associativity(_∩_)
          Associativity.proof [∩]-associativity {x} {y} =
            [↔]-to-[←] [≡]-membership (
              Intersection.membership 〔 [↔]-transitivity 〕
              [↔]-intro (Tuple.mapLeft ([↔]-to-[←] Intersection.membership)) (Tuple.mapLeft ([↔]-to-[→] Intersection.membership)) 〔 [↔]-transitivity 〕
              [∧]-associativity 〔 [↔]-transitivity 〕
              [↔]-symmetry([↔]-intro (Tuple.mapRight ([↔]-to-[←] Intersection.membership)) (Tuple.mapRight ([↔]-to-[→] Intersection.membership))) 〔 [↔]-transitivity 〕
              [↔]-symmetry Intersection.membership
            )

        module _ ⦃ _ : UniversalSet(_∈_) ⦄ where
          instance
            [∩]-identityₗ : Identityₗ(_∩_)(𝐔)
            Identityₗ.proof [∩]-identityₗ {x} =
              [↔]-to-[←] [≡]-membership (
                Intersection.membership 〔 [↔]-transitivity 〕
                [↔]-intro (Tuple.mapLeft {ℓ₁ = ℓ₁} (const Universal.membership)) (Tuple.mapLeft (const [⊤]-intro)) 〔 [↔]-transitivity 〕
                [↔]-intro ([∧]-intro [⊤]-intro) [∧]-elimᵣ
              )

      module _ ⦃ _ : UnionOperator(_∈_) ⦄ ⦃ _ : IntersectionOperator(_∈_) ⦄ where
        instance
          [∩][∪]-distributivityₗ : Distributivityₗ(_∩_)(_∪_)
          Distributivityₗ.proof [∩][∪]-distributivityₗ {x} {y} {z} =
            [↔]-to-[←] [≡]-membership (
              Intersection.membership 〔 [↔]-transitivity 〕
              [↔]-intro (Tuple.mapRight ([↔]-to-[←] Union.membership)) (Tuple.mapRight ([↔]-to-[→] Union.membership)) 〔 [↔]-transitivity 〕
              [∧][∨]-distributivityₗ 〔 [↔]-transitivity 〕
              [↔]-intro (Either.map2 ([↔]-to-[→] Intersection.membership) ([↔]-to-[→] Intersection.membership)) (Either.map2 ([↔]-to-[←] Intersection.membership) ([↔]-to-[←] Intersection.membership)) 〔 [↔]-transitivity 〕
              [↔]-symmetry Union.membership
            )

        instance
          [∪][∩]-distributivityₗ : Distributivityₗ(_∪_)(_∩_)
          Distributivityₗ.proof [∪][∩]-distributivityₗ {x} {y} {z} =
            [↔]-to-[←] [≡]-membership (
              Union.membership 〔 [↔]-transitivity 〕
              [↔]-intro (Either.mapRight ([↔]-to-[←] Intersection.membership)) (Either.mapRight ([↔]-to-[→] Intersection.membership)) 〔 [↔]-transitivity 〕
              [∨][∧]-distributivityₗ 〔 [↔]-transitivity 〕
              [↔]-intro (Tuple.map ([↔]-to-[→] Union.membership) ([↔]-to-[→] Union.membership)) (Tuple.map ([↔]-to-[←] Union.membership) ([↔]-to-[←] Union.membership)) 〔 [↔]-transitivity 〕
              [↔]-symmetry Intersection.membership
            )

        instance
          [∩][∪]-absorptionₗ : Absorptionₗ(_∩_)(_∪_)
          Absorptionₗ.proof [∩][∪]-absorptionₗ {x} {y} =
            [↔]-to-[←] [≡]-membership (
              Intersection.membership 〔 [↔]-transitivity 〕
              [↔]-intro (ax ↦ [∧]-intro ax ([↔]-to-[←] Union.membership ([∨]-introₗ ax))) [∧]-elimₗ
            )

        instance
          [∪][∩]-absorptionₗ : Absorptionₗ(_∪_)(_∩_)
          Absorptionₗ.proof [∪][∩]-absorptionₗ {x} {y} =
            [↔]-to-[←] [≡]-membership (
              Union.membership 〔 [↔]-transitivity 〕
              [↔]-intro [∨]-introₗ ([∨]-elim id ([∧]-elimₗ ∘ [↔]-to-[→] Intersection.membership))
            )

        instance
          [∪][∩]-lattice : Lattice(C) (_∪_)(_∩_)
          Lattice.[∨]-operator       [∪][∩]-lattice = [∪]-binaryOperator
          Lattice.[∧]-operator       [∪][∩]-lattice = [∩]-binaryOperator
          Lattice.[∨]-commutativity  [∪][∩]-lattice = [∪]-commutativity
          Lattice.[∧]-commutativity  [∪][∩]-lattice = [∩]-commutativity
          Lattice.[∨]-associativity  [∪][∩]-lattice = [∪]-associativity
          Lattice.[∧]-associativity  [∪][∩]-lattice = [∩]-associativity
          Lattice.[∨][∧]-absorptionₗ [∪][∩]-lattice = [∪][∩]-absorptionₗ
          Lattice.[∧][∨]-absorptionₗ [∪][∩]-lattice = [∩][∪]-absorptionₗ

        instance
          [∪][∩]-distributiveLattice : Lattice.Distributive([∪][∩]-lattice)
          [∪][∩]-distributiveLattice = intro

        module _ ⦃ _ : EmptySet(_∈_) ⦄ ⦃ _ : UniversalSet(_∈_) ⦄ where
          instance
            [∪][∩]-boundedLattice : Lattice.Bounded([∪][∩]-lattice)(∅)(𝐔)
            Lattice.Bounded.[∨]-identityₗ [∪][∩]-boundedLattice = [∪]-identityₗ
            Lattice.Bounded.[∧]-identityₗ [∪][∩]-boundedLattice = [∩]-identityₗ

        module _ ⦃ _ : ComplementOperator(_∈_) ⦄ where
