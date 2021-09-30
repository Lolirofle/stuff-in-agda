module Structure.Container.SetLike.Proofs where

{-
open import Data.Boolean
open import Data.Boolean.Stmt
open import Functional
open import Lang.Instance
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Container.SetLike
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Relator hiding (module Names)
open import Structure.Setoid renaming (_≡_ to _≡ₛ_ ; _≢_ to _≢ₛ_)
open import Type.Properties.Inhabited
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ₉ ℓ₁₀ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level
private variable A B C C₁ C₂ Cₒ Cᵢ E E₁ E₂ : Type{ℓ}
private variable _∈_ _∈ₒ_ _∈ᵢ_ : E → C

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
        big-intersection-filter-unaryRelator : ⦃ _ : Equiv{ℓₗ}(E) ⦄ ⦃ _ : BinaryRelator{B = C}(_∈_) ⦄ → ∀{As} → UnaryRelator(\a → ∀{A} → (A ∈ As) → (a ∈ A))
        big-intersection-filter-unaryRelator ⦃ [∈]-binaryRelator ⦄ = [∀]-unaryRelator ⦃ rel-P = \{A} → [→]-unaryRelator ⦃ rel-P = const-unaryRelator ⦄ ⦃ rel-Q = BinaryRelator.left (binaryRelator(_∈_)) {A} ⦄ ⦄

    filter-big-union-to-big-intersection : ⦃ _ : BinaryRelator(_∈_) ⦄ ⦃ _ : FilterFunction(_∈_){ℓ = ℓ₁ Lvl.⊔ ℓ₂} ⦄ ⦃ _ : BigUnionOperator(_∈_)(_∈_) ⦄ → BigIntersectionOperator(_∈_)(_∈_)
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
        filter-unaryRelator : UnaryRelator(x ↦ (x ∉ x))
        filter-unaryRelator = [¬]-unaryRelator ⦃ rel-P = binary-unaryRelator ⦄

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
      IntersectionOperator._∩_ filter-to-intersection a b = filter (_∈ b) ⦃ unaryRelator = BinaryRelator.left infer ⦄ a
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
            Complement.membership                            ⦗ [↔]-transitivity ⦘ᵣ
            [¬]-unaryOperator ([↔]-to-[→] [≡]-membership xy) ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-symmetry Complement.membership
          )

      instance
        [∁]-involution : ⦃ _ : ∀{x y} → Classical(x ∈ y) ⦄ → Involution(∁)
        Involution.proof [∁]-involution =
          [↔]-to-[←] [≡]-membership (
            Complement.membership                   ⦗ [↔]-transitivity ⦘ᵣ
            [¬]-unaryOperator Complement.membership ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-intro [¬¬]-intro [¬¬]-elim
          )

    module _ ⦃ _ : UnionOperator(_∈_) ⦄ where
      instance
        [∪]-binaryOperator : BinaryOperator(_∪_)
        BinaryOperator.congruence [∪]-binaryOperator xy₁ xy₂ =
          [↔]-to-[←] [≡]-membership (
            Union.membership ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-intro (Either.map ([↔]-to-[←] ([↔]-to-[→] [≡]-membership xy₁)) ([↔]-to-[←] ([↔]-to-[→] [≡]-membership xy₂))) (Either.map ([↔]-to-[→] ([↔]-to-[→] [≡]-membership xy₁)) ([↔]-to-[→] ([↔]-to-[→] [≡]-membership xy₂))) ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-symmetry Union.membership
          )

      instance
        [∪]-commutativity : Commutativity(_∪_)
        Commutativity.proof [∪]-commutativity {x} {y} =
          [↔]-to-[←] [≡]-membership (
            Union.membership                    ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-intro [∨]-symmetry [∨]-symmetry ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-symmetry Union.membership
          )

      instance
        [∪]-associativity : Associativity(_∪_)
        Associativity.proof [∪]-associativity {x} {y} =
          [↔]-to-[←] [≡]-membership (
            Union.membership ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-intro (Either.mapLeft ([↔]-to-[←] Union.membership)) (Either.mapLeft ([↔]-to-[→] Union.membership)) ⦗ [↔]-transitivity ⦘ᵣ
            [∨]-associativity ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-symmetry([↔]-intro (Either.mapRight ([↔]-to-[←] Union.membership)) (Either.mapRight ([↔]-to-[→] Union.membership))) ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-symmetry Union.membership
          )

      module _ ⦃ _ : EmptySet(_∈_) ⦄ where
        instance
          [∪]-identityₗ : Identityₗ(_∪_)(∅)
          Identityₗ.proof [∪]-identityₗ {x} =
            [↔]-to-[←] [≡]-membership (
              Union.membership ⦗ [↔]-transitivity ⦘ᵣ
              [↔]-intro (Either.mapLeft [⊥]-elim) (Either.mapLeft Empty.membership) ⦗ [↔]-transitivity ⦘ᵣ
              [↔]-intro [∨]-introᵣ [∨]-identityₗ
            )

    module _ ⦃ _ : IntersectionOperator(_∈_) ⦄ where
      instance
        [∩]-binaryOperator : BinaryOperator(_∩_)
        BinaryOperator.congruence [∩]-binaryOperator xy₁ xy₂ =
          [↔]-to-[←] [≡]-membership (
            Intersection.membership ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-intro (Tuple.map ([↔]-to-[←] ([↔]-to-[→] [≡]-membership xy₁)) ([↔]-to-[←] ([↔]-to-[→] [≡]-membership xy₂))) (Tuple.map ([↔]-to-[→] ([↔]-to-[→] [≡]-membership xy₁)) ([↔]-to-[→] ([↔]-to-[→] [≡]-membership xy₂))) ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-symmetry Intersection.membership
          )

      instance
        [∩]-commutativity : Commutativity(_∩_)
        Commutativity.proof [∩]-commutativity {x} {y} =
          [↔]-to-[←] [≡]-membership (
            Intersection.membership             ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-intro [∧]-symmetry [∧]-symmetry ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-symmetry Intersection.membership
          )

      instance
        [∩]-associativity : Associativity(_∩_)
        Associativity.proof [∩]-associativity {x} {y} =
          [↔]-to-[←] [≡]-membership (
            Intersection.membership ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-intro (Tuple.mapLeft ([↔]-to-[←] Intersection.membership)) (Tuple.mapLeft ([↔]-to-[→] Intersection.membership)) ⦗ [↔]-transitivity ⦘ᵣ
            [∧]-associativity ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-symmetry([↔]-intro (Tuple.mapRight ([↔]-to-[←] Intersection.membership)) (Tuple.mapRight ([↔]-to-[→] Intersection.membership))) ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-symmetry Intersection.membership
          )

      module _ ⦃ _ : UniversalSet(_∈_) ⦄ where
        instance
          [∩]-identityₗ : Identityₗ(_∩_)(𝐔)
          Identityₗ.proof [∩]-identityₗ {x} =
            [↔]-to-[←] [≡]-membership (
              Intersection.membership ⦗ [↔]-transitivity ⦘ᵣ
              [↔]-intro (Tuple.mapLeft {ℓ₁} (const Universal.membership)) (Tuple.mapLeft (const [⊤]-intro)) ⦗ [↔]-transitivity ⦘ᵣ
              [↔]-intro ([∧]-intro [⊤]-intro) [∧]-elimᵣ
            )

    module _ ⦃ _ : UnionOperator(_∈_) ⦄ ⦃ _ : IntersectionOperator(_∈_) ⦄ where
      instance
        [∩][∪]-distributivityₗ : Distributivityₗ(_∩_)(_∪_)
        Distributivityₗ.proof [∩][∪]-distributivityₗ {x} {y} {z} =
          [↔]-to-[←] [≡]-membership (
            Intersection.membership ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-intro (Tuple.mapRight ([↔]-to-[←] Union.membership)) (Tuple.mapRight ([↔]-to-[→] Union.membership)) ⦗ [↔]-transitivity ⦘ᵣ
            [∧][∨]-distributivityₗ ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-intro (Either.map ([↔]-to-[→] Intersection.membership) ([↔]-to-[→] Intersection.membership)) (Either.map ([↔]-to-[←] Intersection.membership) ([↔]-to-[←] Intersection.membership)) ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-symmetry Union.membership
          )

      instance
        [∪][∩]-distributivityₗ : Distributivityₗ(_∪_)(_∩_)
        Distributivityₗ.proof [∪][∩]-distributivityₗ {x} {y} {z} =
          [↔]-to-[←] [≡]-membership (
            Union.membership ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-intro (Either.mapRight ([↔]-to-[←] Intersection.membership)) (Either.mapRight ([↔]-to-[→] Intersection.membership)) ⦗ [↔]-transitivity ⦘ᵣ
            [∨][∧]-distributivityₗ ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-intro (Tuple.map ([↔]-to-[→] Union.membership) ([↔]-to-[→] Union.membership)) (Tuple.map ([↔]-to-[←] Union.membership) ([↔]-to-[←] Union.membership)) ⦗ [↔]-transitivity ⦘ᵣ
            [↔]-symmetry Intersection.membership
          )

      instance
        [∩][∪]-absorptionₗ : Absorptionₗ(_∩_)(_∪_)
        Absorptionₗ.proof [∩][∪]-absorptionₗ {x} {y} =
          [↔]-to-[←] [≡]-membership (
            Intersection.membership ⦗ [↔]-transitivity ⦘
            [↔]-intro (ax ↦ [∧]-intro ax ([↔]-to-[←] Union.membership ([∨]-introₗ ax))) [∧]-elimₗ
          )

      instance
        [∪][∩]-absorptionₗ : Absorptionₗ(_∪_)(_∩_)
        Absorptionₗ.proof [∪][∩]-absorptionₗ {x} {y} =
          [↔]-to-[←] [≡]-membership (
            Union.membership ⦗ [↔]-transitivity ⦘
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
-}
