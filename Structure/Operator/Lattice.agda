open import Type
open import Structure.Setoid

module Structure.Operator.Lattice {ℓ ℓₑ} (L : Type{ℓ}) ⦃ equiv-L : Equiv{ℓₑ}(L) ⦄ where

import      Lvl
open import Functional
import      Function.Names as Names
open import Logic
open import Logic.IntroInstances
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Function.Domain using (Involution ; involution)
open import Structure.Function.Multi
open import Structure.Function
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator.Proofs
open import Structure.Operator
open import Structure.Relator
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Syntax.Transitivity

record Semilattice (_▫_ : L → L → L) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ operator ⦄     : BinaryOperator(_▫_)
    ⦃ commutative ⦄  : Commutativity(_▫_)
    ⦃ associative ⦄  : Associativity(_▫_)
    ⦃ idempotent ⦄   : Idempotence(_▫_)

  order : L → L → Stmt
  order x y = (x ▫ y ≡ y)

  partialOrder : Weak.PartialOrder(order)
  BinaryRelator.substitution (Weak.PartialOrder.relator partialOrder) {x₁}{y₁}{x₂}{y₂} xy1 xy2 p =
    (y₁ ▫ y₂) 🝖[ _≡_ ]-[ congruence₂(_▫_) xy1 xy2 ]-sym
    (x₁ ▫ x₂) 🝖[ _≡_ ]-[ p ]
    x₂        🝖[ _≡_ ]-[ xy2 ]
    y₂        🝖-end
  Antisymmetry.proof (Weak.PartialOrder.antisymmetry partialOrder) {x}{y} xy yx =
    x     🝖-[ symmetry(_≡_) yx ]
    y ▫ x 🝖-[ commutativity(_▫_) ]
    x ▫ y 🝖-[ xy ]
    y     🝖-end
  Transitivity.proof (Weak.PartialOrder.transitivity partialOrder) {x}{y}{z} xy yz =
    x ▫ z       🝖-[ congruence₂ᵣ(_▫_)(_) (symmetry(_≡_) yz) ]
    x ▫ (y ▫ z) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
    (x ▫ y) ▫ z 🝖-[ congruence₂ₗ(_▫_)(_) xy ]
    y ▫ z       🝖-[ yz ]
    z           🝖-end
  Reflexivity.proof  (Weak.PartialOrder.reflexivity  partialOrder) = idempotence(_▫_)

record Lattice (_∨_ : L → L → L) (_∧_ : L → L → L) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ [∨]-operator ⦄ : BinaryOperator(_∨_)
    ⦃ [∧]-operator ⦄ : BinaryOperator(_∧_)

    ⦃ [∨]-commutativity ⦄ : Commutativity(_∨_)
    ⦃ [∧]-commutativity ⦄ : Commutativity(_∧_)

    ⦃ [∨]-associativity ⦄ : Associativity(_∨_)
    ⦃ [∧]-associativity ⦄ : Associativity(_∧_)

    ⦃ [∨][∧]-absorptionₗ ⦄ : Absorptionₗ(_∨_)(_∧_)
    ⦃ [∧][∨]-absorptionₗ ⦄ : Absorptionₗ(_∧_)(_∨_)

  instance
    [∨][∧]-absorptionᵣ : Absorptionᵣ(_∨_)(_∧_)
    [∨][∧]-absorptionᵣ = [↔]-to-[→] OneTypeTwoOp.absorption-equivalence-by-commutativity [∨][∧]-absorptionₗ

  instance
    [∨]-idempotence : Idempotence(_∨_)
    Idempotence.proof [∨]-idempotence {x} =
      x ∨ x             🝖-[ congruence₂ᵣ(_∨_)(_) (symmetry(_≡_) (absorptionₗ(_∧_)(_∨_))) ]
      x ∨ (x ∧ (x ∨ x)) 🝖-[ absorptionₗ(_∨_)(_∧_) ]
      x                 🝖-end

  instance
    [∨]-semilattice : Semilattice(_∨_)
    [∨]-semilattice = intro

  instance
    [∧][∨]-absorptionᵣ : Absorptionᵣ(_∧_)(_∨_)
    [∧][∨]-absorptionᵣ = [↔]-to-[→] OneTypeTwoOp.absorption-equivalence-by-commutativity [∧][∨]-absorptionₗ

  instance
    [∧]-idempotence : Idempotence(_∧_)
    Idempotence.proof [∧]-idempotence {x} =
      x ∧ x             🝖-[ congruence₂ᵣ(_∧_)(_) (symmetry(_≡_) (absorptionₗ(_∨_)(_∧_))) ]
      x ∧ (x ∨ (x ∧ x)) 🝖-[ absorptionₗ(_∧_)(_∨_) ]
      x                 🝖-end

  instance
    [∧]-semilattice : Semilattice(_∧_)
    [∧]-semilattice = intro

  record Bounded (𝟎 : L) (𝟏 : L) : Stmt{ℓ Lvl.⊔ ℓₑ} where
    constructor intro
    field
      ⦃ [∨]-identityₗ ⦄ : Identityₗ(_∨_)(𝟎)
      ⦃ [∧]-identityₗ ⦄ : Identityₗ(_∧_)(𝟏)

    instance
      [∨]-identityᵣ : Identityᵣ(_∨_)(𝟎)
      [∨]-identityᵣ = [↔]-to-[→] One.identity-equivalence-by-commutativity [∨]-identityₗ

    instance
      [∧]-identityᵣ : Identityᵣ(_∧_)(𝟏)
      [∧]-identityᵣ = [↔]-to-[→] One.identity-equivalence-by-commutativity [∧]-identityₗ

    instance
      [∨]-identity : Identity(_∨_)(𝟎)
      [∨]-identity = intro

    instance
      [∧]-identity : Identity(_∧_)(𝟏)
      [∧]-identity = intro

    instance
      [∨]-absorberₗ : Absorberₗ(_∨_)(𝟏)
      [∨]-absorberₗ = OneTypeTwoOp.absorberₗ-by-absorptionₗ-identityₗ

    instance
      [∧]-absorberₗ : Absorberₗ(_∧_)(𝟎)
      [∧]-absorberₗ = OneTypeTwoOp.absorberₗ-by-absorptionₗ-identityₗ

    instance
      [∨]-absorberᵣ : Absorberᵣ(_∨_)(𝟏)
      [∨]-absorberᵣ = [↔]-to-[→] One.absorber-equivalence-by-commutativity [∨]-absorberₗ

    instance
      [∧]-absorberᵣ : Absorberᵣ(_∧_)(𝟎)
      [∧]-absorberᵣ = [↔]-to-[→] One.absorber-equivalence-by-commutativity [∧]-absorberₗ

    instance
      [∨]-absorber : Absorber(_∨_)(𝟏)
      [∨]-absorber = intro

    instance
      [∧]-absorber : Absorber(_∧_)(𝟎)
      [∧]-absorber = intro

    instance
      [∧]-monoid : Monoid(_∧_)
      Monoid.identity-existence [∧]-monoid = [∃]-intro(𝟏)

    instance
      [∨]-monoid : Monoid(_∨_)
      Monoid.identity-existence [∨]-monoid = [∃]-intro(𝟎)

    record Complemented (¬_ : L → L) : Stmt{ℓ Lvl.⊔ ℓₑ} where
      constructor intro
      field
        ⦃ [¬]-function ⦄      : Function(¬_)
        ⦃ excluded-middle   ⦄ : ComplementFunction(_∨_)(¬_)
        ⦃ non-contradiction ⦄ : ComplementFunction(_∧_)(¬_)

  record Distributive : Stmt{ℓ Lvl.⊔ ℓₑ} where
    constructor intro
    field
      ⦃ [∨][∧]-distributivityₗ ⦄ : Distributivityₗ(_∨_)(_∧_)
      ⦃ [∧][∨]-distributivityₗ ⦄ : Distributivityₗ(_∧_)(_∨_)

    instance
      [∨][∧]-distributivityᵣ : Distributivityᵣ(_∨_)(_∧_)
      [∨][∧]-distributivityᵣ = [↔]-to-[→] OneTypeTwoOp.distributivity-equivalence-by-commutativity [∨][∧]-distributivityₗ

    instance
      [∧][∨]-distributivityᵣ : Distributivityᵣ(_∧_)(_∨_)
      [∧][∨]-distributivityᵣ = [↔]-to-[→] OneTypeTwoOp.distributivity-equivalence-by-commutativity [∧][∨]-distributivityₗ

  -- TODO: Is a negatable lattice using one of its operators distributed by a negation a lattice? In other words, Lattice(_∧_)(¬_ ∘₂ (_∧_ on ¬_))?
  record Negatable (¬_ : L → L) : Stmt{ℓ Lvl.⊔ ℓₑ} where
    constructor intro
    field
      ⦃ [¬]-function ⦄   : Function(¬_)
      ⦃ [¬]-involution ⦄ : Involution(¬_)
      ⦃ [¬][∧][∨]-distributivity ⦄ : Preserving₂(¬_)(_∧_)(_∨_)

    instance
      [¬][∨][∧]-distributivity : Preserving₂(¬_)(_∨_)(_∧_)
      Preserving.proof [¬][∨][∧]-distributivity {x}{y} =
        ¬(x ∨ y)               🝖-[ congruence₁(¬_) (congruence₂(_∨_) (symmetry(_≡_) (involution(¬_))) (symmetry(_≡_) (involution(¬_)))) ]
        ¬((¬(¬ x)) ∨ (¬(¬ y))) 🝖-[ congruence₁(¬_) (symmetry(_≡_) (preserving₂(¬_)(_∧_)(_∨_))) ]
        ¬(¬((¬ x) ∧ (¬ y)))    🝖-[ involution(¬_) ]
        (¬ x) ∧ (¬ y)          🝖-end
open Lattice using (intro) public

{- TODO: ?
semilattices-to-lattice : ∀{_∨_ _∧_} → ⦃ _ : Semilattice(_∨_) ⦄ → ⦃ _ : Semilattice(_∧_) ⦄ → Lattice(_∨_)(_∧_)
Lattice.[∨]-operator (semilattices-to-lattice ⦃ join ⦄ ⦃ meet ⦄) = Semilattice.operator join
Lattice.[∧]-operator (semilattices-to-lattice ⦃ join ⦄ ⦃ meet ⦄) = Semilattice.operator meet
Lattice.[∨]-commutativity (semilattices-to-lattice ⦃ join ⦄ ⦃ meet ⦄) = Semilattice.commutative join
Lattice.[∧]-commutativity (semilattices-to-lattice ⦃ join ⦄ ⦃ meet ⦄) = Semilattice.commutative meet
Lattice.[∨]-associativity (semilattices-to-lattice ⦃ join ⦄ ⦃ meet ⦄) = Semilattice.associative join
Lattice.[∧]-associativity (semilattices-to-lattice ⦃ join ⦄ ⦃ meet ⦄) = Semilattice.associative meet
Absorptionₗ.proof (Lattice.[∨][∧]-absorptionₗ (semilattices-to-lattice {_∨_}{_∧_} ⦃ join ⦄ ⦃ meet ⦄)) {x} {y} =
  x ∨ (x ∧ y)    🝖-[ {!!} ]
  x    🝖-end
Absorptionₗ.proof (Lattice.[∧][∨]-absorptionₗ (semilattices-to-lattice {_∨_}{_∧_} ⦃ join ⦄ ⦃ meet ⦄)) {x} {y} =
  x ∧ (x ∨ y)    🝖-[ {!!} ]
  x    🝖-end
-}

-- Also called: De Morgan algebra
record MorganicAlgebra (_∨_ : L → L → L) (_∧_ : L → L → L) (¬_ : L → L) (⊥ : L) (⊤ : L) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ lattice ⦄             : Lattice(_∨_)(_∧_)
    ⦃ boundedLattice ⦄      : Lattice.Bounded(lattice)(⊥)(⊤)
    ⦃ distributiveLattice ⦄ : Lattice.Distributive(lattice)
    ⦃ negatableLattice ⦄    : Lattice.Negatable(lattice)(¬_)

record BooleanAlgebra (_∨_ : L → L → L) (_∧_ : L → L → L) (¬_ : L → L) (⊥ : L) (⊤ : L) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ lattice ⦄             : Lattice(_∨_)(_∧_)
    ⦃ boundedLattice ⦄      : Lattice.Bounded(lattice)(⊥)(⊤)
    ⦃ complementedLattice ⦄ : Lattice.Bounded.Complemented(boundedLattice)(¬_)
    ⦃ distributiveLattice ⦄ : Lattice.Distributive(lattice)

-- TODO: Heyting algebra
-- TODO: Import some proofs from SetAlgebra
