open import Type
open import Sets.Setoid

module Structure.Operator.Lattice {ℓ} (L : Type{ℓ}) ⦃ equiv-L : Equiv(L) ⦄ where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Structure.Operator.Properties
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Syntax.Transitivity

record Semilattice (_▫_ : L → L → L) : Stmt{ℓ} where
  constructor intro
  field
    ⦃ operator ⦄     : BinaryOperator(_▫_)
    ⦃ commutative ⦄  : Commutativity(_▫_)
    ⦃ associative ⦄  : Associativity(_▫_)
    ⦃ idempotent ⦄   : Idempotence(_▫_)

  partialOrder : Weak.PartialOrder(x ↦ y ↦ x ▫ y ≡ y)(_≡_)
  Antisymmetry.proof (Weak.PartialOrder.antisymmetry partialOrder) {x}{y} xy yx =
    x     🝖-[ symmetry(_≡_) yx ]
    y ▫ x 🝖-[ commutativity(_▫_) ]
    x ▫ y 🝖-[ xy ]
    y     🝖-end
  Transitivity.proof (Weak.PartialOrder.transitivity partialOrder) {x}{y}{z} xy yz =
    x ▫ z       🝖-[ [≡]-with2ᵣ(_▫_)(_) (symmetry(_≡_) yz) ]
    x ▫ (y ▫ z) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
    (x ▫ y) ▫ z 🝖-[ [≡]-with2ₗ(_▫_)(_) xy ]
    y ▫ z       🝖-[ yz ]
    z           🝖-end
  Reflexivity.proof  (Weak.PartialOrder.reflexivity  partialOrder) = idempotence(_▫_)

record Lattice (_∨_ : L → L → L) (_∧_ : L → L → L) : Stmt{ℓ} where
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
    Absorptionᵣ.proof [∨][∧]-absorptionᵣ {x}{y} =
      (x ∧ y) ∨ y 🝖-[ commutativity(_∨_) ]
      y ∨ (x ∧ y) 🝖-[ [≡]-with2ᵣ(_∨_)(_) (commutativity(_∧_)) ]
      y ∨ (y ∧ x) 🝖-[ absorptionₗ(_∨_)(_∧_) {y}{x} ]
      y           🝖-end

  instance
    [∨]-idempotence : Idempotence(_∨_)
    Idempotence.proof [∨]-idempotence {x} =
      x ∨ x             🝖-[ [≡]-with2ᵣ(_∨_)(_) (symmetry(_≡_) (absorptionₗ(_∧_)(_∨_))) ]
      x ∨ (x ∧ (x ∨ x)) 🝖-[ absorptionₗ(_∨_)(_∧_) ]
      x                 🝖-end

  instance
    [∧][∨]-absorptionᵣ : Absorptionᵣ(_∧_)(_∨_)
    Absorptionᵣ.proof [∧][∨]-absorptionᵣ {x}{y} =
      (x ∨ y) ∧ y 🝖-[ commutativity(_∧_) ]
      y ∧ (x ∨ y) 🝖-[ [≡]-with2ᵣ(_∧_)(_) (commutativity(_∨_)) ]
      y ∧ (y ∨ x) 🝖-[ absorptionₗ(_∧_)(_∨_) {y}{x} ]
      y           🝖-end

  instance
    [∧]-idempotence : Idempotence(_∧_)
    Idempotence.proof [∧]-idempotence {x} =
      x ∧ x             🝖-[ [≡]-with2ᵣ(_∧_)(_) (symmetry(_≡_) (absorptionₗ(_∨_)(_∧_))) ]
      x ∧ (x ∨ (x ∧ x)) 🝖-[ absorptionₗ(_∧_)(_∨_) ]
      x                 🝖-end

  record Bounded (𝟎 : L) (𝟏 : L) : Stmt{ℓ} where
    constructor intro
    field
      ⦃ [∨]-identityₗ ⦄ : Identityₗ(_∨_)(𝟎)
      ⦃ [∧]-identityₗ ⦄ : Identityₗ(_∧_)(𝟏)

    record Complemented (¬_ : L → L) : Stmt{ℓ} where
      constructor intro
      field
        excluded-middle   : ∀{x} → (x ∨ (¬ x) ≡ 𝟏)
        non-contradiction : ∀{x} → (x ∧ (¬ x) ≡ 𝟎)

  record Distributive : Stmt{ℓ} where
    constructor intro
    field
      ⦃ [∨][∧]-distributivityₗ ⦄ : Distributivityₗ(_∨_)(_∧_)
      ⦃ [∧][∨]-distributivityₗ ⦄ : Distributivityₗ(_∧_)(_∨_)

  record Negatable (¬_ : L → L) : Stmt{ℓ} where
    constructor intro
    field
      ⦃ [¬]-function ⦄ : Function(¬_)
      [¬]-involution : ∀{x} → (¬(¬ x) ≡ x)
      [¬][∧][∨]-distributivity : ∀{x y} → (¬(x ∧ y) ≡ (¬ x) ∨ (¬ y))

    [¬][∨][∧]-distributivity : ∀{x y} → (¬(x ∨ y) ≡ (¬ x) ∧ (¬ y))
    [¬][∨][∧]-distributivity {x}{y} =
      ¬(x ∨ y)               🝖-[ [≡]-with(¬_) ([≡]-with2(_∨_) (symmetry(_≡_) [¬]-involution) (symmetry(_≡_) [¬]-involution)) ]
      ¬((¬(¬ x)) ∨ (¬(¬ y))) 🝖-[ [≡]-with(¬_) (symmetry(_≡_) [¬][∧][∨]-distributivity) ]
      ¬(¬((¬ x) ∧ (¬ y)))    🝖-[ [¬]-involution ]
      (¬ x) ∧ (¬ y)          🝖-end

-- Also called: De Morgan algebra
record MorganicAlgebra (_∨_ : L → L → L) (_∧_ : L → L → L) (¬_ : L → L) (⊥ : L) (⊤ : L) : Stmt{ℓ} where
  constructor intro
  field
    ⦃ lattice ⦄             : Lattice(_∨_)(_∧_)
    ⦃ boundedLattice ⦄      : Lattice.Bounded(lattice)(⊥)(⊤)
    ⦃ distributiveLattice ⦄ : Lattice.Distributive(lattice)
    ⦃ negatableLattice ⦄    : Lattice.Negatable(lattice)(¬_)

record BooleanAlgebra (_∨_ : L → L → L) (_∧_ : L → L → L) (¬_ : L → L) (⊥ : L) (⊤ : L) : Stmt{ℓ} where
  constructor intro
  field
    ⦃ lattice ⦄             : Lattice(_∨_)(_∧_)
    ⦃ boundedLattice ⦄      : Lattice.Bounded(lattice)(⊥)(⊤)
    ⦃ complementedLattice ⦄ : Lattice.Bounded.Complemented(boundedLattice)(¬_)
    ⦃ distributiveLattice ⦄ : Lattice.Distributive(lattice)

-- TODO: Import some proofs from SetAlgebra
