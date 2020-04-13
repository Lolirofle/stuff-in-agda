open import Type
open import Sets.Setoid

module Structure.Operator.Lattice {ℓ} (L : Type{ℓ}) ⦃ equiv-L : Equiv(L) ⦄ where

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
open import Structure.Operator.Properties
open import Structure.Operator.Proofs
open import Structure.Operator
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

  order : L → L → Stmt{ℓ}
  order x y = (x ▫ y ≡ y)

  partialOrder : Weak.PartialOrder(order)(_≡_)
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
    [∨][∧]-absorptionᵣ = [↔]-to-[→] OneTypeTwoOp.absorption-equivalence-by-commutativity [∨][∧]-absorptionₗ

  instance
    [∨]-idempotence : Idempotence(_∨_)
    Idempotence.proof [∨]-idempotence {x} =
      x ∨ x             🝖-[ [≡]-with2ᵣ(_∨_)(_) (symmetry(_≡_) (absorptionₗ(_∧_)(_∨_))) ]
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
      x ∧ x             🝖-[ [≡]-with2ᵣ(_∧_)(_) (symmetry(_≡_) (absorptionₗ(_∨_)(_∧_))) ]
      x ∧ (x ∨ (x ∧ x)) 🝖-[ absorptionₗ(_∧_)(_∨_) ]
      x                 🝖-end

  instance
    [∧]-semilattice : Semilattice(_∧_)
    [∧]-semilattice = intro

  record Bounded (𝟎 : L) (𝟏 : L) : Stmt{ℓ} where
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

    record Complemented (¬_ : L → L) : Stmt{ℓ} where
      constructor intro
      field
        ⦃ excluded-middle   ⦄ : ComplementFunction(_∨_)(¬_)
        ⦃ non-contradiction ⦄ : ComplementFunction(_∧_)(¬_)

  record Distributive : Stmt{ℓ} where
    constructor intro
    field
      ⦃ [∨][∧]-distributivityₗ ⦄ : Distributivityₗ(_∨_)(_∧_)
      ⦃ [∧][∨]-distributivityₗ ⦄ : Distributivityₗ(_∧_)(_∨_)

  -- TODO: Is a negatable lattice using one of its operators distributed by a negation a lattice? In other words, Lattice(_∧_)(¬_ ∘₂ (_∧_ on ¬_))?
  record Negatable (¬_ : L → L) : Stmt{ℓ} where
    constructor intro
    field
      ⦃ [¬]-function ⦄   : Function(¬_)
      ⦃ [¬]-involution ⦄ : Involution(¬_)
      [¬][∧][∨]-distributivity : Names.Preserving₂(¬_)(_∧_)(_∨_)

    [¬][∨][∧]-distributivity : Names.Preserving₂(¬_)(_∨_)(_∧_)
    [¬][∨][∧]-distributivity {x}{y} =
      ¬(x ∨ y)               🝖-[ [≡]-with(¬_) ([≡]-with2(_∨_) (symmetry(_≡_) (involution(¬_))) (symmetry(_≡_) (involution(¬_)))) ]
      ¬((¬(¬ x)) ∨ (¬(¬ y))) 🝖-[ [≡]-with(¬_) (symmetry(_≡_) [¬][∧][∨]-distributivity) ]
      ¬(¬((¬ x) ∧ (¬ y)))    🝖-[ involution(¬_) ]
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
