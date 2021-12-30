open import Logic
open import Structure.Setoid
open import Structure.Operator.Ring
open import Structure.Relator.Ordering
open import Type

module Structure.OrderedField.Min
  {ℓ ℓₗ ℓₑ}
  {F : Type{ℓ}}
  ⦃ equiv : Equiv{ℓₑ}(F) ⦄
  (_≤_ : F → F → Stmt{ℓₗ})
  ⦃ ord : Weak.TotalOrder(_≤_) ⦄
  where

import      Data.Either as Either
open import Functional
open import Functional.Instance
open import Lang.Templates.Order
open import Logic.Propositional
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Structure.Relator.Properties.Proofs
open import Structure.Relator.Proofs
open import Syntax.Transitivity

open From-[≤] (_≤_)

private variable x y : F
private variable f g h f₁ f₂ g₁ g₂ h₁ h₂ : F → F

min : F → F → F
min x y = Either.elim (const x) (const y) (converseTotal(_≤_){x}{y})

-- The defining property of a min function.
min-intro : ∀{ℓ}(P : F → Type{ℓ}) → ((x ≤ y) → P(x)) → ((x ≥ y) → P(y)) → P(min x y)
min-intro{x}{y} P ple pge with converseTotal(_≤_){x}{y}
... | Either.Left  xy = ple xy
... | Either.Right yx = pge yx

min-values : (min x y ≡ x) ∨ (min x y ≡ y)
min-values{x}{y} = min-intro(m ↦ (m ≡ x) ∨ (m ≡ y))
  (const([∨]-introₗ (reflexivity(_≡_))))
  (const([∨]-introᵣ (reflexivity(_≡_))))

min-correctness : (min x y ≤ x) ∧ (min x y ≤ y)
min-correctness{x}{y} = min-intro(m ↦ (m ≤ x) ∧ (m ≤ y))
  (xy ↦ [∧]-intro (reflexivity(_≤_)) xy)
  (yx ↦ [∧]-intro yx (reflexivity(_≤_)))

min-when-left : (x ≤ y) ↔ (min x y ≡ x)
min-when-left{x}{y} = min-intro(m ↦ (x ≤ y) ↔ (m ≡ x))
  (xy ↦ [↔]-intro (const xy) (const(reflexivity(_≡_))))
  (yx ↦ [↔]-intro (sub₂(_≡_)(_≤_) ⦃ reflexive-rel-sub ⦄ ∘ symmetry(_≡_)) (antisymmetry(_≤_)(_≡_) yx))

min-when-right : (x ≥ y) ↔ (min x y ≡ y)
min-when-right{x}{y} = min-intro(m ↦ (x ≥ y) ↔ (m ≡ y))
  (xy ↦ [↔]-intro (sub₂(_≡_)(_≤_) ⦃ reflexive-rel-sub ⦄ ∘ symmetry(_≡_)) (antisymmetry(_≤_)(_≡_) xy))
  (yx ↦ [↔]-intro (const yx) (const(reflexivity(_≡_))))

min-self : (min x x ≡ x)
min-self{x} = Either.elim{P = const _} id id (min-values{x}{x})

instance
  min-function : BinaryOperator(min)
  BinaryOperator.congruence min-function {x₁}{y₁}{x₂}{y₂} p1 p2 = min-intro(_≡ min y₁ y₂)
    (x12 ↦ min-intro(x₁ ≡_)
      (y12 ↦ p1)
      (y21 ↦ p1 🝖 antisymmetry(_≤_)(_≡_) (subtransitivityₗ(_≤_)(_≡_) (symmetry(_≡_) p1) x12) (subtransitivityₗ(_≤_)(_≡_) p2 y21) 🝖 p2)
    )
    (x21 ↦ min-intro(x₂ ≡_)
      (y12 ↦ p2 🝖 antisymmetry(_≤_)(_≡_) (subtransitivityₗ(_≤_)(_≡_) (symmetry(_≡_) p2) x21) (subtransitivityₗ(_≤_)(_≡_) p1 y12) 🝖 p1)
      (y21 ↦ p2)
    )
    where
      instance _ = subrelation-transitivity-to-subtransitivityₗ ⦃ reflexive-rel-sub ⦃ equiv ⦄ {_▫_ = _≤_} ⦃ Weak.TotalOrder.reflexivity ⦃ equiv ⦄ ord ⦄ ⦃ Weak.TotalOrder.relator ⦃ equiv ⦄ ord ⦄ ⦄ ⦃ Weak.TotalOrder.transitivity ⦃ equiv ⦄ ord ⦄

instance
  min-commutativity : Commutativity(min)
  Commutativity.proof min-commutativity {x}{y} = min-intro(min x y ≡_)
    ([↔]-to-[→] min-when-right)
    ([↔]-to-[→] min-when-left)

instance
  min-associativity : Associativity(min)
  Associativity.proof min-associativity {x}{y}{z} = min-intro(m ↦ min m z ≡ min x (min y z))
    (xy ↦ min-intro(m ↦ min x z ≡ min x m)
      (yz ↦ [↔]-to-[→] min-when-left (transitivity(_≤_) xy yz) 🝖 symmetry(_≡_) ([↔]-to-[→] min-when-left xy))
      (zy ↦ reflexivity(_≡_))
    )
    (yx ↦ min-intro(m ↦ min y z ≡ min x m)
      (yz ↦ [↔]-to-[→] min-when-left  yz 🝖 symmetry(_≡_) ([↔]-to-[→] min-when-right yx))
      (zy ↦ [↔]-to-[→] min-when-right zy 🝖 symmetry(_≡_) ([↔]-to-[→] min-when-right (transitivity(_≤_) zy yx)))
    )

min-preserve-function : (∀{x y} → (x ≤ y) → (f(x) ≤ f(y))) → (f(min(x)(y)) ≡ min(f(x))(f(y)))
min-preserve-function {f}{x}{y} p = min-intro(m ↦ f(m) ≡ min(f(x))(f(y)))
  (xy ↦ symmetry(_≡_) ([↔]-to-[→] min-when-left  (p xy)))
  (yx ↦ symmetry(_≡_) ([↔]-to-[→] min-when-right (p yx)))

min-preserve-function-by-converse-preserving : ⦃ func : Function(f) ⦄ → (∀{x y} → (x ≤ y) ← (f(x) ≤ f(y))) → (f(min(x)(y)) ≡ min(f(x))(f(y)))
min-preserve-function-by-converse-preserving {f}{x}{y} p = min-intro(m ↦ f(min(x)(y)) ≡ m)
  (xy ↦ congruence₁(f) ([↔]-to-[→] min-when-left  (p xy)))
  (yx ↦ congruence₁(f) ([↔]-to-[→] min-when-right (p yx)))
