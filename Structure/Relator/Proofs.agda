module Structure.Relator.Proofs where

import      Data.Either as Either
import      Data.Tuple as Tuple
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Structure.Function
open import Structure.Setoid.WithLvl
open import Structure.Relator.Properties
open import Structure.Relator
open import Syntax.Transitivity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level
private variable A B : Type{ℓ}

[≡]-binaryRelator : ∀ ⦃ _ : Equiv{ℓₗ}(A) ⦄ → BinaryRelator(_≡_)
BinaryRelator.substitution [≡]-binaryRelator {x₁} {y₁} {x₂} {y₂} xy1 xy2 x1x2 =
  y₁ 🝖-[ xy1 ]-sym
  x₁ 🝖-[ x1x2 ]
  x₂ 🝖-[ xy2 ]
  y₂ 🝖-end

[→]-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₃}(A) ⦄ {P : A → Stmt{ℓₗ₁}}{Q : A → Stmt{ℓₗ₂}} → ⦃ rel-P : UnaryRelator(P) ⦄ → ⦃ rel-Q : UnaryRelator(Q) ⦄ → UnaryRelator(\x → P(x) → Q(x))
UnaryRelator.substitution ([→]-unaryRelator {P = P}{Q = Q}) xy pxqx py = substitute₁(Q) xy (pxqx(substitute₁(P) (symmetry(_≡_) xy) py))

[∀]-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₃}(A) ⦄ {P : B → A → Stmt{ℓₗ₁}} → ⦃ rel-P : ∀{x} → UnaryRelator(P(x)) ⦄ → UnaryRelator(\y → ∀{x} → P(x)(y))
UnaryRelator.substitution ([∀]-unaryRelator {P = P}) {x} {a} xy px {b} = substitute₁ (P b) xy px

[∃]-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₃}(A) ⦄ {P : B → A → Stmt{ℓₗ₁}} → ⦃ rel-P : ∀{x} → UnaryRelator(P(x)) ⦄ → UnaryRelator(\y → ∃(x ↦ P(x)(y)))
UnaryRelator.substitution ([∃]-unaryRelator {P = P}) xy = [∃]-map-proof (substitute₁(P _) xy)

instance
  const-unaryRelator : ∀{P : Stmt{ℓₗ₁}} → ⦃ _ : Equiv{ℓₗ}(A) ⦄ → UnaryRelator{A = A}(const P)
  UnaryRelator.substitution const-unaryRelator = const id

[¬]-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₂}(A) ⦄ {P : A → Stmt{ℓₗ₁}} → ⦃ rel-P : UnaryRelator(P) ⦄ → UnaryRelator(\x → ¬ P(x))
[¬]-unaryRelator {P = P} = [→]-unaryRelator

[∧]-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₃}(A) ⦄ {P : A → Stmt{ℓₗ₁}}{Q : A → Stmt{ℓₗ₂}} → ⦃ rel-P : UnaryRelator(P) ⦄ → ⦃ rel-Q : UnaryRelator(Q) ⦄ → UnaryRelator(x ↦ P(x) ∧ Q(x))
UnaryRelator.substitution [∧]-unaryRelator xy = Tuple.map (substitute₁(_) xy) (substitute₁(_) xy)

[∨]-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₃}(A) ⦄ {P : A → Stmt{ℓₗ₁}}{Q : A → Stmt{ℓₗ₂}} → ⦃ rel-P : UnaryRelator(P) ⦄ → ⦃ rel-Q : UnaryRelator(Q) ⦄ → UnaryRelator(x ↦ P(x) ∨ Q(x))
UnaryRelator.substitution [∨]-unaryRelator xy = Either.map2 (substitute₁(_) xy) (substitute₁(_) xy)

[∘]-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ {f : A → B} ⦃ func : Function(f) ⦄ {P : B → Stmt{ℓₗ₃}} → ⦃ rel : UnaryRelator(P) ⦄ → UnaryRelator(P ∘ f)
UnaryRelator.substitution ([∘]-unaryRelator {f = f}{P = P}) xy pfx = substitute₁(P) (congruence₁(f) xy) pfx

binary-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₂}(A) ⦄ {P : A → A → Stmt{ℓₗ₁}} → ⦃ rel-P : BinaryRelator(P) ⦄ → UnaryRelator(\x → P x x)
UnaryRelator.substitution (binary-unaryRelator {P = P}) xy pxx = substitute₂(P) xy xy pxx

binary-unaryRelatorₗ : ∀ ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ {_▫_ : A → B → Stmt{ℓₗ₃}} → ⦃ rel-P : BinaryRelator(_▫_) ⦄ → ∀{x} → UnaryRelator(x ▫_)
UnaryRelator.substitution binary-unaryRelatorₗ xy x1x2 = substitute₂ _ (reflexivity(_≡_)) xy x1x2

binary-unaryRelatorᵣ : ∀ ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ {_▫_ : A → B → Stmt{ℓₗ₃}} → ⦃ rel-P : BinaryRelator(_▫_) ⦄ → ∀{x} → UnaryRelator(_▫ x)
UnaryRelator.substitution binary-unaryRelatorᵣ xy x1x2 = substitute₂ _ xy (reflexivity(_≡_)) x1x2

binaryRelator-from-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₂}(A) ⦄ {_▫_ : A → A → Stmt{ℓₗ₁}} → ⦃ _ : ∀{x} → UnaryRelator(_▫ x) ⦄ → ⦃ _ : ∀{x} → UnaryRelator(x ▫_) ⦄ → BinaryRelator(_▫_)
BinaryRelator.substitution binaryRelator-from-unaryRelator xy1 xy2 = substitute₁ _ xy1 ∘ substitute₁ _ xy2
