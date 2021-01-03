module Structure.Relator.Proofs where

import      Data.Either as Either
import      Data.Tuple as Tuple
open import Functional
open import Function.Proofs
open import Logic
open import Logic.Propositional.Proofs.Structures
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Structure.Function
open import Structure.Operator
open import Structure.Setoid
open import Structure.Relator.Properties
open import Structure.Relator
open import Syntax.Transitivity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ ℓₗ₄ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ : Lvl.Level
private variable A B A₁ A₂ B₁ B₂ : Type{ℓ}

[≡]-binaryRelator : ∀ ⦃ equiv : Equiv{ℓₗ}(A) ⦄ → BinaryRelator ⦃ equiv ⦄ (_≡_)
BinaryRelator.substitution [≡]-binaryRelator {x₁} {y₁} {x₂} {y₂} xy1 xy2 x1x2 =
  y₁ 🝖-[ xy1 ]-sym
  x₁ 🝖-[ x1x2 ]
  x₂ 🝖-[ xy2 ]
  y₂ 🝖-end

reflexive-binaryRelator-sub : ∀ ⦃ equiv : Equiv{ℓₗ}(A) ⦄ {_▫_ : A → A → Type{ℓ}} ⦃ refl : Reflexivity(_▫_) ⦄ ⦃ rel : BinaryRelator ⦃ equiv ⦄ (_▫_) ⦄ → ((_≡_) ⊆₂ (_▫_))
_⊆₂_.proof (reflexive-binaryRelator-sub {_▫_ = _▫_}) xy = substitute₂ᵣ(_▫_) xy (reflexivity(_▫_))

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {f : A → B} ⦃ func : Function(f) ⦄
  {P : B → Stmt{ℓₗ₃}} ⦃ rel : UnaryRelator(P) ⦄
  where

  [∘]-unaryRelator : UnaryRelator(P ∘ f)
  [∘]-unaryRelator = [↔]-to-[←] relator-function₁ ([∘]-function ⦃ equiv-c = [↔]-equiv ⦄ ⦃ func-f = [↔]-to-[→] relator-function₁ rel ⦄)

module _
  ⦃ equiv-A₁ : Equiv{ℓₑ₁}(A₁) ⦄
  ⦃ equiv-B₁ : Equiv{ℓₑ₂}(B₁) ⦄
  ⦃ equiv-A₂ : Equiv{ℓₑ₃}(A₂) ⦄
  ⦃ equiv-B₂ : Equiv{ℓₑ₄}(B₂) ⦄
  {f : A₁ → A₂} ⦃ func-f : Function(f) ⦄
  {g : B₁ → B₂} ⦃ func-g : Function(g) ⦄
  {_▫_ : A₂ → B₂ → Stmt{ℓₗ}} ⦃ rel : BinaryRelator(_▫_) ⦄
  where

  [∘]-binaryRelator : BinaryRelator(x ↦ y ↦ f(x) ▫ g(y))
  BinaryRelator.substitution [∘]-binaryRelator xy1 xy2 = substitute₂(_▫_) (congruence₁(f) xy1) (congruence₁(g) xy2)

module _
  ⦃ equiv-A : Equiv{ℓₑ}(A) ⦄
  {P : A → Stmt{ℓₗ₁}} ⦃ rel-P : UnaryRelator(P) ⦄
  {▫ : Stmt{ℓₗ₁} → Stmt{ℓₗ₂}} ⦃ rel : Function ⦃ [↔]-equiv ⦄ ⦃ [↔]-equiv ⦄ ▫ ⦄
  where

  unaryRelator-sub : UnaryRelator(▫ ∘ P)
  unaryRelator-sub = [∘]-unaryRelator
    ⦃ equiv-B = [↔]-equiv ⦄
    ⦃ func = [↔]-to-[→] relator-function₁ rel-P ⦄
    ⦃ rel = [↔]-to-[←] (relator-function₁ ⦃ [↔]-equiv ⦄) rel ⦄

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {P : A → Stmt{ℓₗ₁}} ⦃ rel-P : UnaryRelator(P) ⦄
  {Q : B → Stmt{ℓₗ₂}} ⦃ rel-Q : UnaryRelator(Q) ⦄
  {_▫_ : Stmt{ℓₗ₁} → Stmt{ℓₗ₂} → Stmt{ℓₗ₃}} ⦃ rel : BinaryOperator ⦃ [↔]-equiv ⦄ ⦃ [↔]-equiv ⦄ ⦃ [↔]-equiv ⦄ (_▫_) ⦄
  where

  binaryRelator-sub : BinaryRelator(x ↦ y ↦ P(x) ▫ Q(y))
  binaryRelator-sub = [∘]-binaryRelator
    ⦃ equiv-A₂ = [↔]-equiv ⦄
    ⦃ equiv-B₂ = [↔]-equiv ⦄
    ⦃ func-f = [↔]-to-[→] relator-function₁ rel-P ⦄
    ⦃ func-g = [↔]-to-[→] relator-function₁ rel-Q ⦄
    ⦃ rel = [↔]-to-[←] (relator-function₂ ⦃ [↔]-equiv ⦄ ⦃ [↔]-equiv ⦄) rel ⦄

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {P : A → Stmt{ℓₗ₁}} ⦃ rel-P : UnaryRelator(P) ⦄
  {Q : B → Stmt{ℓₗ₂}} ⦃ rel-Q : UnaryRelator(Q) ⦄
  where

  [→]-binaryRelator : BinaryRelator(x ↦ y ↦ (P(x) → Q(y)))
  [→]-binaryRelator = binaryRelator-sub{_▫_ = _→ᶠ_}

  [↔]-binaryRelator : BinaryRelator(x ↦ y ↦ (P(x) ↔ Q(y)))
  [↔]-binaryRelator = binaryRelator-sub{_▫_ = _↔_}

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
UnaryRelator.substitution [∨]-unaryRelator xy = Either.map (substitute₁(_) xy) (substitute₁(_) xy)

binary-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₂}(A) ⦄ {P : A → A → Stmt{ℓₗ₁}} → ⦃ rel-P : BinaryRelator(P) ⦄ → UnaryRelator(P $₂_)
UnaryRelator.substitution (binary-unaryRelator {P = P}) xy pxx = substitute₂(P) xy xy pxx

binary-unaryRelatorₗ : ∀ ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ {_▫_ : A → B → Stmt{ℓₗ₃}} → ⦃ rel-P : BinaryRelator(_▫_) ⦄ → ∀{x} → UnaryRelator(x ▫_)
UnaryRelator.substitution binary-unaryRelatorₗ xy x1x2 = substitute₂ _ (reflexivity(_≡_)) xy x1x2

binary-unaryRelatorᵣ : ∀ ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ {_▫_ : A → B → Stmt{ℓₗ₃}} → ⦃ rel-P : BinaryRelator(_▫_) ⦄ → ∀{x} → UnaryRelator(_▫ x)
UnaryRelator.substitution binary-unaryRelatorᵣ xy x1x2 = substitute₂ _ xy (reflexivity(_≡_)) x1x2

binaryRelator-from-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₂}(A) ⦄ {_▫_ : A → A → Stmt{ℓₗ₁}} → ⦃ relₗ : ∀{x} → UnaryRelator(_▫ x) ⦄ → ⦃ relᵣ : ∀{x} → UnaryRelator(x ▫_) ⦄ → BinaryRelator(_▫_)
BinaryRelator.substitution binaryRelator-from-unaryRelator xy1 xy2 = substitute₁ _ xy1 ∘ substitute₁ _ xy2

instance
  const-binaryRelator : ∀{P : Stmt{ℓₗ}} → ⦃ equiv-A : Equiv{ℓₗ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₗ₂}(B) ⦄ → BinaryRelator{A = A}{B = B}((const ∘ const) P)
  BinaryRelator.substitution const-binaryRelator = (const ∘ const) id

-- TODO: Temporary until substitution is a specialization of congruence
[¬]-binaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₂}(A) ⦄ ⦃ _ : Equiv{ℓₗ₃}(B) ⦄ {P : A → B → Stmt{ℓₗ₁}} → ⦃ rel-P : BinaryRelator(P) ⦄ → BinaryRelator(\x y → ¬ P(x)(y))
BinaryRelator.substitution ([¬]-binaryRelator {P = P}) xy₁ xy₂ npx py = npx(substitute₂(P) (symmetry(_≡_) xy₁) (symmetry(_≡_) xy₂) py)
