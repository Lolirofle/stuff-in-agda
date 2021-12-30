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
[≡]-binaryRelator = BinaryRelator-introᵣ \{x₁} {y₁} {x₂} {y₂} xy1 xy2 x1x2 →
  y₁ 🝖-[ xy1 ]-sym
  x₁ 🝖-[ x1x2 ]
  x₂ 🝖-[ xy2 ]
  y₂ 🝖-end

reflexive-rel-sub : ∀ ⦃ equiv : Equiv{ℓₗ}(A) ⦄ {_▫_ : A → A → Type{ℓ}} ⦃ refl : Reflexivity(_▫_) ⦄ ⦃ rel : BinaryRelator ⦃ equiv ⦄ (_▫_) ⦄ → ((_≡_) ⊆₂ (_▫_))
_⊆₂_.proof (reflexive-rel-sub {_▫_ = _▫_}) xy = substitute₂-₁ₗ(_▫_)(_) xy (reflexivity(_▫_))

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {f : A → B} ⦃ func : Function(f) ⦄
  {P : B → Stmt{ℓₗ₃}} ⦃ rel : UnaryRelator(P) ⦄
  where

  [∘]-unaryRelator : UnaryRelator(P ∘ f)
  [∘]-unaryRelator = [∘]-function {f = P}

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
  unaryRelator-sub = [∘]-unaryRelator{f = P}

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {P : A → Stmt{ℓₗ₁}} ⦃ rel-P : UnaryRelator(P) ⦄
  {Q : B → Stmt{ℓₗ₂}} ⦃ rel-Q : UnaryRelator(Q) ⦄
  {_▫_ : Stmt{ℓₗ₁} → Stmt{ℓₗ₂} → Stmt{ℓₗ₃}} ⦃ rel : BinaryOperator ⦃ [↔]-equiv ⦄ ⦃ [↔]-equiv ⦄ ⦃ [↔]-equiv ⦄ (_▫_) ⦄
  where

  binaryRelator-sub : BinaryRelator(x ↦ y ↦ P(x) ▫ Q(y))
  binaryRelator-sub = [∘]-binaryRelator {f = P}{g = Q}

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
[→]-unaryRelator {P = P}{Q = Q} = UnaryRelator-introᵣ \xy pxqx → substitute₁ᵣ(Q) xy ∘ pxqx ∘ substitute₁ₗ(P) xy

[→]-dependent-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₃}(A) ⦄ {P : B → A → Stmt{ℓₗ₁}} → ((b : B) → UnaryRelator(P(b))) → UnaryRelator(\a → (b : B) → P(b)(a))
[→]-dependent-unaryRelator rel = UnaryRelator-introᵣ \xy px b → [↔]-to-[→] (UnaryRelator.substitution ⦃ rel = rel b ⦄ xy) (px b)

[∀]-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₃}(A) ⦄ {P : B → A → Stmt{ℓₗ₁}} → ⦃ rel-P : ∀{x} → UnaryRelator(P(x)) ⦄ → UnaryRelator(\y → ∀{x} → P(x)(y))
[∀]-unaryRelator {P = P} = UnaryRelator-introᵣ \{x} {a} xy px {b} → substitute₁ᵣ (P b) xy (px{b})

[∃]-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₃}(A) ⦄ {P : B → A → Stmt{ℓₗ₁}} → ⦃ rel-P : ∀{x} → UnaryRelator(P(x)) ⦄ → UnaryRelator(\y → ∃(x ↦ P(x)(y)))
[∃]-unaryRelator {P = P} = UnaryRelator-introᵣ \xy → [∃]-map-proof (substitute₁ᵣ(P _) xy)

instance
  const-unaryRelator : ∀{P : Stmt{ℓₗ₁}} → ⦃ _ : Equiv{ℓₗ}(A) ⦄ → UnaryRelator{A = A}(const P)
  const-unaryRelator = UnaryRelator-introᵣ(const id)

[¬]-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₂}(A) ⦄ {P : A → Stmt{ℓₗ₁}} → ⦃ rel-P : UnaryRelator(P) ⦄ → UnaryRelator(\x → ¬ P(x))
[¬]-unaryRelator {P = P} = [→]-unaryRelator

[∧]-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₃}(A) ⦄ {P : A → Stmt{ℓₗ₁}}{Q : A → Stmt{ℓₗ₂}} → ⦃ rel-P : UnaryRelator(P) ⦄ → ⦃ rel-Q : UnaryRelator(Q) ⦄ → UnaryRelator(x ↦ P(x) ∧ Q(x))
[∧]-unaryRelator = UnaryRelator-introᵣ \xy → Tuple.map (substitute₁ᵣ(_) xy) (substitute₁ᵣ(_) xy)

[∨]-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₃}(A) ⦄ {P : A → Stmt{ℓₗ₁}}{Q : A → Stmt{ℓₗ₂}} → ⦃ rel-P : UnaryRelator(P) ⦄ → ⦃ rel-Q : UnaryRelator(Q) ⦄ → UnaryRelator(x ↦ P(x) ∨ Q(x))
[∨]-unaryRelator = UnaryRelator-introᵣ \xy → Either.map (substitute₁ᵣ(_) xy) (substitute₁ᵣ(_) xy)

binary-unaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₂}(A) ⦄ {P : A → A → Stmt{ℓₗ₁}} → ⦃ rel-P : BinaryRelator(P) ⦄ → UnaryRelator(P $₂_)
binary-unaryRelator {P = P} = UnaryRelator-introᵣ \xy pxx → substitute₂ᵣ(P) xy xy pxx

instance
  const-binaryRelator : ∀{P : Stmt{ℓₗ}} → ⦃ equiv-A : Equiv{ℓₗ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₗ₂}(B) ⦄ → BinaryRelator{A = A}{B = B}((const ∘ const) P)
  const-binaryRelator = BinaryRelator-introᵣ((const ∘ const) id)

-- TODO: Temporary until substitution is a specialization of congruence
[¬]-binaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₂}(A) ⦄ ⦃ _ : Equiv{ℓₗ₃}(B) ⦄ {P : A → B → Stmt{ℓₗ₁}} → ⦃ rel-P : BinaryRelator(P) ⦄ → BinaryRelator(\x y → ¬ P(x)(y))
[¬]-binaryRelator {P = P} = BinaryRelator-introᵣ \xy₁ xy₂ npx → npx ∘ substitute₂ₗ(P) xy₁ xy₂

swap-binaryRelator : ∀ ⦃ _ : Equiv{ℓₗ₂}(A) ⦄ ⦃ _ : Equiv{ℓₗ₃}(B) ⦄ {P : A → B → Stmt{ℓₗ₁}} → ⦃ rel-P : BinaryRelator(P) ⦄ → BinaryRelator(swap P)
swap-binaryRelator {P = P} = BinaryRelator-introᵣ(swap(substitute₂ᵣ(P)))
