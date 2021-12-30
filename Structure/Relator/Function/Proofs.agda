module Structure.Relator.Function.Proofs where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Functional
import      Structure.Function as Func
open import Structure.Relator.Function
open import Structure.Setoid
open import Structure.Setoid.Uniqueness
open import Structure.Relator.Properties
open import Structure.Relator
open import Type

private variable ℓ₁ ℓ₂ ℓ₃ ℓₗ ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₒ₄ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ : Lvl.Level

module _ {A : Type{ℓₒ₁}}{B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ (φ : A → B → Stmt{ℓₗ}) where
  totalFunction : ⦃ tot : Total(φ) ⦄ → ⦃ func : Function(φ) ⦄ → (∀{x} → ∃!(φ(x)))
  totalFunction ⦃ tot ⦄ ⦃ func ⦄ = [∧]-intro (Total.proof tot) (Function.proof func)

  total-to-computable : ⦃ rel : ∀{x} → UnaryRelator(φ(x)) ⦄ → Total(φ) → ∃(Computable(φ))
  ∃.witness (total-to-computable tot) = Total.compute tot
  Computable.proof (∃.proof (total-to-computable tot)) {x} eq = substitute₁ᵣ(φ(x)) eq ([∃]-proof(Total.proof tot{x}))

module _ {A : Type{ℓₒ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ (φ : A → B → Stmt{ℓₗ}) where
  Total-compute-function : ⦃ rel : BinaryRelator(φ) ⦄ → ⦃ tot : Total(φ) ⦄ → ⦃ func : Function(φ) ⦄ → Func.Function(Total.compute tot)
  Func.Function.congruence Total-compute-function {x}{y} xy = function(φ) {y}  (substitute₂-₁ᵣ(φ)(_) xy ([∃]-proof(total(φ)))) ([∃]-proof(total(φ)))

module _ {A : Type{ℓₒ₁}}{B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ (φ : A → B → Stmt{ℓₗ}) ⦃ totality : Total(φ)⦄ ⦃ func : Function(φ)⦄ ⦃ _ : ∀{x} → UnaryRelator(φ(x)) ⦄ where
  -- There is a function for a total and function-like binary relation.
  relation-function-existence : ∃(f ↦ ∀{x}{y} → (f(x) ≡ y) ↔ φ(x)(y))
  relation-function-existence = [∃]-intro(f) ⦃ \{x y} → proof{x}{y} ⦄ where
    -- The function
    f : A → B
    f(x) = [∃]-witness(total(φ){x})

    -- Proof that the function returns the value that the binary relation defines the element from Y that an element from X is associated with.
    proof : ∀{x}{y} → (f(x) ≡ y) ↔ φ(x)(y)
    proof{x}{y} = [↔]-intro l r where
      r : (f(x) ≡ y) → φ(x)(y)
      r(fxy) = substitute₁ᵣ(φ(x)) fxy ([∃]-proof(total(φ){x}))

      l : (f(x) ≡ y) ← φ(x)(y)
      l(φxy) = [∃!]-existence-eq-any(totalFunction(φ)) φxy

  -- Constructing a total function from a a binary operation with conditions.
  relation-function : A → B
  relation-function = [∃]-witness(relation-function-existence)

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ {f : A → B} where
  -- Actual functions are total.
  -- ∀{x} → ∃(y ↦ f(x) ≡ y)
  Function-totality : Total(x ↦ y ↦ f(x) ≡ y)
  Total.proof(Function-totality) {x} = [∃]-intro(f(x)) ⦃ reflexivity(_≡_) ⦄

module _ {X : Type{ℓₒ₁}} {Y : X → Type{ℓₒ₂}} {φ : (x : X) → Y(x) → Stmt{ℓₗ}} where
  -- Every binary predicate that have its first argument defined for all values
  -- have at least one choice function that can determine the second argument from the first.
  -- Proposition: ∀(X: Type)∀(Y: Type)∀(φ: X → Y → Stmt). (∀(x: X)∃(y: Y). φ(x)(y)) → (∃(choice: X → Y)∀(x: X). φ(x)(choice(x)))
  --   ∀(x: X)∃(y: Y). φ(x)(y) means that the predicate φ holds for every x and some y (which may depend on x). In other words: it associates every element in X with a subset of Y, a function (X → ℘(Y)).
  --   ∃(choice: X → Y)∀(x: X). φ(x)(choice(x)) means that there is a function that picks out a particular y.
  -- Note: This proposition can be recognised as one equivalent variant of "Axiom of Choice" from set theory when formulated in classical logic.
  -- Note: This is similar to what one does in the process of "Skolemization" for an existentially quantified formula in logic.
  dependent-function-choice : (∀{x : X} → ∃{Obj = Y(x)}(y ↦ φ(x)(y))) → ∃{Obj = (x : X) → Y(x)}(choice ↦ ∀{x : X} → φ(x)(choice(x)))
  dependent-function-choice(function) = [∃]-intro(x ↦ [∃]-witness(function{x})) ⦃ \{x} → [∃]-proof(function{x}) ⦄

module _ {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} {φ : X → Y → Stmt{ℓₗ}} where
  function-choice : (∀{x} → ∃(y ↦ φ(x)(y))) → ∃{Obj = X → Y}(choice ↦ ∀{x} → φ(x)(choice(x)))
  function-choice = dependent-function-choice

{-
module _ {ℓₗ₁ ℓₗ₂ ℓₒ} {X : Type{ℓₒ}} {P : (X → Stmt{ℓₗ₁}) → Stmt{ℓₗ₂}} where
  standard-choice : (∀{Q : X → Stmt{ℓₗ₁}} → P(Q) → (∃ P)) → ∃{Obj = (X → Stmt{ℓₗ₁}) → X}(f ↦ ∀{Q : X → Stmt{ℓₗ₁}} → P(Q) → Q(f(Q)))
  standard-choice ep = [∃]-intro (choice) ⦃ \{x} → proof{x} ⦄ where
    choice : (X → Stmt{ℓₗ₁}) → X
    choice(R) = [∃]-witness(ep{R} (pr))

    proof : ∀{Q : X → Stmt{ℓₗ₁}} → P(Q) → Q(choice(Q))
    proof{Q} pq = [∃]-proof(surjective{x})
-}
