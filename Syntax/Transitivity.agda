module Syntax.Transitivity where

open import Logic
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Type

-- The transitivity operator
infixl 1000 _🝖_
_🝖_ : ∀{ℓ}{T : Type{ℓ}}{_▫_ : T → T → Stmt{ℓ}} → ⦃ _ : Transitivity(_▫_) ⦄ → Names.Transitivity(_▫_)
_🝖_ {_}{T}{_▫_} = transitivity(_▫_)

-- Syntax for "equational reasoning" for any transitive relation
infixr 1 _🝖[_]-[_]_
_🝖[_]-[_]_ : ∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}} → (x : T) → ∀{y z : T} → (_▫_ : T → T → Stmt{ℓ₂}) → ⦃ _ : Transitivity(_▫_) ⦄ → (x ▫ y) → (y ▫ z) → (x ▫ z)
_🝖[_]-[_]_ (_)(_▫_) = transitivity(_▫_)

-- Syntax for "equational reasoning" for any transitive relation
infixr 1 _🝖-[_]_
_🝖-[_]_ : ∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}} → (x : T) → ∀{y z : T}{_▫_ : T → T → Stmt{ℓ₂}} → ⦃ _ : Transitivity(_▫_) ⦄ → (x ▫ y) → (y ▫ z) → (x ▫ z)
_🝖-[_]_ (_) {_▫_ = _▫_} = transitivity(_▫_)

-- Syntax for "equational reasoning" for any transitive relation
infixr 1 _🝖-[_]-sym_
_🝖-[_]-sym_ : ∀{ℓ}{T : Type{ℓ}} → (x : T) → ∀{y z : T}{_▫_ : T → T → Stmt{ℓ}} → ⦃ _ : Transitivity(_▫_) ⦄ → ⦃ _ : Symmetry(_▫_) ⦄ → (y ▫ x) → (y ▫ z) → (x ▫ z)
_🝖-[_]-sym_ (_) {_▫_ = _▫_} yx yz = transitivity(_▫_) (symmetry(_▫_) yx) (yz)

-- Syntax for "equational reasoning" for any transitive relation
infixr 1 _🝖-reduce_
_🝖-reduce_ : ∀{ℓ}{T : Type{ℓ}} → (x : T) → ∀{y : T}{_▫_ : T → T → Stmt{ℓ}} → (x ▫ y) → (x ▫ y)
_🝖-reduce_ (_) xy = xy

{-
infixr 1 _🝖-[_]-end_
_🝖-[_]-end_ : ∀{ℓ}{T : Type{ℓ}} → (x : T) → ∀{y z : T}{_▫_ : T → T → Stmt{ℓ}} → (x ▫ y) → y
_🝖-[_]-end_ (_) = 
-}

-- Syntax for "equational reasoning" for any transitive relation
infixr 2 _🝖-end
_🝖-end : ∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}} → (x : T) → ∀{_▫_ : T → T → Stmt{ℓ₂}} → ⦃ _ : Reflexivity(_▫_) ⦄ → (x ▫ x)
_🝖-end x {_▫_} = reflexivity(_▫_)