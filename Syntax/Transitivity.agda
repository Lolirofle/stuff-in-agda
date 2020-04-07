module Syntax.Transitivity where

import      Lvl
open import Logic
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Type

private variable ℓ₁ ℓ₂ ℓ₃ : Lvl.Level
private variable T : Type{ℓ₁}

-- The transitivity operator
infixl 1000 _🝖_
_🝖_ : ∀{_▫_ : T → T → Stmt{ℓ₂}} → ⦃ _ : Transitivity(_▫_) ⦄ → Names.Transitivity(_▫_)
_🝖_ {_▫_ = _▫_} = transitivity(_▫_)

_🝖-subₗ_ : ∀{_▫₁_ : T → T → Stmt{ℓ₂}}{_▫₂_ : T → T → Stmt{ℓ₃}} → ⦃ _ : Subtransitivityₗ(_▫₁_)(_▫₂_) ⦄ → Names.Subtransitivityₗ(_▫₁_)(_▫₂_)
_🝖-subₗ_ {_▫₁_ = _▫₁_} {_▫₂_ = _▫₂_} = subtransitivityₗ(_▫₁_)(_▫₂_)

_🝖-subᵣ_ : ∀{_▫₁_ : T → T → Stmt{ℓ₂}}{_▫₂_ : T → T → Stmt{ℓ₃}} → ⦃ _ : Subtransitivityᵣ(_▫₁_)(_▫₂_) ⦄ → Names.Subtransitivityᵣ(_▫₁_)(_▫₂_)
_🝖-subᵣ_ {_▫₁_ = _▫₁_} {_▫₂_ = _▫₂_} = subtransitivityᵣ(_▫₁_)(_▫₂_)


-- Syntax for "equational reasoning" for reflexive-transitive relation

infixr 1 _🝖[_]-[_]_
_🝖[_]-[_]_ : (x : T) → ∀{y z : T} → (_▫_ : T → T → Stmt{ℓ₂}) → ⦃ _ : Transitivity(_▫_) ⦄ → (x ▫ y) → (y ▫ z) → (x ▫ z)
_🝖[_]-[_]_ (_)(_▫_) = transitivity(_▫_)

infixr 1 _🝖[_]-[_]-sym_
_🝖[_]-[_]-sym_ : (x : T) → ∀{y z : T} → (_▫_ : T → T → Stmt{ℓ₂}) → ⦃ _ : Transitivity(_▫_) ⦄ → ⦃ _ : Symmetry(_▫_) ⦄ → (y ▫ x) → (y ▫ z) → (x ▫ z)
_🝖[_]-[_]-sym_ (_)(_▫_) yx yz = transitivity(_▫_) (symmetry(_▫_) yx) (yz)

infixr 1 _🝖[_]-[_]-sub_
_🝖[_]-[_]-sub_ : (x : T) → ∀{y z : T}{_▫₁_ : T → T → Stmt{ℓ₂}} (_▫₂_ : T → T → Stmt{ℓ₃}) → ⦃ _ : Subtransitivityₗ(_▫₁_)(_▫₂_) ⦄ → (x ▫₂ y) → (y ▫₁ z) → (x ▫₁ z)
_🝖[_]-[_]-sub_ (_) {_▫₁_ = _▫₁_} (_▫₂_) = subtransitivityₗ(_▫₁_)(_▫₂_)

infixr 1 _🝖[_]-[_]-super_
_🝖[_]-[_]-super_ : (x : T) → ∀{y z : T} (_▫₁_ : T → T → Stmt{ℓ₂}) {_▫₂_ : T → T → Stmt{ℓ₃}} → ⦃ _ : Subtransitivityᵣ(_▫₁_)(_▫₂_) ⦄ → (x ▫₁ y) → (y ▫₂ z) → (x ▫₁ z)
_🝖[_]-[_]-super_ (_) (_▫₁_) {_▫₂_ = _▫₂_} = subtransitivityᵣ(_▫₁_)(_▫₂_)

infixr 1 _🝖[_]-[]_
_🝖[_]-[]_ : (x : T) → ∀{y : T} → (_▫_ : T → T → Stmt{ℓ₂}) → (x ▫ y) → (x ▫ y)
_🝖[_]-[]_ (_)(_▫_) xy = xy

infixr 2 _🝖-semiend_🝖[_]-end-from-[_]
_🝖-semiend_🝖[_]-end-from-[_] : (x y : T) → (_▫_ : T → T → Stmt{ℓ₂}) → ⦃ _ : Transitivity(_▫_) ⦄ → (x ▫ y) → (x ▫ y)
_🝖-semiend_🝖[_]-end-from-[_] _ _ (_▫_) xy = xy

infixr 2 _🝖[_]-end
_🝖[_]-end : (x : T) → (_▫_ : T → T → Stmt{ℓ₂}) → ⦃ _ : Reflexivity(_▫_) ⦄ → (x ▫ x)
_🝖[_]-end (_)(_▫_) = reflexivity(_▫_)



-- Syntax for "equational reasoning" for reflexive-transitive relations.
-- Example:
--   import      Lvl
--   open import Logic
--   open import Structure.Relator.Properties
--   open import Type
--   postulate ℓ₁ ℓ₂ : Lvl.Level
--   postulate T : Type{ℓ₁}
--   postulate _▫_ : T → T → Stmt{ℓ₂}
--   instance postulate trans : Transitivity(_▫_)
--   instance postulate sym   : Symmetry    (_▫_)
--   instance postulate refl  : Reflexivity (_▫_)
--   postulate a b c e : T
--   d = c
--   postulate ab : (a ▫ b)
--   postulate cb : (c ▫ b)
--   postulate de : (d ▫ e)
--
--   ac : (a ▫ e)
--   ac =
--     a 🝖-[ ab ]
--     b 🝖-[ cb ]-sym
--     c 🝖-[]
--     d 🝖-[ de ]
--     e 🝖-end

infixr 1 _🝖-[_]_
_🝖-[_]_ : (x : T) → ∀{y z : T}{_▫_ : T → T → Stmt{ℓ₂}} → ⦃ _ : Transitivity(_▫_) ⦄ → (x ▫ y) → (y ▫ z) → (x ▫ z)
_🝖-[_]_ (_) {_▫_ = _▫_} = transitivity(_▫_)

infixr 1 _🝖-[_]-sym_
_🝖-[_]-sym_ : (x : T) → ∀{y z : T}{_▫_ : T → T → Stmt{ℓ₂}} → ⦃ _ : Transitivity(_▫_) ⦄ → ⦃ _ : Symmetry(_▫_) ⦄ → (y ▫ x) → (y ▫ z) → (x ▫ z)
_🝖-[_]-sym_ (_) {_▫_ = _▫_} yx yz = transitivity(_▫_) (symmetry(_▫_) yx) (yz)

infixr 1 _🝖-[_]-sub_
_🝖-[_]-sub_ : (x : T) → ∀{y z : T}{_▫₁_ : T → T → Stmt{ℓ₂}}{_▫₂_ : T → T → Stmt{ℓ₃}} → ⦃ _ : Subtransitivityₗ(_▫₁_)(_▫₂_) ⦄ → (x ▫₂ y) → (y ▫₁ z) → (x ▫₁ z)
_🝖-[_]-sub_ (_) {_▫₁_ = _▫₁_} {_▫₂_ = _▫₂_} = subtransitivityₗ(_▫₁_)(_▫₂_)

infixr 1 _🝖-[_]-super_
_🝖-[_]-super_ : (x : T) → ∀{y z : T}{_▫₁_ : T → T → Stmt{ℓ₂}}{_▫₂_ : T → T → Stmt{ℓ₃}} → ⦃ _ : Subtransitivityᵣ(_▫₁_)(_▫₂_) ⦄ → (x ▫₁ y) → (y ▫₂ z) → (x ▫₁ z)
_🝖-[_]-super_ (_) {_▫₁_ = _▫₁_} {_▫₂_ = _▫₂_} = subtransitivityᵣ(_▫₁_)(_▫₂_)


infixr 1 _🝖-[]_
_🝖-[]_ : (x : T) → ∀{y : T}{_▫_ : T → T → Stmt{ℓ₂}} → (x ▫ y) → (x ▫ y)
_🝖-[]_ (_) xy = xy

infixr 2 _🝖-semiend_🝖-end-from-[_]
_🝖-semiend_🝖-end-from-[_] : (x y : T) → ∀{_▫_ : T → T → Stmt{ℓ₂}} → ⦃ _ : Transitivity(_▫_) ⦄ → (x ▫ y) → (x ▫ y)
_🝖-semiend_🝖-end-from-[_] _ _ {_▫_ = _▫_} xy = xy

infixr 2 _🝖-end
_🝖-end : (x : T) → ∀{_▫_ : T → T → Stmt{ℓ₂}} → ⦃ _ : Reflexivity(_▫_) ⦄ → (x ▫ x)
_🝖-end x {_▫_} = reflexivity(_▫_)

-- syntax _🝖-[]_ a {b} ab = a 🝖-[ ab ]-end b
