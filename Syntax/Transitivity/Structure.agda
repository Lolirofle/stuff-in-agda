module Syntax.Transitivity.Structure where

open import Functional.Instance
import      Lvl
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type

module _ {ℓ} {T : Type{ℓ}}  where
  -- TODO: Looks like the reflexive-transitive closure with some additional stuff.
  -- TODO: Would be nice if the proofs (transitivity, symmetry, reflexivity) was not required in the data structure. Maybe inferred by a macro named 🝖-begin?
  data TransitivityChain : ∀{ℓₑ} → (T → T → Type{ℓₑ}) → T → T → Typeω where
    _🝖[_][_]-[_]_ : ∀{ℓₑ} → (x : T) → (_≡_ : T → T → Type{ℓₑ}) → Transitivity(_≡_) → ∀{y} → (x ≡ y) → ∀{z} → TransitivityChain(_≡_) y z → TransitivityChain(_≡_) x z
    _🝖[_][_,_]-[_]-sym_ : ∀{ℓₑ} → (x : T) → (_≡_ : T → T → Type{ℓₑ}) → Transitivity(_≡_) → Symmetry(_≡_) → ∀{y} → (y ≡ x) → ∀{z} → TransitivityChain(_≡_) y z → TransitivityChain(_≡_) x z
    _🝖[_,_][_]-[_]-sub_ : ∀{ℓₑₗ ℓₑᵣ} → (x : T) → (_≡ₗ_ : T → T → Type{ℓₑₗ}) → (_≡ᵣ_ : T → T → Type{ℓₑᵣ}) → Subtransitivityₗ(_≡ₗ_)(_≡ᵣ_) → ∀{y} → (x ≡ᵣ y) → ∀{z} → TransitivityChain(_≡ₗ_) y z → TransitivityChain(_≡ₗ_) x z
    _🝖[_,_][_]-[_]-sup_ : ∀{ℓₑₗ ℓₑᵣ} → (x : T) → (_≡ₗ_ : T → T → Type{ℓₑₗ}) → (_≡ᵣ_ : T → T → Type{ℓₑᵣ}) → Subtransitivityᵣ(_≡ₗ_)(_≡ᵣ_) → ∀{y} → (x ≡ₗ y) → ∀{z} → TransitivityChain(_≡ᵣ_) y z → TransitivityChain(_≡ₗ_) x z
    _🝖[_][_]-end : ∀{ℓₑ} → (x : T) → (_≡_ : T → T → Type{ℓₑ}) → Reflexivity(_≡_) → TransitivityChain(_≡_) x x
  infixr 1 _🝖[_][_]-[_]_ _🝖[_][_,_]-[_]-sym_ _🝖[_,_][_]-[_]-sub_ _🝖[_,_][_]-[_]-sup_
  infixr 2 _🝖[_][_]-end

  _🝖[_]-[_]_ : ∀{ℓₑ} → (x : T) → (_≡_ : T → T → Type{ℓₑ}) ⦃ trans : Transitivity(_≡_) ⦄ → ∀{y} → (x ≡ y) → ∀{z} → TransitivityChain(_≡_) y z → TransitivityChain(_≡_) x z
  x 🝖[ _≡_ ]-[ p ] r = x 🝖[ _≡_ ][ infer ]-[ p ] r
  infixr 1 _🝖[_]-[_]_

  _🝖[_]-[_]-sym_ : ∀{ℓₑ} → (x : T) → (_≡_ : T → T → Type{ℓₑ}) ⦃ trans : Transitivity(_≡_) ⦄ ⦃ sym : Symmetry(_≡_) ⦄ → ∀{y} → (y ≡ x) → ∀{z} → TransitivityChain(_≡_) y z → TransitivityChain(_≡_) x z
  x 🝖[ _≡_ ]-[ p ]-sym r = x 🝖[ _≡_ ][ infer , infer ]-[ p ]-sym r
  infixr 1 _🝖[_]-[_]-sym_

  _🝖[_]-end : ∀{ℓₑ} → (x : T) → (_≡_ : T → T → Type{ℓₑ}) → ⦃ refl : Reflexivity(_≡_) ⦄ → TransitivityChain(_≡_) x x
  x 🝖[ _≡_ ]-end = x 🝖[ _≡_ ][ infer ]-end
  infixr 2 _🝖[_]-end

  _🝖-[_]_ : ∀{ℓₑ} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ (x : T) → ∀{y} → (x ≡ y) → ∀{z} → TransitivityChain(_≡_) y z → TransitivityChain(_≡_) x z
  x 🝖-[ p ] r = x 🝖[ _≡_ ]-[ p ] r
  infixr 1 _🝖-[_]_

  _🝖-[_]-sym_ : ∀{ℓₑ} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ (x : T) → ∀{y} → (y ≡ x) → ∀{z} → TransitivityChain(_≡_) y z → TransitivityChain(_≡_) x z
  x 🝖-[ p ]-sym r = x 🝖[ _≡_ ]-[ p ]-sym r
  infixr 1 _🝖-[_]-sym_

  _🝖-end : ∀{ℓₑ} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → (x : T) → TransitivityChain(_≡_) x x
  x 🝖-end = x 🝖[ _≡_ ]-end
  infixr 2 _🝖-end

  _🝖[_]-[]_ : ∀{ℓₑ} → (x : T) → (_≡_ : T → T → Type{ℓₑ}) → ∀{y} → TransitivityChain(_≡_) x y → TransitivityChain(_≡_) x y
  x 🝖[ _≡_ ]-[] r = r
  infixr 1 _🝖[_]-[]_

  _🝖-[]_ : ∀{ℓₑ} → (x : T) → ∀{_≡_ : T → T → Type{ℓₑ}}{y} → TransitivityChain(_≡_) x y → TransitivityChain(_≡_) x y
  x 🝖-[] r = r
  infixr 1 _🝖-[]_

  🝖-begin_ : ∀{x y}{ℓₑ}{_≡_} → TransitivityChain{ℓₑ}(_≡_) x y → (x ≡ y)
  🝖-begin_ (x 🝖[ _≡_ ][ trans ]-[ p ] r)                = Transitivity.proof trans p (🝖-begin r)
  🝖-begin_ (x 🝖[ _≡_ ][ trans , sym ]-[ p ]-sym r)      = Transitivity.proof trans (Symmetry.proof sym p) (🝖-begin r)
  🝖-begin_ (x 🝖[ _≡ₗ_ , _≡ᵣ_ ][ subtrans ]-[ p ]-sub r) = Subtransitivityₗ.proof subtrans p (🝖-begin r)
  🝖-begin_ (x 🝖[ _≡ₗ_ , _≡ᵣ_ ][ subtrans ]-[ p ]-sup r) = Subtransitivityᵣ.proof subtrans p (🝖-begin r)
  🝖-begin_ (x 🝖[ _≡_ ][ refl ]-end)                     = Reflexivity.proof refl {x}
  infixr 0 🝖-begin_
  {-# INLINE 🝖-begin_ #-}
  {-# STATIC 🝖-begin_ #-}
