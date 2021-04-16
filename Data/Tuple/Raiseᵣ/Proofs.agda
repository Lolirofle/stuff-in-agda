module Data.Tuple.Raiseᵣ.Proofs where

import      Lvl
-- open import Data hiding (empty)
-- open import Data.Option as Option using (Option)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Equiv as Tuple
open import Data.Tuple.Raiseᵣ
open import Data.Tuple.Raiseᵣ.Functions
open import Functional
-- open import Functional using (id ; const ; apply)
-- open import Functional.Dependent using (_∘_)
open import Numeral.Natural
-- open import Numeral.Natural.Oper using (_+_ ; _⋅_)
-- open import Numeral.Natural.Oper.Proofs.Rewrite
-- open import Numeral.Natural.Relation.Order
-- open import Numeral.Finite
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid
-- open import Syntax.Function
-- open import Syntax.Number
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T A B C A₁ A₂ : Type{ℓ}
private variable n n₁ n₂ : ℕ

module _ ⦃ equiv : ∀{n} → Equiv{ℓₑ}(T ^ n)⦄ ⦃ ext : ∀{n} → Tuple.Extensionality(equiv{𝐒(𝐒 n)}) ⦄ where
  map-id : ∀{xs : T ^ n} → (map{n} id xs ≡ xs)
  map-id {n = 𝟎}       {xs = <>}     = reflexivity(_≡_) ⦃ Equiv.reflexivity(equiv{𝟎}) ⦄
  map-id {n = 𝐒 𝟎}     {xs = x}      = reflexivity(_≡_) ⦃ Equiv.reflexivity(equiv{1}) ⦄
  map-id {n = 𝐒 (𝐒 n)} {xs = x , xs} = congruence₂(_,_) ⦃ Tuple.Extensionality.[,]-function ext ⦄ (reflexivity(_≡_) ⦃ Equiv.reflexivity(equiv{1}) ⦄) (map-id {n = 𝐒 n})

module _ ⦃ equiv : ∀{n} → Equiv{ℓₑ}(C ^ n) ⦄ ⦃ ext : ∀{n} → Tuple.Extensionality(equiv{𝐒(𝐒 n)}) ⦄ where
  map-[∘] : ∀{f : B → C}{g : A → B}{xs : A ^ n} → (map{n} (f ∘ g) xs ≡ map{n} f (map{n} g xs))
  map-[∘] {n = 𝟎}       {xs = <>}     = reflexivity(_≡_) ⦃ Equiv.reflexivity(equiv{𝟎}) ⦄
  map-[∘] {n = 𝐒 𝟎}     {xs = x}      = reflexivity(_≡_) ⦃ Equiv.reflexivity(equiv{1}) ⦄
  map-[∘] {n = 𝐒 (𝐒 n)} {xs = x , xs} = congruence₂(_,_) ⦃ Tuple.Extensionality.[,]-function ext ⦄ (reflexivity(_≡_) ⦃ Equiv.reflexivity(equiv{1}) ⦄) (map-[∘] {n = 𝐒 n})
