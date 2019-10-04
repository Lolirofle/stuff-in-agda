module Data.Either.Proofs where

import      Lvl
open import Data.Either
open import Functional
open import Relator.Equals
open import Type

module _ {ℓ₁}{ℓ₂} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} where
  Left-injectivity : ∀{x y : T₁} → (Left {T₁ = T₁} {T₂ = T₂} (x) ≡ Left(y)) → (x ≡ y)
  Left-injectivity [≡]-intro = [≡]-intro

  Right-injectivity : ∀{x y : T₂} → (Right {T₁ = T₁} {T₂ = T₂} (x) ≡ Right(y)) → (x ≡ y)
  Right-injectivity [≡]-intro = [≡]-intro

  mapLeft-preserves-id : ∀{e : (T₁ ‖ T₂)} → (mapLeft id(e) ≡ e)
  mapLeft-preserves-id {Left  x} = [≡]-intro
  mapLeft-preserves-id {Right x} = [≡]-intro

  mapRight-preserves-id : ∀{e : (T₁ ‖ T₂)} → (mapRight id(e) ≡ e)
  mapRight-preserves-id {Left  x} = [≡]-intro
  mapRight-preserves-id {Right x} = [≡]-intro

{- TODO
module _ {ℓ₁}{ℓ₂}{ℓ₃} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} {f : B → C}{g : A → B} where
  mapLeft-preserves-[∘] : ∀{l} → (mapLeft(f ∘ g)(l) ≡ ((map f) ∘ (map g))(l))
-}
