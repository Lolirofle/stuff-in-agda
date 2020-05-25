-- Idiom bracket notation.
module Syntax.Idiom where

import      Lvl
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A B : Type{ℓ}
private variable F : Type{ℓ₁} → Type{ℓ₂}

-- The notation `⦇ f x₁ x₂ x₃ ⦈` will automatically be translated to `((pure f <*> x₁) <*> x₂) <*> x₃`.
record IdiomBrackets (F : Type{ℓ₁} → Type{ℓ₂}) : Type{Lvl.𝐒(ℓ₁) Lvl.⊔ ℓ₂} where
  constructor intro
  field
    pure : (A → F(A))
    _<*>_ : F(A → B) → (F(A) → F(B))
open IdiomBrackets ⦃ … ⦄ using (pure ; _<*>_) public

-- The notation `⦇⦈` will automatically be translated to `empty`.
record IdiomBrackets₀ (F : Type{ℓ₁} → Type{ℓ₂}) : Type{Lvl.𝐒(ℓ₁) Lvl.⊔ ℓ₂} where
  constructor intro
  field
    empty : F(A)
open IdiomBrackets₀ ⦃ … ⦄ using (empty) public

-- The notation `⦇ f₁ x₁ x₂ x₃ | f₂ y₁ y₂ | f₃ z₁ ⦈` will automatically be translated to `(((pure f <*> x₁) <*> x₂) <*> x₃) <|> (((pure f₂ <*> y₁) <*> y₂) <|> (pure f₃ <*> z₁))`.
record IdiomBrackets₊ (F : Type{ℓ₁} → Type{ℓ₂}) ⦃ _ : IdiomBrackets(F) ⦄ : Type{Lvl.𝐒(ℓ₁) Lvl.⊔ ℓ₂} where
  constructor intro
  field
    _<|>_ : F(A) → F(A) → F(A)
open IdiomBrackets₊ ⦃ … ⦄ using (_<|>_) public
