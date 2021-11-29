module Functional.Instance where

import      Lvl
open import Type

infixl 10000 _⦃∘⦄_
infixl 30 _⦃→⦄_ _⦃←⦄_
infixr 0 _⦃$⦄_

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T X Y Z : Type{ℓ}

-- Instance function type.
_⦃→⦄_ : Type{ℓ₁} → Type{ℓ₂} → Type
X ⦃→⦄ Y = ⦃ X ⦄ → Y
{-# INLINE _⦃→⦄_ #-}

-- Converse of an instance function type.
_⦃←⦄_ : Type{ℓ₁} → Type{ℓ₂} → Type
Y ⦃←⦄ X = X ⦃→⦄ Y
{-# INLINE _⦃←⦄_ #-}

_⦃$⦄_ : (X ⦃→⦄ Y) → (X → Y)
f ⦃$⦄ x = f ⦃ x ⦄
{-# INLINE _⦃$⦄_ #-}

-- Function composition on instance arguments.
_⦃∘⦄_ : let _ = X in (Y ⦃→⦄ Z) → (X ⦃→⦄ Y) → (X ⦃→⦄ Z)
(f ⦃∘⦄ g) ⦃ x ⦄ = f ⦃ g ⦃ x ⦄ ⦄
{-# INLINE _⦃∘⦄_ #-}

-- Infers/resolves/(searches for) an instance/proof of an inferred type/statement.
-- Also the identity function in instance function space.
infer : ⦃ _ : T ⦄ → T
infer ⦃ x ⦄ = x
{-# INLINE infer #-}

-- Infers/resolves/(searches for) an instance/proof of the specified type/statement.
resolve : (T : Type{ℓ}) →  ⦃ _ : T ⦄ → T
resolve _ = infer
{-# INLINE resolve #-}

module _ where
  private variable A B C D : Type{ℓ}

  inferArg : (A → B) → (⦃ inst : A ⦄ → B)
  inferArg f = f infer
  {-# INLINE inferArg #-}

  inferArg₂ : (A → B → C) → (⦃ inst₁ : A ⦄ → ⦃ inst₂ : B ⦄ → C)
  inferArg₂ f = inferArg(inferArg f)
  {-# INLINE inferArg₂ #-}

  inferArg₃ : (A → B → C → D) → (⦃ inst₁ : A ⦄ → ⦃ inst₂ : B ⦄ → ⦃ inst₃ : C ⦄ → D)
  inferArg₃ f = inferArg₂(inferArg f)
  {-# INLINE inferArg₃ #-}

module _ where
  private variable A C : Type{ℓ}
  private variable B : A → Type{ℓ}

  resolveArg : ({a : A} → B(a) → C) → ((a : A) → ⦃ _ : B(a) ⦄ → C)
  resolveArg P(a) ⦃ b ⦄ = P{a}(b)
  {-# INLINE resolveArg #-}
