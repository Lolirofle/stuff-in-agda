module Type.Category.Functor where

open import Functional
import      Lvl
import      Structure.Category.Functor as Category
open import Structure.Operator
open import Structure.Setoid
open import Type
open import Type.Category

private variable ℓ ℓₒ₁ ℓₒ₂ ℓₘ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable A B C : Type{ℓ}

module _
  ⦃ equiv-func₁ : ∀{A B : Type{ℓₒ₁}} → Equiv{ℓₑ}(A → B) ⦄
  ⦃ equiv-func₂ : ∀{A B : Type{ℓₒ₂}} → Equiv{ℓₑ}(A → B) ⦄
  ⦃ [∘]-func₁ : ∀{A B C : Type{ℓₒ₁}} → BinaryOperator(_∘_ {X = A}{Y = B}{Z = C}) ⦄
  ⦃ [∘]-func₂ : ∀{A B C : Type{ℓₒ₂}} → BinaryOperator(_∘_ {X = A}{Y = B}{Z = C}) ⦄
  where

  -- Shorthand for the category-related types in the category of types.
  Functor = Category.Functor(typeFnCategory{ℓₒ₁})(typeFnCategory{ℓₒ₂})
  module Functor {F} ⦃ functor : Functor(F) ⦄ where
    open Category.Functor functor public

    module HaskellNames where
      _<$_ : ∀{x y} → y → (F(x) → F(y))
      _<$_ = map ∘ const

      _$>_ : ∀{x y} → F(x) → y → F(y)
      _$>_ = swap(_<$_)

      _<$>_ : ∀{x y} → (x → y) → (F(x) → F(y))
      _<$>_ = map

      _<&>_ : ∀{x y} → F(x) → (x → y) → F(y)
      _<&>_ = swap(_<$>_)

      -- Applies an unlifted argument to a lifted function, returning a lifted value.
      -- TODO: When `f` is an instance of `Applicative`, it should be functionally equivalent
      -- to `f <*> pure x` because:
      --   f <*$> x
      --   = fmap ($ x) f //Definition: <*$>
      --   = pure ($ x) <*> f //Applicative: "As a consequence of these laws, the Functor instance for f will satisfy..."
      --   = f <*> pure x //Applicative: interchange
      _<*$>_ : ∀{x y : Type{ℓₒ₁}} → F(x → y) → (x → F(y))
      f <*$> x = (_$ x) <$> f
