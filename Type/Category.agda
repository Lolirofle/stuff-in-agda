-- A module which re-exports Type.Category.ExtensionalFunctionsCategory as the default category for types, and defines some shorthand names for categorical stuff.
module Type.Category where

open import Functional
open import Function.Equals
open import Logic.Predicate
open import Relator.Equals.Proofs.Equiv
import      Structure.Category.Functor               as Category
import      Structure.Category.Monad.ExtensionSystem as Category
import      Structure.Category.NaturalTransformation as Category
open import Syntax.Transitivity
open import Type

module _ {ℓ} where
  open import Type.Category.ExtensionalFunctionsCategory{ℓ} public

  -- Shorthand for the category-related types in the category of types.
  Functor = Category.Endofunctor(typeExtensionalFnCategory) -- TODO: Should not be an endofunctor. Let it be parameterized by different levels
  module Functor {F} ⦃ functor : Functor(F) ⦄ where
    open Category.Endofunctor(typeExtensionalFnCategory) functor public

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
      _<*$>_ : ∀{x y : Type{ℓ}} → F(x → y) → (x → F(y))
      f <*$> x = (_$ x) <$> f

  module _ {F₁} ⦃ functor₁ : Functor(F₁) ⦄ {F₂} ⦃ functor₂ : Functor(F₂) ⦄ where
    NaturalTransformation : (∀{T} → F₁(T) → F₂(T)) → Type
    NaturalTransformation η = Category.NaturalTransformation {Cₗ = typeExtensionalFnCategoryObject} {Cᵣ = typeExtensionalFnCategoryObject} ([∃]-intro F₁) ([∃]-intro F₂) (T ↦ η{T})
    module NaturalTransformation {η : ∀{T} → F₁(T) → F₂(T)} ⦃ nt : NaturalTransformation(η) ⦄ where
      open Category.NaturalTransformation {Cₗ = typeExtensionalFnCategoryObject} {Cᵣ = typeExtensionalFnCategoryObject} {[∃]-intro F₁} {[∃]-intro F₂} nt public

    {-
    -- All mappings between functors are natural.
    -- Also called: Theorems for free.
    -- TODO: Is this correct? Is this provable? Maybe one needs to prove stuff about how types are formed?
    natural-functor-mapping : ∀{η : ∀{T} → F₁(T) → F₂(T)} → NaturalTransformation(η)
    Dependent._⊜_.proof (Category.NaturalTransformation.natural (natural-functor-mapping {η}) {X}{Y} {f}) {F₁X} =
      (η ∘ (Functor.map f)) F₁X 🝖[ _≡_ ]-[]
      η(Functor.map f(F₁X))     🝖[ _≡_ ]-[ {!!} ]
      Functor.map f (η(F₁X))    🝖[ _≡_ ]-[]
      ((Functor.map f) ∘ η) F₁X 🝖-end
    -}

  Monad = Category.ExtensionSystem{cat = typeExtensionalFnCategoryObject}
  module Monad {T} ⦃ monad : Monad(T) ⦄ where
    open Category.ExtensionSystem{cat = typeExtensionalFnCategoryObject} (monad) public

    -- Do notation for monads.
    open import Syntax.Do
    instance
      doNotation : DoNotation(T)
      return ⦃ doNotation ⦄ = HaskellNames.return
      _>>=_  ⦃ doNotation ⦄ = swap(HaskellNames.bind)

  open Monad using () renaming (doNotation to Monad-doNotation) public
