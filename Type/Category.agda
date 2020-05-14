module Type.Category where

open import Data
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Category
import      Structure.Category.Functor as Category
import      Structure.Category.Monad.ExtensionSystem as Category
open import Structure.Category.NaturalTransformation
open import Structure.Category.Properties
open import Structure.Operator.Properties
open import Structure.Operator
open import Syntax.Transitivity
open import Type
open import Type.Unit

module _ {ℓ} where
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv

  -- The set category is a category containing all sets/types of a single level in the language.
  -- The objects are all sets/types.
  -- The morphisms are all functions where the domain/codomain-pair are from these objects.
  typeIntensionalFnCategory : Category{Obj = Type{ℓ}}(_→ᶠ_)
  Category._∘_            typeIntensionalFnCategory = _∘_
  Category.id             typeIntensionalFnCategory = id
  BinaryOperator.congruence (Category.binaryOperator typeIntensionalFnCategory) [≡]-intro [≡]-intro = [≡]-intro
  Category.associativity  typeIntensionalFnCategory = Morphism.intro [≡]-intro
  Category.identity       typeIntensionalFnCategory = [∧]-intro (Morphism.intro [≡]-intro) (Morphism.intro [≡]-intro)

  typeIntensionalFnCategoryObject : CategoryObject
  typeIntensionalFnCategoryObject = intro typeIntensionalFnCategory

module _ {ℓ} where
  open import Function.Equals
  open import Function.Equals.Proofs
  import      Relator.Equals as Eq
  open import Relator.Equals.Proofs.Equiv

  -- The set category but the equality on the morphisms/functions is pointwise/extensional.
  typeExtensionalFnCategory : Category{Obj = Type{ℓ}}(_→ᶠ_) ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄
  Category._∘_ typeExtensionalFnCategory = _∘_
  Category.id  typeExtensionalFnCategory = id
  Category.binaryOperator typeExtensionalFnCategory = [⊜][∘]-binaryOperator
  Morphism.Associativity.proof (Category.associativity typeExtensionalFnCategory) {x = _} {_} {_} {x = f} {g} {h} = [⊜]-associativity {x = f}{y = g}{z = h}
  Category.identity typeExtensionalFnCategory = [∧]-intro (Morphism.intro (Dependent.intro Eq.[≡]-intro)) (Morphism.intro (Dependent.intro Eq.[≡]-intro))

  typeExtensionalFnCategoryObject : CategoryObject
  typeExtensionalFnCategoryObject = intro typeExtensionalFnCategory

  -- Shorthand for the category-related types in the category of types.
  Functor = Category.Endofunctor(typeExtensionalFnCategory)
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

  Monad = Category.ExtensionSystem{cat = typeExtensionalFnCategoryObject}

  module Monad {T} ⦃ monad : Monad(T) ⦄ where
    open Category.ExtensionSystem{cat = typeExtensionalFnCategoryObject} (monad) renaming (module HaskellNames to HaskellNames') public

    module HaskellNames where -- TODO: What to do about this. Maybe remove or move now that Syntax.Do exists?
      open HaskellNames' public

      _=<<_ : ∀{x y} → (x → T(y)) → T(x) → T(y)
      _=<<_ = bind

      _>>=_ : ∀{x y} → T(x) → (x → T(y)) → T(y)
      _>>=_ = swap(_=<<_)

      _>>_ : ∀{x y} → T(x) → T(y) → T(y)
      f >> g = f >>= const g

      _>=>_ : ∀{x y z : Type} → (x → T(y)) → (y → T(z)) → (x → T(z))
      (f >=> g)(x) = f(x) >>= g

      _<=<_ : ∀{x y z : Type} → (y → T(z)) → (x → T(y)) → (x → T(z))
      _<=<_ = swap(_>=>_)

      pure : ∀{x} → (x → T(x))
      pure = return

      _<*>_ : ∀{x y} → T(x → y) → (T(x) → T(y))
      _<*>_ tf ta = do
        f <- tf
        a <- ta
        return(f(a))

  -- Do notation for monads.
  open import Syntax.Do
  instance
    Monad-doNotation : ∀{T} ⦃ _ : Monad(T) ⦄ → DoNotation(T)
    return ⦃ Monad-doNotation ⦄ = Monad.HaskellNames.pure
    _>>=_  ⦃ Monad-doNotation ⦄ = Monad.HaskellNames._>>=_

  Empty-initialObject : Object.Initial{Obj = Type{ℓ}}(_→ᶠ_) ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ (Empty)
  IsUnit.unit Empty-initialObject = empty
  _⊜_.proof (IsUnit.uniqueness Empty-initialObject {f}) {}

  Unit-terminalObject : Object.Terminal{Obj = Type{ℓ}}(_→ᶠ_) ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ (Unit)
  IsUnit.unit Unit-terminalObject = const <>
  _⊜_.proof (IsUnit.uniqueness Unit-terminalObject {f}) {_} = Eq.[≡]-intro
