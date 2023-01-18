open import Structure.Category
open import Type

module Structure.Category.Monad.ExtensionSystem
  {ℓₒ ℓₘ ℓₑ}
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}}
  where

import      Lvl
open import Structure.Function
open import Structure.Relator.Equivalence
open import Structure.Setoid

open CategoryObject(C)
open Category.ArrowNotation(category)
private open module MorphismEquiv {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equiv{x}{y} ⦄) using ()

record ExtensionSystem (T : Object → Object) : Type{Lvl.of(Type.of(C))} where
  field
    η   : (x : Object) → (x ⟶ T(x))
    ext : ∀{x y} → (x ⟶ T(y)) → (T(x) ⟶ T(y))

  μ : (x : Object) → (T(T(x)) ⟶ T(x))
  μ(x) = ext(id{x = T(x)})

  field
    ⦃ ext-function ⦄ : ∀{x y} → Function(ext{x}{y})
    ext-inverse      : ∀{x} → (ext(η(x)) ≡ id) -- ext ∘ᶠⁿ η ⊜ idᴺᵀ
    ext-identity     : ∀{x y}{f : x ⟶ T(y)} → (ext(f) ∘ η(x) ≡ f)
    ext-distribute   : ∀{x y z}{f : y ⟶ T(z)}{g : x ⟶ T(y)} → (ext(ext(f) ∘ g) ≡ ext(f) ∘ ext(g))

  -- Also called: Kleisli composition.
  _∘ₑₓₜ_ : ∀{x y z} → (y ⟶ T(z)) → (x ⟶ T(y)) → (x ⟶ T(z))
  f ∘ₑₓₜ g = ext(f) ∘ g

  idₑₓₜ : ∀{x} → (x ⟶ T(x))
  idₑₓₜ{x} = η(x)

  module FunctionalNames where
    -- Name sources:
    --   https://wiki.haskell.org/Lifting
    -- Also called: unit.
    lift : ∀{x} → (x ⟶ T(x))
    lift{x} = η(x)

    -- Name sources:
    --   Javascript: Array.prototype.flat
    --   Scala: scala.collection.IterableOnceOps.flatten
    flatten : ∀{x} → (T(T(x)) ⟶ T(x))
    flatten{x} = μ(x)

    -- Name sources:
    --   Javascript: Array.prototype.flatMap
    --   Java: Stream.flatMap
    --   Scala: scala.collection.IterableOnceOps.flatMap
    flatMap : ∀{x y} → (x ⟶ T(y)) → (T(x) ⟶ T(y))
    flatMap = ext

  module HaskellNames where
    return = FunctionalNames.lift
    join   = FunctionalNames.flatten
    bind   = FunctionalNames.flatMap
