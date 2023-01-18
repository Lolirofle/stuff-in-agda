open import Structure.Setoid
open import Type

module Structure.Category.Proofs.MonadIsEndofunctorMonoid where

open import Data.Tuple as Tuple
open import Data.Tuple.Category
open import Functional as Fn using (pointwise₂,₁ ; const)
open import Function.Equals
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Structure.Function
open import Structure.Categorical.Properties
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.Functor.Category
import      Structure.Category.Functor.Functors
open        Structure.Category.Functor.Functors.Wrapped
open import Structure.Category.Monad
open import Structure.Category.Enriched.Monoid as Monoid
open import Structure.Category.Monoidal
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Type.Function
open import Syntax.Function

module _
  {ℓₒ ℓₘ ℓₑ}
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (let open CategoryObject(C))
  where

  <∘>ᶠᵘⁿᶜᵗᵒʳ : (Endofunctorᶜᵃᵗ(C) ⨯ᶜᵃᵗ Endofunctorᶜᵃᵗ(C)) →ᶠᵘⁿᶜᵗᵒʳ Endofunctorᶜᵃᵗ(C)
  ∃.witness <∘>ᶠᵘⁿᶜᵗᵒʳ (f , g) = f ∘ᶠᵘⁿᶜᵗᵒʳ g
  ∃.proof   <∘>ᶠᵘⁿᶜᵗᵒʳ = {!!}

  -- The monoidal category of endofunctors.
  instance
    [∘]-endofunctor-monoidal : Monoidalᶜᵃᵗ(Endofunctorᶜᵃᵗ(C))
    Monoidalᶜᵃᵗ.productFunctor   [∘]-endofunctor-monoidal = <∘>ᶠᵘⁿᶜᵗᵒʳ
    Monoidalᶜᵃᵗ.unitObject       [∘]-endofunctor-monoidal = idᶠᵘⁿᶜᵗᵒʳ
    MonoidalCategory.associator (Monoidalᶜᵃᵗ.monoidalCategory [∘]-endofunctor-monoidal) = [∃]-intro (\(x , (y , z)) → {!Morphism.associativity ⦃ ? ⦄ (_∘ᶠᵘⁿᶜᵗᵒʳ_) ⦃ ? ⦄ {?}{?}{?}{?} {x}{y}{z}!}) ⦃ {!!} ⦄
    MonoidalCategory.unitorₗ    (Monoidalᶜᵃᵗ.monoidalCategory [∘]-endofunctor-monoidal) = [∃]-intro {!!} ⦃ {!!} ⦄
    MonoidalCategory.unitorᵣ    (Monoidalᶜᵃᵗ.monoidalCategory [∘]-endofunctor-monoidal) = [∃]-intro {!!} ⦃ {!!} ⦄
    MonoidalCategory.associativity-condition (Monoidalᶜᵃᵗ.monoidalCategory [∘]-endofunctor-monoidal) = {!!}
    MonoidalCategory.unitality-condition     (Monoidalᶜᵃᵗ.monoidalCategory [∘]-endofunctor-monoidal) = {!!}


-- (x ∘ᶠᵘⁿᶜᵗᵒʳ y) ∘ᶠᵘⁿᶜᵗᵒʳ z ≡ x ∘ᶠᵘⁿᶜᵗᵒʳ (y ∘ᶠᵘⁿᶜᵗᵒʳ z)



  -- "A monad is just a monoid in the category of endofunctors".
  monad-is-endofunctor-monoid : ∀{F} → Monoid(Endofunctorᶜᵃᵗ(C)) F ↔ Monad(F)
  monad-is-endofunctor-monoid{F = F} = [↔]-intro l r where
    l : Monoid(Endofunctorᶜᵃᵗ(C)) F ← Monad(F)
    l m = [∃]-intro sign where
      open Monad(m)

      sign : Monoid.Signature(Endofunctorᶜᵃᵗ(C)) F
      sign = (Μ , Η)

      instance
        cond : Monoid.Conditions(Endofunctorᶜᵃᵗ(C)) sign
        Conditions.associativity-condition cond = {!μ-on-μ-preserving-functor!}
        Conditions.unitalityₗ-condition    cond = Dependent.intro \{x} → {!Dependent._⊜_.proof μ-on-μ-functor-η-inverse₀ {x}!}
        Conditions.unitalityᵣ-condition    cond = Dependent.intro \{x} → {!!} -- μ-on-μ-functor-η-inverse₁

    r : Monoid(Endofunctorᶜᵃᵗ(C)) F → Monad(F)
    Monad.Η (r m) = Monoid.η _ m
    Monad.Μ (r m) = Monoid.μ _ m
    Monad.μ-on-μ-preserving-functor (r m) = {!!}
    Monad.μ-on-μ-functor-η-inverse₁ (r m) = {!Monoid.unitalityₗ-condition _ m!}
    Monad.μ-on-μ-functor-η-inverse₀ (r m) = {!!}

{-
module _
  {ℓₒ ℓₘ ℓₑ}
  (C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}) (let open CategoryObject(C)) (let open ArrowNotation)
  ⦃ M : Monoidalᶜᵃᵗ(C) ⦄           (let open Monoidalᶜᵃᵗ(M) renaming (unitObject to 𝟏))
  where

  endomorphism-monoid : ∀{x} → Monoid(C)(x ⟶ x)
  endomorphism-monoid = ?
-}
