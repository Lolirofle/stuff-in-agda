module Structure.Container.Iterable where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Option
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
import      Structure.Container.IndexedIterable
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T : Type{ℓ}
private variable Elem : Type{ℓₑ}

open Structure.Container.IndexedIterable{Index = Unit{Lvl.𝟎}} hiding (Iterable ; module Iterable)
module Iterable{ℓ}{Iter} = Structure.Container.IndexedIterable.Iterable{Index = Unit{Lvl.𝟎}}{ℓ}{Iter = const Iter}
Iterable : ∀{ℓ} → Type{ℓ} → ∀{ℓₑ} → Type
Iterable{ℓ} Iter {ℓₑ} = Structure.Container.IndexedIterable.Iterable{Index = Unit{Lvl.𝟎}}{ℓ}(const Iter){ℓₑ}

module _ {Iter : Type{ℓ}} (iterator : Iterable(Iter){ℓₑ}) where
  open Iterable(iterator)

  next : Iter → Option(Element ⨯ Iter)
  next(i) with isEmpty(i) | indexStep i | current i | step i
  ... | 𝑇 | <> | <> | <> = None
  ... | 𝐹 | _  | x  | is = Some(x , is)

  head : Iter → Option(Element)
  head(i) with isEmpty(i) | indexStep i | current i
  ... | 𝑇 | <>  | <> = None
  ... | 𝐹 | _   | x  = Some(x)

  tail : Iter → Option(Iter)
  tail(i) with isEmpty(i) | indexStep i | step i
  ... | 𝑇 | <>  | <> = None
  ... | 𝐹 | _   | is = Some(is)

  tail₀ : Iter → Iter
  tail₀(i) with isEmpty(i) | indexStep i | step i
  ... | 𝑇 | <>  | <> = i
  ... | 𝐹 | _   | is = is

  {-
  record Finite : Type{ℓ} where
    field
      length : I → ℕ
    field
      length-proof : LengthCriteria(length)
    --field
    --  length-when-empty    : ∀{i} → IsTrue (isEmpty(i)) → (length(i) ≡ 𝟎)
      -- length-when-nonempty : ∀{i} → IsFalse(isEmpty(i)) → ∃(n ↦ length(i) ≡ 𝐒(n))
      -- length-of-step : ∀{i} → IsFalse(isEmpty(i)) → (𝐒(length(step i)) ≡ length(i)))
      -- empty-on-length-step : ∀{i} → IsTrue(isEmpty₊(length(i)) i)
      -- length-minimal-empty-step : ∀{n}{i} → (n < length(i)) → IsFalse(isEmpty₊(n) i)
  open Finite ⦃ … ⦄ public
  -}

  -- TODO: It is possible for Finite and the constructions to be from different iterables
  module _
    ⦃ fin : Finite ⦄
    {prepend : (x : Element) → (iter : Iter) → Iter}
    ⦃ prepend-construction : PrependConstruction(prepend) ⦄
    where

    _++_ : Iter → Iter → Iter
    _++_ = swap(foldᵣ prepend)

  module _
    ⦃ fin : Finite ⦄
    {empty}
    ⦃ empty-construciton : EmptyConstruction(empty) ⦄
    {prepend : (x : Element) → (iter : Iter) → Iter}
    ⦃ prepend-construction : PrependConstruction(prepend) ⦄
    where

    map : (Element → Element) → (Iter → Iter)
    map f = foldᵣ (prepend ∘ f) empty

    filter : (Element → Bool) → Iter → Iter
    filter f = foldᵣ (x ↦ if f(x) then (prepend x) else id) empty

    reverse : Iter → Iter
    reverse = foldₗ (swap prepend) empty

    postpend : Element → Iter → Iter
    postpend = foldᵣ prepend ∘ singleton

    open import Numeral.Natural
    repeat : Element → ℕ → Iter
    repeat x 𝟎      = empty
    repeat x (𝐒(n)) = prepend x (repeat x n)
