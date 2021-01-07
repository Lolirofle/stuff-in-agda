module Data.ListNonEmpty where

open import Data.Boolean
import      Data.IndexedList
open import Functional
import      Lvl
open import Numeral.Natural
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

module _ (T : Type{ℓ}) where
  open Data.IndexedList(T){Bool} using (IndexedList ; intro)

  -- A non-empty list.
  List₊ : Type{ℓ}
  List₊ = IndexedList(intro 𝐹 (const(const 𝑇)))(𝑇)

module _ {T : Type{ℓ}} where
  open Data.IndexedList(T){Bool} using (∅ ; _⊰_ ; singleton) public

pattern ‥ = _ ⊰ _

open import Data.List
import      Data.List.Functions as List

-- A list from a non-empty list.
list : List₊(T) → List(T)
list (singleton(x)) = List.singleton(x)
list (x ⊰ l@‥)      = x List.⊰ list(l)

-- A list without its first element.
tail₀ : List₊(T) → List(T)
tail₀ (singleton(_)) = List.∅
tail₀ (_ ⊰ l@‥)      = list(l)

-- List concatenation.
_++_ : List₊(T) → List₊(T) → List₊(T)
singleton(x) ++ y = x ⊰ y
(x ⊰ xl@‥)   ++ y = x ⊰ (xl ++ y)

-- The first element of the list.
head : List₊(T) → T
head(singleton x)   = x
head(x ⊰ l@‥) = x

-- Applies a binary operator to each element in the list starting with the initial element.
-- Example:
--   reduceᵣ(_▫_) [a]         = a
--   reduceᵣ(_▫_) [a,b]       = a ▫ b
--   reduceᵣ(_▫_) [a,b,c]     = a ▫ (b ▫ c)
--   reduceᵣ(_▫_) [a,b,c,d,e] = a ▫ (b ▫ (c ▫ (d ▫ e)))
reduceᵣ : (T → T → T) → List₊(T) → T
reduceᵣ(_)   (singleton(x)) = x
reduceᵣ(_▫_) (x ⊰ l@‥)      = x ▫ (reduceᵣ(_▫_) l)
