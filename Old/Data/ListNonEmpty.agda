module Data.ListNonEmpty where

open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data hiding (empty)
open import Functional
import      Data.List as List
open        List using (List)
open import Numeral.Natural
open import Type

-- A non-empty list
data List₊ {ℓ} (T : Type{ℓ}) : Type{ℓ} where
  singleton : T → List₊(T) -- The singleton list
  _⊰_       : T → List₊(T) → List₊(T) -- Cons

_⊱_ : ∀{ℓ}{T : Type{ℓ}} → List₊(T) → T → List₊(T)
_⊱_ = swap _⊰_

-- List concatenation
_++_ : ∀{ℓ}{T : Type{ℓ}} → List₊(T) → List₊(T) → List₊(T)
_++_ (singleton(elem)) b = elem ⊰ b
_++_ (elem ⊰ rest)     b = elem ⊰ (rest ++ b)

-- A list from a non-empty list
list : ∀{ℓ}{T : Type{ℓ}} → List₊(T) → List(T)
list (singleton(x)) = List.singleton(x)
list (x ⊰ l)        = x List.⊰ list(l)

-- The first element of the list
head : ∀{ℓ}{T : Type{ℓ}} → List₊(T) → T
head (singleton(x)) = x
head (x ⊰ _)        = x

-- A list without its first element
tail₀ : ∀{ℓ}{T : Type{ℓ}} → List₊(T) → List(T)
tail₀ (singleton(_)) = List.∅
tail₀ (_ ⊰ l)        = list(l)

-- Applies a binary operator to each element in the list starting with the initial element.
-- Example:
--   foldᵣ(▫)[a]         = a
--   foldᵣ(▫)[a,b]       = a▫b
--   foldᵣ(▫)[a,b,c]     = a▫(b▫c)
--   foldᵣ(▫)[a,b,c,d,e] = a▫(b▫(c▫(d▫e)))
reduceᵣ : ∀{ℓ}{T : Type{ℓ}} → (T → T → T) → List₊(T) → T
reduceᵣ _   (singleton(elem)) = elem
reduceᵣ _▫_ (elem ⊰ l) = elem ▫ (reduceᵣ _▫_ l)
