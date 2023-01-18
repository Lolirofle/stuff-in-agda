module Structure.Setoid.Signature.IndexedCategory where

open import Data.Tuple as Tuple
open import Function.Signature.IndexedCategory
open import Logic.Predicate
open import Lvl
open import Signature.IndexedCategory
open import Signature.IndexedCategory.Functor
open import Structure.Function
open import Structure.Setoid
open import Typeω.Dependent.Sigma

setoidFunction : IndexedCategory
setoidFunction = indexedCategory (Lvl.Level ⨯ Lvl.Level) (\(ℓₑ , ℓ) → Setoid{ℓₑ}{ℓ}) (_→ᶠⁿ_)

setoidHomFunctor : setoidFunction →ᶠᵘⁿᶜᵗᵒʳ explicitFunction
setoidHomFunctor = intro(functor Tuple.right [∃]-witness) [∃]-witness
